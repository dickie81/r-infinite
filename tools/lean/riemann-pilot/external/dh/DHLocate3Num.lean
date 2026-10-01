import DHLocate3Trig2

/-! # Generated (`gen_locate_zero.py 3`): the interval evaluation of `PReG cZ 41 12`, `PImG cZ 41 12`, `AReG cZ 41 12`

The three open inequalities of `DHLocate3Base` (`H1`, `H2`, `H3`) from the atom bounds of `DHLocate3Exp` /
`DHLocate3Trig`, `DHLocate3Trig2`, `κ` (`PsiOmega.kappa_bounds`) and `log n` (`PsiOmega.Num.log_bound_n`), by interval products
(`mul_bounds_of`) and block sums; then `dh_zero_located` = `dh_zero_near_of_center' H1 H2 H3`. -/

open Real Finset

namespace PsiOmega.Locate.Z3

theorem lgB_2 : (346573590228867 / 500000000000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (138629436131547 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_2
  constructor <;> linarith [h.1, h.2]

theorem eC_2 : (-89224213502511 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 2 * cCG cZ 2 ∧ ex (57436 / 100000) 2 * cCG cZ 2 ≤ (-89224208930963 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_2 cCB_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_2 : (-126733646296031 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 2 * cCG cZ 2) ∧ kappa * (ex (57436 / 100000) 2 * cCG cZ 2) ≤ (-1013869118421 / 8000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_2 : (250998609572367 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 2 * sCG cZ 2 ∧ ex (57436 / 100000) 2 * sCG cZ 2 ≤ (20079889681501 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_2 sCB_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_2 : (142606890025181 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 2 * sCG cZ 2) ∧ kappa * (ex (57436 / 100000) 2 * sCG cZ 2) ≤ (28521379305709 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_2 : (-309227560178347 / 1000000000000000 : ℝ) ≤ Real.log 2 * (ex (57436 / 100000) 2 * cCG cZ 2) ∧ Real.log 2 * (ex (57436 / 100000) 2 * cCG cZ 2) ≤ (-309227544245343 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_2 eC_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_2 : (-87845069624569 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 2 * (ex (57436 / 100000) 2 * cCG cZ 2)) ∧ kappa * (Real.log 2 * (ex (57436 / 100000) 2 * cCG cZ 2)) ≤ (-17569013019667 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_3 : (1098612288561369 / 1000000000000000 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (1098612288829637 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_3
  constructor <;> linarith [h.1, h.2]

theorem eC_3 : (51553372971659 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 3 * cCG cZ 3 ∧ ex (57436 / 100000) 3 * cCG cZ 3 ≤ (412427007972639 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_3 cCB_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_3 : (14645232900537 / 125000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 3 * cCG cZ 3) ∧ kappa * (ex (57436 / 100000) 3 * cCG cZ 3) ≤ (11716187007883 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_3 : (336142592455881 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 3 * sCG cZ 3 ∧ ex (57436 / 100000) 3 * sCG cZ 3 ≤ (42017827079061 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_3 sCB_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_3 : (95491066258903 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 3 * sCG cZ 3) ∧ kappa * (ex (57436 / 100000) 3 * sCG cZ 3) ≤ (23872768281743 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_3 : (14159292265863 / 31250000000000 : ℝ) ≤ Real.log 3 * (ex (57436 / 100000) 3 * cCG cZ 3) ∧ Real.log 3 * (ex (57436 / 100000) 3 * cCG cZ 3) ≤ (22654868960199 / 50000000000000 : ℝ) := by
  exact mul_bounds_of lgB_3 eC_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_3 : (25743092533397 / 200000000000000 : ℝ) ≤ kappa * (Real.log 3 * (ex (57436 / 100000) 3 * cCG cZ 3)) ∧ kappa * (Real.log 3 * (ex (57436 / 100000) 3 * cCG cZ 3)) ≤ (8044716890679 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_4 : (693147180505767 / 500000000000000 : ℝ) ≤ Real.log 4 ∧ Real.log 4 ≤ (693147180650437 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_4
  constructor <;> linarith [h.1, h.2]

theorem eC_4 : (-52977231271573 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 4 * cCG cZ 4 ∧ ex (57436 / 100000) 4 * cCG cZ 4 ≤ (-26488604621747 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_4 cCB_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_4 : (-447903080682471 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 4 * sCG cZ 4 ∧ ex (57436 / 100000) 4 * sCG cZ 4 ≤ (-447903058588761 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_4 sCB_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_4 : (-36721018494557 / 500000000000000 : ℝ) ≤ Real.log 4 * (ex (57436 / 100000) 4 * cCG cZ 4) ∧ Real.log 4 * (ex (57436 / 100000) 4 * cCG cZ 4) ≤ (-73442006436383 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_4 eC_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_6 : (1791759469113201 / 1000000000000000 : ℝ) ≤ Real.log 6 ∧ Real.log 6 ≤ (1791759469474139 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_6
  constructor <;> linarith [h.1, h.2]

theorem eC_6 : (-352735034700273 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 6 * cCG cZ 6 ∧ ex (57436 / 100000) 6 * cCG cZ 6 ≤ (-2755742289981 / 7812500000000 : ℝ) := by
  exact mul_bounds_of exB_6 cCB_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_6 : (57076902865141 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 6 * sCG cZ 6 ∧ ex (57436 / 100000) 6 * sCG cZ 6 ≤ (7134615548319 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_6 sCB_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_6 : (-39501021164969 / 62500000000000 : ℝ) ≤ Real.log 6 * (ex (57436 / 100000) 6 * cCG cZ 6) ∧ Real.log 6 * (ex (57436 / 100000) 6 * cCG cZ 6) ≤ (-632016299841171 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_6 eC_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_7 : (972955074470179 / 500000000000000 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ (972955074651209 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_7
  constructor <;> linarith [h.1, h.2]

theorem eC_7 : (-7623641229897 / 25000000000000 : ℝ) ≤ ex (57436 / 100000) 7 * cCG cZ 7 ∧ ex (57436 / 100000) 7 * cCG cZ 7 ≤ (-304945629404583 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_7 cCB_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_7 : (-4331433422343 / 50000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 7 * cCG cZ 7) ∧ kappa * (ex (57436 / 100000) 7 * cCG cZ 7) ≤ (-43314331412283 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_7 : (-7386528245381 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 7 * sCG cZ 7 ∧ ex (57436 / 100000) 7 * sCG cZ 7 ≤ (-118184432173641 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_7 sCB_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_7 : (-33573726099969 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 7 * sCG cZ 7) ∧ kappa * (ex (57436 / 100000) 7 * sCG cZ 7) ≤ (-33573720488709 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_7 : (-296698416877939 / 500000000000000 : ℝ) ≤ Real.log 7 * (ex (57436 / 100000) 7 * cCG cZ 7) ∧ Real.log 7 * (ex (57436 / 100000) 7 * cCG cZ 7) ≤ (-593396795133383 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_7 eC_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_7 : (-168571605151299 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 7 * (ex (57436 / 100000) 7 * cCG cZ 7)) ∧ kappa * (Real.log 7 * (ex (57436 / 100000) 7 * cCG cZ 7)) ≤ (-1316965579527 / 7812500000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_8 : (2079441541559079 / 1000000000000000 : ℝ) ≤ Real.log 8 ∧ Real.log 8 ≤ (519860385493349 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_8
  constructor <;> linarith [h.1, h.2]

theorem eC_8 : (49696068370513 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 8 * cCG cZ 8 ∧ ex (57436 / 100000) 8 * cCG cZ 8 ≤ (49696072597291 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_8 cCB_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_8 : (14117611585323 / 200000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 8 * cCG cZ 8) ∧ kappa * (ex (57436 / 100000) 8 * cCG cZ 8) ≤ (70588063930311 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_8 : (86612282134359 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 8 * sCG cZ 8 ∧ ex (57436 / 100000) 8 * sCG cZ 8 ≤ (173224585383137 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_8 sCB_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_8 : (49209468587129 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 8 * sCG cZ 8) ∧ kappa * (ex (57436 / 100000) 8 * sCG cZ 8) ≤ (24604737292647 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_8 : (16146885784657 / 31250000000000 : ℝ) ≤ Real.log 8 * (ex (57436 / 100000) 8 * cCG cZ 8) ∧ Real.log 8 * (ex (57436 / 100000) 8 * cCG cZ 8) ≤ (64587548644833 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_8 eC_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_8 : (73391869995291 / 500000000000000 : ℝ) ≤ kappa * (Real.log 8 * (ex (57436 / 100000) 8 * cCG cZ 8)) ∧ kappa * (Real.log 8 * (ex (57436 / 100000) 8 * cCG cZ 8)) ≤ (146783752504163 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_9 : (2197224577213583 / 1000000000000000 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ (274653072205603 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_9
  constructor <;> linarith [h.1, h.2]

theorem eC_9 : (1784505131759 / 31250000000000 : ℝ) ≤ ex (57436 / 100000) 9 * cCG cZ 9 ∧ ex (57436 / 100000) 9 * cCG cZ 9 ≤ (57104184692393 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_9 cCB_9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_9 : (277268559274889 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 9 * sCG cZ 9 ∧ ex (57436 / 100000) 9 * sCG cZ 9 ≤ (138634289902763 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_9 sCB_9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_9 : (31367668269317 / 250000000000000 : ℝ) ≤ Real.log 9 * (ex (57436 / 100000) 9 * cCG cZ 9) ∧ Real.log 9 * (ex (57436 / 100000) 9 * cCG cZ 9) ≤ (7841919880781 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_9 eC_9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_11 : (2397895272674763 / 1000000000000000 : ℝ) ≤ Real.log 11 ∧ Real.log 11 ≤ (2397895273114743 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_11
  constructor <;> linarith [h.1, h.2]

theorem eC_11 : (-61579145069957 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 11 * cCG cZ 11 ∧ ex (57436 / 100000) 11 * cCG cZ 11 ≤ (-7697392552411 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_11 cCB_11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_11 : (-27241178327509 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 11 * sCG cZ 11 ∧ ex (57436 / 100000) 11 * sCG cZ 11 ≤ (-54482338100821 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_11 sCB_11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_11 : (-147660340885697 / 250000000000000 : ℝ) ≤ Real.log 11 * (ex (57436 / 100000) 11 * cCG cZ 11) ∧ Real.log 11 * (ex (57436 / 100000) 11 * cCG cZ 11) ≤ (-73830164853393 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_11 eC_11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_12 : (248490664966427 / 100000000000000 : ℝ) ≤ Real.log 12 ∧ Real.log 12 ≤ (1242453325052681 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_12
  constructor <;> linarith [h.1, h.2]

theorem eC_12 : (128710060952819 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 12 * cCG cZ 12 ∧ ex (57436 / 100000) 12 * cCG cZ 12 ≤ (64355039346309 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_12 cCB_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_12 : (36563831048117 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 12 * cCG cZ 12) ∧ kappa * (ex (57436 / 100000) 12 * cCG cZ 12) ≤ (4570479510953 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_12 : (-6329225823647 / 31250000000000 : ℝ) ≤ ex (57436 / 100000) 12 * sCG cZ 12 ∧ ex (57436 / 100000) 12 * sCG cZ 12 ≤ (-202535208597681 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_12 sCB_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_12 : (-11507202689483 / 200000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 12 * sCG cZ 12) ∧ kappa * (ex (57436 / 100000) 12 * sCG cZ 12) ≤ (-57536008402447 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_12 : (319832486340353 / 1000000000000000 : ℝ) ≤ Real.log 12 * (ex (57436 / 100000) 12 * cCG cZ 12) ∧ Real.log 12 * (ex (57436 / 100000) 12 * cCG cZ 12) ≤ (319832530478871 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_12 eC_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_12 : (90857706908669 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 12 * (ex (57436 / 100000) 12 * cCG cZ 12)) ∧ kappa * (Real.log 12 * (ex (57436 / 100000) 12 * cCG cZ 12)) ≤ (45428859723749 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_13 : (641237339334437 / 250000000000000 : ℝ) ≤ Real.log 13 ∧ Real.log 13 ≤ (512989871555873 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_13
  constructor <;> linarith [h.1, h.2]

theorem eC_13 : (2223121915577 / 10000000000000 : ℝ) ≤ ex (57436 / 100000) 13 * cCG cZ 13 ∧ ex (57436 / 100000) 13 * cCG cZ 13 ≤ (111156104250367 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_13 cCB_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_13 : (63154234811777 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 13 * cCG cZ 13) ∧ kappa * (ex (57436 / 100000) 13 * cCG cZ 13) ≤ (3157711981247 / 50000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_13 : (-27862618367113 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 13 * sCG cZ 13 ∧ ex (57436 / 100000) 13 * sCG cZ 13 ≤ (-55725219833447 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_13 sCB_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_13 : (-395759299231 / 25000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 13 * sCG cZ 13) ∧ kappa * (ex (57436 / 100000) 13 * sCG cZ 13) ≤ (-7915183584041 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_13 : (142554878216067 / 250000000000000 : ℝ) ≤ Real.log 13 * (ex (57436 / 100000) 13 * cCG cZ 13) ∧ Real.log 13 * (ex (57436 / 100000) 13 * cCG cZ 13) ≤ (57021955642047 / 100000000000000 : ℝ) := by
  exact mul_bounds_of lgB_13 eC_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_13 : (80993706996813 / 500000000000000 : ℝ) ≤ kappa * (Real.log 13 * (ex (57436 / 100000) 13 * cCG cZ 13)) ∧ kappa * (Real.log 13 * (ex (57436 / 100000) 13 * cCG cZ 13)) ≤ (20248428295879 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_14 : (32988216618643 / 12500000000000 : ℝ) ≤ Real.log 14 ∧ Real.log 14 ≤ (65976433248333 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_14
  constructor <;> linarith [h.1, h.2]

theorem eC_14 : (195370925551311 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 14 * cCG cZ 14 ∧ ex (57436 / 100000) 14 * cCG cZ 14 ≤ (97685470964551 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_14 cCB_14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_14 : (-12544663194027 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 14 * sCG cZ 14 ∧ ex (57436 / 100000) 14 * sCG cZ 14 ≤ (-100357289198597 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_14 sCB_14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_14 : (515595073045713 / 1000000000000000 : ℝ) ≤ Real.log 14 * (ex (57436 / 100000) 14 * cCG cZ 14) ∧ Real.log 14 * (ex (57436 / 100000) 14 * cCG cZ 14) ≤ (257797558176987 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_14 eC_14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_16 : (1386294361052777 / 500000000000000 : ℝ) ≤ Real.log 16 ∧ Real.log 16 ≤ (1386294361310171 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_16
  constructor <;> linarith [h.1, h.2]

theorem eC_16 : (-98905291551797 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 16 * cCG cZ 16 ∧ ex (57436 / 100000) 16 * cCG cZ 16 ≤ (-197810565584739 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_16 cCB_16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_16 : (47457308629351 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 16 * sCG cZ 16 ∧ ex (57436 / 100000) 16 * sCG cZ 16 ≤ (47457326103749 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_16 sCB_16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_16 : (-548447391927979 / 1000000000000000 : ℝ) ≤ Real.log 16 * (ex (57436 / 100000) 16 * cCG cZ 16) ∧ Real.log 16 * (ex (57436 / 100000) 16 * cCG cZ 16) ≤ (-8569489738337 / 15625000000000 : ℝ) := by
  exact mul_bounds_of lgB_16 eC_16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_17 : (2833213343915281 / 1000000000000000 : ℝ) ≤ Real.log 17 ∧ Real.log 17 ≤ (2833213344477039 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_17
  constructor <;> linarith [h.1, h.2]

theorem eC_17 : (22296482924249 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 17 * cCG cZ 17 ∧ ex (57436 / 100000) 17 * cCG cZ 17 ≤ (11148242616519 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_17 cCB_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_17 : (50671708400997 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 17 * cCG cZ 17) ∧ kappa * (ex (57436 / 100000) 17 * cCG cZ 17) ≤ (50671713648027 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_17 : (82346418094379 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 17 * sCG cZ 17 ∧ ex (57436 / 100000) 17 * sCG cZ 17 ≤ (82346436533691 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_17 sCB_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_17 : (23392891715933 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 17 * sCG cZ 17) ∧ kappa * (ex (57436 / 100000) 17 * sCG cZ 17) ≤ (23392896954157 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_17 : (505365543546891 / 1000000000000000 : ℝ) ≤ Real.log 17 * (ex (57436 / 100000) 17 * cCG cZ 17) ∧ Real.log 17 * (ex (57436 / 100000) 17 * cCG cZ 17) ≤ (505365595977429 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_17 eC_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_17 : (14356376040069 / 100000000000000 : ℝ) ≤ kappa * (Real.log 17 * (ex (57436 / 100000) 17 * cCG cZ 17)) ∧ kappa * (Real.log 17 * (ex (57436 / 100000) 17 * cCG cZ 17)) ≤ (143563775295109 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_18 : (1445185878875393 / 500000000000000 : ℝ) ≤ Real.log 18 ∧ Real.log 18 ≤ (578074351668731 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_18
  constructor <;> linarith [h.1, h.2]

theorem eC_18 : (-4116585928041 / 25000000000000 : ℝ) ≤ ex (57436 / 100000) 18 * cCG cZ 18 ∧ ex (57436 / 100000) 18 * cCG cZ 18 ≤ (-6586536731267 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_18 cCB_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_18 : (-730897371453 / 15625000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 18 * cCG cZ 18) ∧ kappa * (ex (57436 / 100000) 18 * cCG cZ 18) ≤ (-5847178302619 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_18 : (-47514610340789 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 18 * sCG cZ 18 ∧ ex (57436 / 100000) 18 * sCG cZ 18 ≤ (-47514600932743 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_18 sCB_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_18 : (-26995810148123 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 18 * sCG cZ 18) ∧ kappa * (ex (57436 / 100000) 18 * sCG cZ 18) ≤ (-1687237800179 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_18 : (-95187709657637 / 200000000000000 : ℝ) ≤ Real.log 18 * (ex (57436 / 100000) 18 * cCG cZ 18) ∧ Real.log 18 * (ex (57436 / 100000) 18 * cCG cZ 18) ≤ (-475938493736057 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_18 eC_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_18 : (-67602083862251 / 500000000000000 : ℝ) ≤ kappa * (Real.log 18 * (ex (57436 / 100000) 18 * cCG cZ 18)) ∧ kappa * (Real.log 18 * (ex (57436 / 100000) 18 * cCG cZ 18)) ≤ (-16900519028423 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_19 : (58888779580361 / 20000000000000 : ℝ) ≤ Real.log 19 ∧ Real.log 19 ≤ (1472219489816001 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_19
  constructor <;> linarith [h.1, h.2]

theorem eC_19 : (183388598108207 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 19 * cCG cZ 19 ∧ ex (57436 / 100000) 19 * cCG cZ 19 ≤ (183388617057411 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_19 cCB_19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_19 : (45868893189 / 2500000000000 : ℝ) ≤ ex (57436 / 100000) 19 * sCG cZ 19 ∧ ex (57436 / 100000) 19 * sCG cZ 19 ≤ (3669515233321 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_19 sCB_19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_19 : (421856669201 / 781250000000 : ℝ) ≤ Real.log 19 * (ex (57436 / 100000) 19 * cCG cZ 19) ∧ Real.log 19 * (ex (57436 / 100000) 19 * cCG cZ 19) ≤ (67497074060581 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_19 eC_19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_21 : (1522261218785741 / 500000000000000 : ℝ) ≤ Real.log 21 ∧ Real.log 21 ≤ (3044522438210293 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_21
  constructor <;> linarith [h.1, h.2]

theorem eC_21 : (-10755124389123 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 21 * cCG cZ 21 ∧ ex (57436 / 100000) 21 * cCG cZ 21 ≤ (-86040976520571 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_21 cCB_21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_21 : (-3781192155893 / 25000000000000 : ℝ) ≤ ex (57436 / 100000) 21 * sCG cZ 21 ∧ ex (57436 / 100000) 21 * sCG cZ 21 ≤ (-75623833809627 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_21 sCB_21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_21 : (-130976870113711 / 500000000000000 : ℝ) ≤ Real.log 21 * (ex (57436 / 100000) 21 * cCG cZ 21) ∧ Real.log 21 * (ex (57436 / 100000) 21 * cCG cZ 21) ≤ (-261953683567439 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_21 eC_21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_22 : (3091042453205323 / 1000000000000000 : ℝ) ≤ Real.log 22 ∧ Real.log 22 ≤ (386380306731437 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_22
  constructor <;> linarith [h.1, h.2]

theorem eC_22 : (13723698823687 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 22 * cCG cZ 22 ∧ ex (57436 / 100000) 22 * cCG cZ 22 ≤ (137237006646757 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_22 cCB_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_22 : (38986152397867 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 22 * cCG cZ 22) ∧ kappa * (ex (57436 / 100000) 22 * cCG cZ 22) ≤ (9746539406933 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_22 : (-49672260853827 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 22 * sCG cZ 22 ∧ ex (57436 / 100000) 22 * sCG cZ 22 ≤ (-49672251656531 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_22 sCB_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_22 : (-14110848368747 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 22 * sCG cZ 22) ∧ kappa * (ex (57436 / 100000) 22 * sCG cZ 22) ≤ (-1128867660479 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_22 : (106051339197551 / 250000000000000 : ℝ) ≤ Real.log 22 * (ex (57436 / 100000) 22 * cCG cZ 22) ∧ Real.log 22 * (ex (57436 / 100000) 22 * cCG cZ 22) ≤ (212102706892313 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_22 eC_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_22 : (120507852148941 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 22 * (ex (57436 / 100000) 22 * cCG cZ 22)) ∧ kappa * (Real.log 22 * (ex (57436 / 100000) 22 * cCG cZ 22)) ≤ (15063483542483 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_23 : (97984194242981 / 31250000000000 : ℝ) ≤ Real.log 23 ∧ Real.log 23 ≤ (78387355410673 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_23
  constructor <;> linarith [h.1, h.2]

theorem eC_23 : (72837806304141 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 23 * cCG cZ 23 ∧ ex (57436 / 100000) 23 * cCG cZ 23 ≤ (29135126141243 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_23 cCB_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_23 : (41383388740627 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 23 * cCG cZ 23) ∧ kappa * (ex (57436 / 100000) 23 * cCG cZ 23) ≤ (41383393881871 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_23 : (77801425142061 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 23 * sCG cZ 23 ∧ ex (57436 / 100000) 23 * sCG cZ 23 ≤ (77801443214531 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_23 sCB_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_23 : (11050877231889 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 23 * sCG cZ 23) ∧ kappa * (ex (57436 / 100000) 23 * sCG cZ 23) ≤ (22101759597789 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_23 : (114191260178201 / 250000000000000 : ℝ) ≤ Real.log 23 * (ex (57436 / 100000) 23 * cCG cZ 23) ∧ Real.log 23 * (ex (57436 / 100000) 23 * cCG cZ 23) ≤ (456765097553681 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_23 eC_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_23 : (6487868801271 / 50000000000000 : ℝ) ≤ kappa * (Real.log 23 * (ex (57436 / 100000) 23 * cCG cZ 23)) ∧ kappa * (Real.log 23 * (ex (57436 / 100000) 23 * cCG cZ 23)) ≤ (129757392172723 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_24 : (397256728774203 / 125000000000000 : ℝ) ≤ Real.log 24 ∧ Real.log 24 ≤ (3178053830849101 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_24
  constructor <;> linarith [h.1, h.2]

theorem eC_24 : (4425183518159 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 24 * cCG cZ 24 ∧ ex (57436 / 100000) 24 * cCG cZ 24 ≤ (22125926420293 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_24 cCB_24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_24 : (154967315426341 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 24 * sCG cZ 24 ∧ ex (57436 / 100000) 24 * sCG cZ 24 ≤ (7748366656351 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_24 sCB_24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_24 : (140634714291949 / 1000000000000000 : ℝ) ≤ Real.log 24 * (ex (57436 / 100000) 24 * cCG cZ 24) ∧ Real.log 24 * (ex (57436 / 100000) 24 * cCG cZ 24) ≤ (35158692610549 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_24 eC_24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_26 : (162904826893321 / 50000000000000 : ℝ) ≤ Real.log 26 ∧ Real.log 26 ≤ (1629048269263539 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_26
  constructor <;> linarith [h.1, h.2]

theorem eC_26 : (-71204253455013 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 26 * cCG cZ 26 ∧ ex (57436 / 100000) 26 * cCG cZ 26 ≤ (-71204236454621 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_26 cCB_26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_26 : (13646029699259 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 26 * sCG cZ 26 ∧ ex (57436 / 100000) 26 * sCG cZ 26 ≤ (4164438294 / 30517578125 : ℝ) := by
  exact mul_bounds_of exB_26 sCB_26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_26 : (-231990331710183 / 1000000000000000 : ℝ) ≤ Real.log 26 * (ex (57436 / 100000) 26 * cCG cZ 26) ∧ Real.log 26 * (ex (57436 / 100000) 26 * cCG cZ 26) ≤ (-115995138137111 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_26 eC_26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_27 : (51497451028891 / 15625000000000 : ℝ) ≤ Real.log 27 ∧ Real.log 27 ≤ (411979608313923 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_27
  constructor <;> linarith [h.1, h.2]

theorem eC_27 : (-13930097135727 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 27 * cCG cZ 27 ∧ ex (57436 / 100000) 27 * cCG cZ 27 ≤ (-69650468990349 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_27 cCB_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_27 : (-1236640210913 / 62500000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 27 * cCG cZ 27) ∧ kappa * (ex (57436 / 100000) 27 * cCG cZ 27) ≤ (-9893119316907 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_27 : (667740900307 / 5000000000000 : ℝ) ≤ ex (57436 / 100000) 27 * sCG cZ 27 ∧ ex (57436 / 100000) 27 * sCG cZ 27 ≤ (66774098387021 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_27 sCB_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_27 : (37938239298469 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 27 * sCG cZ 27) ∧ kappa * (ex (57436 / 100000) 27 * sCG cZ 27) ≤ (18969122023091 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_27 : (-229556638470069 / 1000000000000000 : ℝ) ≤ Real.log 27 * (ex (57436 / 100000) 27 * cCG cZ 27) ∧ Real.log 27 * (ex (57436 / 100000) 27 * cCG cZ 27) ≤ (-114778291711033 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_27 eC_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_27 : (-65212230363797 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 27 * (ex (57436 / 100000) 27 * cCG cZ 27)) ∧ kappa * (Real.log 27 * (ex (57436 / 100000) 27 * cCG cZ 27)) ≤ (-16303053681453 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_28 : (3332204510019711 / 1000000000000000 : ℝ) ≤ Real.log 28 ∧ Real.log 28 ≤ (1666102255341693 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_28
  constructor <;> linarith [h.1, h.2]

theorem eC_28 : (-18390006072793 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 28 * cCG cZ 28 ∧ ex (57436 / 100000) 28 * cCG cZ 28 ≤ (-2298749732523 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_28 cCB_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_28 : (-10448430682757 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 28 * cCG cZ 28) ∧ kappa * (ex (57436 / 100000) 28 * cCG cZ 28) ≤ (-1306053252087 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_28 : (142847162415027 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 28 * sCG cZ 28 ∧ ex (57436 / 100000) 28 * sCG cZ 28 ≤ (142847178880677 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_28 sCB_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_28 : (317030354017 / 7812500000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 28 * sCG cZ 28) ∧ kappa * (ex (57436 / 100000) 28 * sCG cZ 28) ≤ (10144972497931 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_28 : (-7659907648407 / 62500000000000 : ℝ) ≤ Real.log 28 * (ex (57436 / 100000) 28 * cCG cZ 28) ∧ Real.log 28 * (ex (57436 / 100000) 28 * cCG cZ 28) ≤ (-24511693523583 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_28 eC_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_28 : (-17408153925323 / 500000000000000 : ℝ) ≤ kappa * (Real.log 28 * (ex (57436 / 100000) 28 * cCG cZ 28)) ∧ kappa * (Real.log 28 * (ex (57436 / 100000) 28 * cCG cZ 28)) ≤ (-34816292295443 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_29 : (673459165966167 / 200000000000000 : ℝ) ≤ Real.log 29 ∧ Real.log 29 ≤ (3367295830495533 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_29
  constructor <;> linarith [h.1, h.2]

theorem eC_29 : (13594372016213 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 29 * cCG cZ 29 ∧ ex (57436 / 100000) 29 * cCG cZ 29 ≤ (6797190034119 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_29 cCB_29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_29 : (70991591144333 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 29 * sCG cZ 29 ∧ ex (57436 / 100000) 29 * sCG cZ 29 ≤ (2218487475571 / 15625000000000 : ℝ) := by
  exact mul_bounds_of exB_29 sCB_29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_29 : (45776272199363 / 500000000000000 : ℝ) ≤ Real.log 29 * (ex (57436 / 100000) 29 * cCG cZ 29) ∧ Real.log 29 * (ex (57436 / 100000) 29 * cCG cZ 29) ≤ (91552598643899 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_29 eC_29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_31 : (3433987204329301 / 1000000000000000 : ℝ) ≤ Real.log 31 ∧ Real.log 31 ≤ (42924840062443 / 12500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_31
  constructor <;> linarith [h.1, h.2]

theorem eC_31 : (3466556034119 / 25000000000000 : ℝ) ≤ ex (57436 / 100000) 31 * cCG cZ 31 ∧ ex (57436 / 100000) 31 * cCG cZ 31 ≤ (34665564234181 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_31 cCB_31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_31 : (-5700904293099 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 31 * sCG cZ 31 ∧ ex (57436 / 100000) 31 * sCG cZ 31 ≤ (-456071722517 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_31 sCB_31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_31 : (238082181285103 / 500000000000000 : ℝ) ≤ Real.log 31 * (ex (57436 / 100000) 31 * cCG cZ 31) ∧ Real.log 31 * (ex (57436 / 100000) 31 * cCG cZ 31) ≤ (476164416136501 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_31 eC_31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_32 : (3465735902643809 / 1000000000000000 : ℝ) ≤ Real.log 32 ∧ Real.log 32 ≤ (433216987913807 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_32
  constructor <;> linarith [h.1, h.2]

theorem eC_32 : (12884802782351 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 32 * cCG cZ 32 ∧ ex (57436 / 100000) 32 * cCG cZ 32 ≤ (64424029134759 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_32 cCB_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_32 : (4575378068103 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 32 * cCG cZ 32) ∧ kappa * (ex (57436 / 100000) 32 * cCG cZ 32) ≤ (366030331939 / 20000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_32 : (-120472076086407 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 32 * sCG cZ 32 ∧ ex (57436 / 100000) 32 * sCG cZ 32 ≤ (-3764751901309 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_32 sCB_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_32 : (-1069487255753 / 31250000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 32 * sCG cZ 32) ∧ kappa * (ex (57436 / 100000) 32 * sCG cZ 32) ≤ (-34223587853447 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_32 : (223276618006393 / 1000000000000000 : ℝ) ≤ Real.log 32 * (ex (57436 / 100000) 32 * cCG cZ 32) ∧ Real.log 32 * (ex (57436 / 100000) 32 * cCG cZ 32) ≤ (111638335404127 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_32 eC_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_32 : (63428208155177 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 32 * (ex (57436 / 100000) 32 * cCG cZ 32)) ∧ kappa * (Real.log 32 * (ex (57436 / 100000) 32 * cCG cZ 32)) ≤ (1585705578877 / 25000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_33 : (699301512262101 / 200000000000000 : ℝ) ≤ Real.log 33 ∧ Real.log 33 ≤ (3496507561977559 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_33
  constructor <;> linarith [h.1, h.2]

theorem eC_33 : (-1301152685079 / 15625000000000 : ℝ) ≤ ex (57436 / 100000) 33 * cCG cZ 33 ∧ ex (57436 / 100000) 33 * cCG cZ 33 ≤ (-83273756807047 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_33 cCB_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_33 : (-23656333482729 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 33 * cCG cZ 33) ∧ kappa * (ex (57436 / 100000) 33 * cCG cZ 33) ≤ (-2957041151343 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_33 : (-105267492820971 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 33 * sCG cZ 33 ∧ ex (57436 / 100000) 33 * sCG cZ 33 ≤ (-10526747777239 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_33 sCB_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_33 : (-29904288708059 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 33 * sCG cZ 33) ∧ kappa * (ex (57436 / 100000) 33 * sCG cZ 33) ≤ (-1869017777067 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_33 : (-291167372970633 / 1000000000000000 : ℝ) ≤ Real.log 33 * (ex (57436 / 100000) 33 * cCG cZ 33) ∧ Real.log 33 * (ex (57436 / 100000) 33 * cCG cZ 33) ≤ (-291167320334571 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_33 eC_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_33 : (-82714548911023 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 33 * (ex (57436 / 100000) 33 * cCG cZ 33)) ∧ kappa * (Real.log 33 * (ex (57436 / 100000) 33 * cCG cZ 33)) ≤ (-82714533958219 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_34 : (3526360524460139 / 1000000000000000 : ℝ) ≤ Real.log 34 ∧ Real.log 34 ≤ (3526360525127523 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_34
  constructor <;> linarith [h.1, h.2]

theorem eC_34 : (-120913134413627 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 34 * cCG cZ 34 ∧ ex (57436 / 100000) 34 * cCG cZ 34 ≤ (-30228279902137 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_34 cCB_34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_34 : (13201425686867 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 34 * sCG cZ 34 ∧ ex (57436 / 100000) 34 * sCG cZ 34 ≤ (52805717526433 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_34 sCB_34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_34 : (-426383304165653 / 1000000000000000 : ℝ) ≤ Real.log 34 * (ex (57436 / 100000) 34 * cCG cZ 34) ∧ Real.log 34 * (ex (57436 / 100000) 34 * cCG cZ 34) ≤ (-42638325187691 / 100000000000000 : ℝ) := by
  exact mul_bounds_of lgB_34 eC_34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_36 : (3583518938300017 / 1000000000000000 : ℝ) ≤ Real.log 36 ∧ Real.log 36 ≤ (3583518938967891 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_36
  constructor <;> linarith [h.1, h.2]

theorem eC_36 : (1893190877751 / 15625000000000 : ℝ) ≤ ex (57436 / 100000) 36 * cCG cZ 36 ∧ ex (57436 / 100000) 36 * cCG cZ 36 ≤ (121164230507653 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_36 cCB_36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_36 : (-20133029582403 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 36 * sCG cZ 36 ∧ ex (57436 / 100000) 36 * sCG cZ 36 ≤ (-10066511216063 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_36 sCB_36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_36 : (217097131655601 / 500000000000000 : ℝ) ≤ Real.log 36 * (ex (57436 / 100000) 36 * cCG cZ 36) ∧ Real.log 36 * (ex (57436 / 100000) 36 * cCG cZ 36) ≤ (217097157374823 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_36 eC_36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_37 : (1805458956244053 / 500000000000000 : ℝ) ≤ Real.log 37 ∧ Real.log 37 ≤ (11284118478613 / 3125000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_37
  constructor <;> linarith [h.1, h.2]

theorem eC_37 : (-57131083584297 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 37 * cCG cZ 37 ∧ ex (57436 / 100000) 37 * cCG cZ 37 ≤ (-57131069539549 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_37 cCB_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_37 : (-8114871799097 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 37 * cCG cZ 37) ∧ kappa * (ex (57436 / 100000) 37 * cCG cZ 37) ≤ (-129837916867 / 8000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_37 : (-111951181453769 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 37 * sCG cZ 37 ∧ ex (57436 / 100000) 37 * sCG cZ 37 ≤ (-22390233477591 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_37 sCB_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_37 : (-31057602133 / 976562500000 : ℝ) ≤ kappa * (ex (57436 / 100000) 37 * sCG cZ 37) ∧ kappa * (ex (57436 / 100000) 37 * sCG cZ 37) ≤ (-7950745147097 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_37 : (-2578695663907 / 12500000000000 : ℝ) ≤ Real.log 37 * (ex (57436 / 100000) 37 * cCG cZ 37) ∧ Real.log 37 * (ex (57436 / 100000) 37 * cCG cZ 37) ≤ (-206295602359961 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_37 eC_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_37 : (-1172085437693 / 20000000000000 : ℝ) ≤ kappa * (Real.log 37 * (ex (57436 / 100000) 37 * cCG cZ 37)) ∧ kappa * (Real.log 37 * (ex (57436 / 100000) 37 * cCG cZ 37)) ≤ (-58604257466899 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_38 : (1818793079785123 / 500000000000000 : ℝ) ≤ Real.log 38 ∧ Real.log 38 ≤ (72751723204769 / 20000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_38
  constructor <;> linarith [h.1, h.2]

theorem eC_38 : (-5688997140021 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 38 * cCG cZ 38 ∧ ex (57436 / 100000) 38 * cCG cZ 38 ≤ (-91023940328689 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_38 cCB_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_38 : (-25857997887169 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 38 * cCG cZ 38) ∧ kappa * (ex (57436 / 100000) 38 * cCG cZ 38) ≤ (-646449848379 / 25000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_38 : (41937664995751 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 38 * sCG cZ 38 ∧ ex (57436 / 100000) 38 * sCG cZ 38 ≤ (16775068778667 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_38 sCB_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_38 : (2978402943223 / 125000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 38 * sCG cZ 38) ∧ kappa * (ex (57436 / 100000) 38 * sCG cZ 38) ≤ (4765445499001 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_38 : (-13244299047793 / 40000000000000 : ℝ) ≤ Real.log 38 * (ex (57436 / 100000) 38 * cCG cZ 38) ∧ Real.log 38 * (ex (57436 / 100000) 38 * cCG cZ 38) ≤ (-331107425529187 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_38 eC_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_38 : (-94060695245839 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 38 * (ex (57436 / 100000) 38 * cCG cZ 38)) ∧ kappa * (Real.log 38 * (ex (57436 / 100000) 38 * cCG cZ 38)) ≤ (-94060680852791 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_39 : (3663561645973489 / 1000000000000000 : ℝ) ≤ Real.log 39 ∧ Real.log 39 ≤ (3663561646641817 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_39
  constructor <;> linarith [h.1, h.2]

theorem eC_39 : (110419168863509 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 39 * cCG cZ 39 ∧ ex (57436 / 100000) 39 * cCG cZ 39 ≤ (55209591278533 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_39 cCB_39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_39 : (10349201520149 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 39 * sCG cZ 39 ∧ ex (57436 / 100000) 39 * sCG cZ 39 ≤ (51746021271767 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_39 sCB_39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_39 : (404527432028621 / 1000000000000000 : ℝ) ≤ Real.log 39 * (ex (57436 / 100000) 39 * cCG cZ 39) ∧ Real.log 39 * (ex (57436 / 100000) 39 * cCG cZ 39) ≤ (404527482269609 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_39 eC_39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_41 : (3713572066548123 / 1000000000000000 : ℝ) ≤ Real.log 41 ∧ Real.log 41 ≤ (3713572067216643 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_41
  constructor <;> linarith [h.1, h.2]

theorem eC_41 : (-1870905301011 / 20000000000000 : ℝ) ≤ ex (57436 / 100000) 41 * cCG cZ 41 ∧ ex (57436 / 100000) 41 * cCG cZ 41 ≤ (-93545251745923 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_41 cCB_41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_41 : (14545306514247 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 41 * sCG cZ 41 ∧ ex (57436 / 100000) 41 * sCG cZ 41 ≤ (28408806979 / 390625000000 : ℝ) := by
  exact mul_bounds_of exB_41 sCB_41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_41 : (-3473870833121 / 10000000000000 : ℝ) ≤ Real.log 41 * (ex (57436 / 100000) 41 * cCG cZ 41) ∧ Real.log 41 * (ex (57436 / 100000) 41 * cCG cZ 41) ≤ (-347387033841871 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_41 eC_41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_42 : (3737669618127173 / 1000000000000000 : ℝ) ≤ Real.log 42 ∧ Real.log 42 ≤ (3737669618795767 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_42
  constructor <;> linarith [h.1, h.2]

theorem eC_42 : (57155301898181 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 42 * cCG cZ 42 ∧ ex (57436 / 100000) 42 * cCG cZ 42 ≤ (114310616929601 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_42 cCB_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_42 : (3247324702729 / 100000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 42 * cCG cZ 42) ∧ kappa * (ex (57436 / 100000) 42 * cCG cZ 42) ≤ (32473250758169 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_42 : (2428243044171 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 42 * sCG cZ 42 ∧ ex (57436 / 100000) 42 * sCG cZ 42 ≤ (194259548323 / 8000000000000 : ℝ) := by
  exact mul_bounds_of exB_42 sCB_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_42 : (3449064811001 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 42 * sCG cZ 42) ∧ kappa * (ex (57436 / 100000) 42 * sCG cZ 42) ≤ (6898133343059 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_42 : (213627635419717 / 500000000000000 : ℝ) ≤ Real.log 42 * (ex (57436 / 100000) 42 * cCG cZ 42) ∧ Real.log 42 * (ex (57436 / 100000) 42 * cCG cZ 42) ≤ (427255320003571 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_42 eC_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_42 : (60687134407921 / 500000000000000 : ℝ) ≤ kappa * (Real.log 42 * (ex (57436 / 100000) 42 * cCG cZ 42)) ∧ kappa * (Real.log 42 * (ex (57436 / 100000) 42 * cCG cZ 42)) ≤ (24274856556469 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_43 : (1880600057768679 / 500000000000000 : ℝ) ≤ Real.log 43 ∧ Real.log 43 ≤ (1880600058103007 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_43
  constructor <;> linarith [h.1, h.2]

theorem eC_43 : (-6373502099781 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 43 * cCG cZ 43 ∧ ex (57436 / 100000) 43 * cCG cZ 43 ≤ (-31867504061031 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_43 cCB_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_43 : (-18105783824207 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 43 * cCG cZ 43) ∧ kappa * (ex (57436 / 100000) 43 * cCG cZ 43) ≤ (-4526445041619 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_43 : (-19214796166007 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 43 * sCG cZ 43 ∧ ex (57436 / 100000) 43 * sCG cZ 43 ≤ (-24018491985373 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_43 sCB_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_43 : (-27292604612139 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 43 * sCG cZ 43) ∧ kappa * (ex (57436 / 100000) 43 * sCG cZ 43) ≤ (-27292600950773 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_43 : (-59930042095839 / 250000000000000 : ℝ) ≤ Real.log 43 * (ex (57436 / 100000) 43 * cCG cZ 43) ∧ Real.log 43 * (ex (57436 / 100000) 43 * cCG cZ 43) ≤ (-119860059956237 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_43 eC_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_43 : (-68099476223607 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 43 * (ex (57436 / 100000) 43 * cCG cZ 43)) ∧ kappa * (Real.log 43 * (ex (57436 / 100000) 43 * cCG cZ 43)) ≤ (-17024865613511 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_44 : (3784189633762049 / 1000000000000000 : ℝ) ≤ Real.log 44 ∧ Real.log 44 ≤ (3784189634430759 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_44
  constructor <;> linarith [h.1, h.2]

theorem eC_44 : (-567682533251 / 50000000000000 : ℝ) ≤ ex (57436 / 100000) 44 * cCG cZ 44 ∧ ex (57436 / 100000) 44 * cCG cZ 44 ≤ (-354801185663 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_44 cCB_44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_44 : (28303066271331 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 44 * sCG cZ 44 ∧ ex (57436 / 100000) 44 * sCG cZ 44 ≤ (113212277848251 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_44 sCB_44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_44 : (-42964367159517 / 1000000000000000 : ℝ) ≤ Real.log 44 * (ex (57436 / 100000) 44 * cCG cZ 44) ∧ Real.log 44 * (ex (57436 / 100000) 44 * cCG cZ 44) ≤ (-42964319002637 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_44 eC_44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_46 : (3828641396332871 / 1000000000000000 : ℝ) ≤ Real.log 46 ∧ Real.log 46 ≤ (59822521828151 / 15625000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_46
  constructor <;> linarith [h.1, h.2]

theorem eC_46 : (-4161802916503 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 46 * cCG cZ 46 ∧ ex (57436 / 100000) 46 * cCG cZ 46 ≤ (-104045060495927 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_46 cCB_46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_46 : (38419894379671 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 46 * sCG cZ 46 ∧ ex (57436 / 100000) 46 * sCG cZ 46 ≤ (9604976692777 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_46 sCB_46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_46 : (-199175636653571 / 500000000000000 : ℝ) ≤ Real.log 46 * (ex (57436 / 100000) 46 * cCG cZ 46) ∧ Real.log 46 * (ex (57436 / 100000) 46 * cCG cZ 46) ≤ (-398351225698663 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_46 eC_46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_47 : (385014760155383 / 100000000000000 : ℝ) ≤ Real.log 47 ∧ Real.log 47 ≤ (60158556284729 / 15625000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_47
  constructor <;> linarith [h.1, h.2]

theorem eC_47 : (109154719870307 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 47 * cCG cZ 47 ∧ ex (57436 / 100000) 47 * cCG cZ 47 ≤ (27288683038043 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_47 cCB_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_47 : (969017764107 / 31250000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 47 * cCG cZ 47) ∧ kappa * (ex (57436 / 100000) 47 * cCG cZ 47) ≤ (15504285970223 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_47 : (9302185536243 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 47 * sCG cZ 47 ∧ ex (57436 / 100000) 47 * sCG cZ 47 ≤ (9302197779749 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_47 sCB_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_47 : (1321277986381 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 47 * sCG cZ 47) ∧ kappa * (ex (57436 / 100000) 47 * sCG cZ 47) ≤ (1321279725443 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_47 : (210130891453471 / 500000000000000 : ℝ) ≤ Real.log 47 * (ex (57436 / 100000) 47 * cCG cZ 47) ∧ Real.log 47 * (ex (57436 / 100000) 47 * cCG cZ 47) ≤ (210130915133471 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_47 eC_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_47 : (11938756545087 / 100000000000000 : ℝ) ≤ kappa * (Real.log 47 * (ex (57436 / 100000) 47 * cCG cZ 47)) ∧ kappa * (Real.log 47 * (ex (57436 / 100000) 47 * cCG cZ 47)) ≤ (23877515780971 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_48 : (1935600505375829 / 500000000000000 : ℝ) ≤ Real.log 48 ∧ Real.log 48 ≤ (3871201011420513 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_48
  constructor <;> linarith [h.1, h.2]

theorem eC_48 : (-19506970600659 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 48 * cCG cZ 48 ∧ ex (57436 / 100000) 48 * cCG cZ 48 ≤ (-9753484091259 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_48 cCB_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_48 : (-6926901945573 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 48 * cCG cZ 48) ∧ kappa * (ex (57436 / 100000) 48 * cCG cZ 48) ≤ (-1108304173903 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_48 : (-46919889355091 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 48 * sCG cZ 48 ∧ ex (57436 / 100000) 48 * sCG cZ 48 ≤ (-23459938641923 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_48 sCB_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_48 : (-13328957305093 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 48 * sCG cZ 48) ∧ kappa * (ex (57436 / 100000) 48 * sCG cZ 48) ≤ (-208264904311 / 15625000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_48 : (-377577021595107 / 1000000000000000 : ℝ) ≤ Real.log 48 * (ex (57436 / 100000) 48 * cCG cZ 48) ∧ Real.log 48 * (ex (57436 / 100000) 48 * cCG cZ 48) ≤ (-2359856092027 / 6250000000000 : ℝ) := by
  exact mul_bounds_of lgB_48 eC_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_48 : (-107261719270849 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 48 * (ex (57436 / 100000) 48 * cCG cZ 48)) ∧ kappa * (Real.log 48 * (ex (57436 / 100000) 48 * cCG cZ 48)) ≤ (-41899103889 / 390625000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_49 : (389182029795439 / 100000000000000 : ℝ) ≤ Real.log 49 ∧ Real.log 49 ≤ (389182029862327 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_49
  constructor <;> linarith [h.1, h.2]

theorem eC_49 : (79024273990009 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 49 * cCG cZ 49 ∧ ex (57436 / 100000) 49 * cCG cZ 49 ≤ (3951214300889 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_49 cCB_49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_49 : (72079655092859 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 49 * sCG cZ 49 ∧ ex (57436 / 100000) 49 * sCG cZ 49 ≤ (18019916778083 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_49 sCB_49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_49 : (153774136772713 / 500000000000000 : ℝ) ≤ Real.log 49 * (ex (57436 / 100000) 49 * cCG cZ 49) ∧ Real.log 49 * (ex (57436 / 100000) 49 * cCG cZ 49) ≤ (19221770025513 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_49 eC_49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_51 : (982956408142021 / 250000000000000 : ℝ) ≤ Real.log 51 ∧ Real.log 51 ≤ (982956408309251 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_51
  constructor <;> linarith [h.1, h.2]

theorem eC_51 : (45885226979717 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 51 * cCG cZ 51 ∧ ex (57436 / 100000) 51 * cCG cZ 51 ≤ (22942619366711 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_51 cCB_51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_51 : (93920269677191 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 51 * sCG cZ 51 ∧ ex (57436 / 100000) 51 * sCG cZ 51 ≤ (93920281449369 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_51 sCB_51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_51 : (36082542319011 / 200000000000000 : ℝ) ≤ Real.log 51 * (ex (57436 / 100000) 51 * cCG cZ 51) ∧ Real.log 51 * (ex (57436 / 100000) 51 * cCG cZ 51) ≤ (180412757839269 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_51 eC_51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_52 : (3951243718425183 / 1000000000000000 : ℝ) ≤ Real.log 52 ∧ Real.log 52 ≤ (3951243719094119 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_52
  constructor <;> linarith [h.1, h.2]

theorem eC_52 : (-1836849409643 / 50000000000000 : ℝ) ≤ ex (57436 / 100000) 52 * cCG cZ 52 ∧ ex (57436 / 100000) 52 * cCG cZ 52 ≤ (-9184244160503 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_52 cCB_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_52 : (-2087241695881 / 200000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 52 * cCG cZ 52) ∧ kappa * (ex (57436 / 100000) 52 * cCG cZ 52) ≤ (-208724103961 / 20000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_52 : (-96622155196173 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 52 * sCG cZ 52 ∧ ex (57436 / 100000) 52 * sCG cZ 52 ≤ (-96622143622313 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_52 sCB_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_52 : (-27448329461929 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 52 * sCG cZ 52) ∧ kappa * (ex (57436 / 100000) 52 * sCG cZ 52) ≤ (-27448326174037 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_52 : (-145156793855473 / 1000000000000000 : ℝ) ≤ Real.log 52 * (ex (57436 / 100000) 52 * cCG cZ 52) ∧ Real.log 52 * (ex (57436 / 100000) 52 * cCG cZ 52) ≤ (-72578374095341 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_52 eC_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_52 : (-41236003205403 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 52 * (ex (57436 / 100000) 52 * cCG cZ 52)) ∧ kappa * (Real.log 52 * (ex (57436 / 100000) 52 * cCG cZ 52)) ≤ (-1288624694781 / 31250000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_53 : (31762335307167 / 8000000000000 : ℝ) ≤ Real.log 53 ∧ Real.log 53 ≤ (1985145957032413 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_53
  constructor <;> linarith [h.1, h.2]

theorem eC_53 : (33498863282687 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 53 * cCG cZ 53 ∧ ex (57436 / 100000) 53 * cCG cZ 53 ≤ (6699774946401 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_53 cCB_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_53 : (4758162525543 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 53 * cCG cZ 53) ∧ kappa * (ex (57436 / 100000) 53 * cCG cZ 53) ≤ (4758164151799 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_53 : (96602282807079 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 53 * sCG cZ 53 ∧ ex (57436 / 100000) 53 * sCG cZ 53 ≤ (24150573570161 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_53 sCB_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_53 : (6860671033159 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 53 * sCG cZ 53) ∧ kappa * (ex (57436 / 100000) 53 * sCG cZ 53) ≤ (6860671848009 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_53 : (66500132999603 / 500000000000000 : ℝ) ≤ Real.log 53 * (ex (57436 / 100000) 53 * cCG cZ 53) ∧ Real.log 53 * (ex (57436 / 100000) 53 * cCG cZ 53) ≤ (106400249183 / 800000000000 : ℝ) := by
  exact mul_bounds_of lgB_53 eC_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_53 : (18891294197787 / 500000000000000 : ℝ) ≤ kappa * (Real.log 53 * (ex (57436 / 100000) 53 * cCG cZ 53)) ∧ kappa * (Real.log 53 * (ex (57436 / 100000) 53 * cCG cZ 53)) ≤ (37782601315361 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_54 : (1994492023204013 / 500000000000000 : ℝ) ≤ Real.log 54 ∧ Real.log 54 ≤ (3988984047076989 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_54
  constructor <;> linarith [h.1, h.2]

theorem eC_54 : (-35968281938247 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 54 * cCG cZ 54 ∧ ex (57436 / 100000) 54 * cCG cZ 54 ≤ (-35968270566203 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_54 cCB_54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_54 : (-47271505638533 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 54 * sCG cZ 54 ∧ ex (57436 / 100000) 54 * sCG cZ 54 ≤ (-94542999882513 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_54 sCB_54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_54 : (-28695380570487 / 200000000000000 : ℝ) ≤ Real.log 54 * (ex (57436 / 100000) 54 * cCG cZ 54) ∧ Real.log 54 * (ex (57436 / 100000) 54 * cCG cZ 54) ≤ (-143476857465471 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_54 eC_54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_56 : (2012675845289449 / 500000000000000 : ℝ) ≤ Real.log 56 ∧ Real.log 56 ≤ (2012675845623941 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_56
  constructor <;> linarith [h.1, h.2]

theorem eC_56 : (-27650277714363 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 56 * cCG cZ 56 ∧ ex (57436 / 100000) 56 * cCG cZ 56 ≤ (-55300544340271 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_56 cCB_56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_56 : (-16438119256399 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 56 * sCG cZ 56 ∧ ex (57436 / 100000) 56 * sCG cZ 56 ≤ (-2054764629571 / 25000000000000 : ℝ) := by
  exact mul_bounds_of exB_56 sCB_56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_56 : (-22260418432197 / 100000000000000 : ℝ) ≤ Real.log 56 * (ex (57436 / 100000) 56 * cCG cZ 56) ∧ Real.log 56 * (ex (57436 / 100000) 56 * cCG cZ 56) ≤ (-222604139650043 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_56 eC_56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_57 : (2021525633839149 / 500000000000000 : ℝ) ≤ Real.log 57 ∧ Real.log 57 ≤ (404305126834729 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_57
  constructor <;> linarith [h.1, h.2]

theorem eC_57 : (69467008206071 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 57 * cCG cZ 57 ∧ ex (57436 / 100000) 57 * cCG cZ 57 ≤ (69467019200231 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_57 cCB_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_57 : (9867060634817 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 57 * cCG cZ 57) ∧ kappa * (ex (57436 / 100000) 57 * cCG cZ 57) ≤ (9867062196423 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_57 : (34605875229887 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 57 * sCG cZ 57 ∧ ex (57436 / 100000) 57 * sCG cZ 57 ≤ (17302940360883 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_57 sCB_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_57 : (19661607893133 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 57 * sCG cZ 57) ∧ kappa * (ex (57436 / 100000) 57 * sCG cZ 57) ≤ (1966161101339 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_57 : (140429337794687 / 500000000000000 : ℝ) ≤ Real.log 57 * (ex (57436 / 100000) 57 * cCG cZ 57) ∧ Real.log 57 * (ex (57436 / 100000) 57 * cCG cZ 57) ≤ (1404293600429 / 5000000000000 : ℝ) := by
  exact mul_bounds_of lgB_57 eC_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_57 : (79786064015713 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 57 * (ex (57436 / 100000) 57 * cCG cZ 57)) ∧ kappa * (Real.log 57 * (ex (57436 / 100000) 57 * cCG cZ 57)) ≤ (79786076656217 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_58 : (4060443010370279 / 1000000000000000 : ℝ) ≤ Real.log 58 ∧ Real.log 58 ≤ (2030221505569357 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_58
  constructor <;> linarith [h.1, h.2]

theorem eC_58 : (-16680929826759 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 58 * cCG cZ 58 ∧ ex (57436 / 100000) 58 * cCG cZ 58 ≤ (-83404636662333 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_58 cCB_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_58 : (-11846756488887 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 58 * cCG cZ 58) ∧ kappa * (ex (57436 / 100000) 58 * cCG cZ 58) ≤ (-5923377358723 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_58 : (-1242325480627 / 25000000000000 : ℝ) ≤ ex (57436 / 100000) 58 * sCG cZ 58 ∧ ex (57436 / 100000) 58 * sCG cZ 58 ≤ (-4969300676861 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_58 sCB_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_58 : (-3529186346751 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 58 * sCG cZ 58) ∧ kappa * (ex (57436 / 100000) 58 * sCG cZ 58) ≤ (-14116741848381 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_58 : (-67731964934359 / 200000000000000 : ℝ) ≤ Real.log 58 * (ex (57436 / 100000) 58 * cCG cZ 58) ∧ Real.log 58 * (ex (57436 / 100000) 58 * cCG cZ 58) ≤ (-169329886984021 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_58 eC_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_58 : (-48103079589963 / 500000000000000 : ℝ) ≤ kappa * (Real.log 58 * (ex (57436 / 100000) 58 * cCG cZ 58)) ∧ kappa * (Real.log 58 * (ex (57436 / 100000) 58 * cCG cZ 58)) ≤ (-96206144776051 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_59 : (2038768721855667 / 500000000000000 : ℝ) ≤ Real.log 59 ∧ Real.log 59 ≤ (4077537444570997 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_59
  constructor <;> linarith [h.1, h.2]

theorem eC_59 : (9334528512827 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 59 * cCG cZ 59 ∧ ex (57436 / 100000) 59 * cCG cZ 59 ≤ (93345299008081 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_59 cCB_59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_59 : (23002199404671 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 59 * sCG cZ 59 ∧ ex (57436 / 100000) 59 * sCG cZ 59 ≤ (23002213249747 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_59 sCB_59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_59 : (380618895304431 / 1000000000000000 : ℝ) ≤ Real.log 59 * (ex (57436 / 100000) 59 * cCG cZ 59) ∧ Real.log 59 * (ex (57436 / 100000) 59 * cCG cZ 59) ≤ (380618951980127 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_59 eC_59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_61 : (205543693197337 / 50000000000000 : ℝ) ≤ Real.log 61 ∧ Real.log 61 ≤ (2055436932483667 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_61
  constructor <;> linarith [h.1, h.2]

theorem eC_61 : (41569346333477 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 61 * cCG cZ 61 ∧ ex (57436 / 100000) 61 * cCG cZ 61 ≤ (10392338598831 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_61 cCB_61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_61 : (-44532697461097 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 61 * sCG cZ 61 ∧ ex (57436 / 100000) 61 * sCG cZ 61 ≤ (-5566585170009 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_61 sCB_61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_61 : (341772678767281 / 1000000000000000 : ℝ) ≤ Real.log 61 * (ex (57436 / 100000) 61 * cCG cZ 61) ∧ Real.log 61 * (ex (57436 / 100000) 61 * cCG cZ 61) ≤ (68354549026921 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_61 eC_61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_62 : (515891798100539 / 125000000000000 : ℝ) ≤ Real.log 62 ∧ Real.log 62 ≤ (82542687717919 / 20000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_62
  constructor <;> linarith [h.1, h.2]

theorem eC_62 : (-56136486665329 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 62 * cCG cZ 62 ∧ ex (57436 / 100000) 62 * cCG cZ 62 ≤ (-28068234824037 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_62 cCB_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_62 : (-15947199456447 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 62 * cCG cZ 62) ∧ kappa * (ex (57436 / 100000) 62 * cCG cZ 62) ≤ (-15947194622201 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_62 : (37347319394277 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 62 * sCG cZ 62 ∧ ex (57436 / 100000) 62 * sCG cZ 62 ≤ (74694655818397 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_62 sCB_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_62 : (21219181567057 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 62 * sCG cZ 62) ∧ kappa * (ex (57436 / 100000) 62 * sCG cZ 62) ≤ (21219186404879 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_62 : (-231682824419869 / 1000000000000000 : ℝ) ≤ Real.log 62 * (ex (57436 / 100000) 62 * cCG cZ 62) ∧ Real.log 62 * (ex (57436 / 100000) 62 * cCG cZ 62) ≤ (-231682754126089 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_62 eC_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_62 : (-65816235235443 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 62 * (ex (57436 / 100000) 62 * cCG cZ 62)) ∧ kappa * (Real.log 62 * (ex (57436 / 100000) 62 * cCG cZ 62)) ≤ (-16454053816613 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_63 : (828626945227529 / 200000000000000 : ℝ) ≤ Real.log 63 ∧ Real.log 63 ≤ (517891840911853 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_63
  constructor <;> linarith [h.1, h.2]

theorem eC_63 : (15355155816633 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 63 * cCG cZ 63 ∧ ex (57436 / 100000) 63 * cCG cZ 63 ≤ (307103474001 / 20000000000000 : ℝ) := by
  exact mul_bounds_of exB_63 cCB_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_63 : (4362077982409 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 63 * cCG cZ 63) ∧ kappa * (ex (57436 / 100000) 63 * cCG cZ 63) ≤ (2181041531357 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_63 : (-91300674721221 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 63 * sCG cZ 63 ∧ ex (57436 / 100000) 63 * sCG cZ 63 ≤ (-3652026271493 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_63 sCB_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_63 : (-2593660837679 / 100000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 63 * sCG cZ 63) ∧ kappa * (ex (57436 / 100000) 63 * sCG cZ 63) ≤ (-810518852567 / 31250000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_63 : (31809239644573 / 500000000000000 : ℝ) ≤ Real.log 63 * (ex (57436 / 100000) 63 * cCG cZ 63) ∧ Real.log 63 * (ex (57436 / 100000) 63 * cCG cZ 63) ≤ (31809276700161 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_63 eC_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_63 : (18072676767041 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 63 * (ex (57436 / 100000) 63 * cCG cZ 63)) ∧ kappa * (Real.log 63 * (ex (57436 / 100000) 63 * cCG cZ 63)) ≤ (9036348910237 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_64 : (1039720770773419 / 250000000000000 : ℝ) ≤ Real.log 64 ∧ Real.log 64 ≤ (831776616862279 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_64
  constructor <;> linarith [h.1, h.2]

theorem eC_64 : (1269428820047 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 64 * cCG cZ 64 ∧ ex (57436 / 100000) 64 * cCG cZ 64 ≤ (15867869568859 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_64 cCB_64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_64 : (86085798337637 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 64 * sCG cZ 64 ∧ ex (57436 / 100000) 64 * sCG cZ 64 ≤ (17217163402439 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_64 sCB_64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_64 : (1055881208977 / 8000000000000 : ℝ) ≤ Real.log 64 * (ex (57436 / 100000) 64 * cCG cZ 64) ∧ Real.log 64 * (ex (57436 / 100000) 64 * cCG cZ 64) ≤ (5279409146719 / 40000000000000 : ℝ) := by
  exact mul_bounds_of lgB_64 eC_64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_66 : (261853421358679 / 62500000000000 : ℝ) ≤ Real.log 66 ∧ Real.log 66 ≤ (837930948612883 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_66
  constructor <;> linarith [h.1, h.2]

theorem eC_66 : (89994155588009 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 66 * cCG cZ 66 ∧ ex (57436 / 100000) 66 * cCG cZ 66 ≤ (17998835121239 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_66 cCB_66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_66 : (5158835630977 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 66 * sCG cZ 66 ∧ ex (57436 / 100000) 66 * sCG cZ 66 ≤ (1289713896143 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_66 sCB_66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_66 : (188522220344043 / 500000000000000 : ℝ) ≤ Real.log 66 * (ex (57436 / 100000) 66 * cCG cZ 66) ∧ Real.log 66 * (ex (57436 / 100000) 66 * cCG cZ 66) ≤ (377044524676667 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_66 eC_66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_67 : (131396644346681 / 31250000000000 : ℝ) ≤ Real.log 67 ∧ Real.log 67 ≤ (840938524093481 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_67
  constructor <;> linarith [h.1, h.2]

theorem eC_67 : (-74710957246621 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 67 * cCG cZ 67 ∧ ex (57436 / 100000) 67 * cCG cZ 67 ≤ (-74710936687311 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_67 cCB_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_67 : (-21223817299023 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 67 * cCG cZ 67) ∧ kappa * (ex (57436 / 100000) 67 * cCG cZ 67) ≤ (-2652976432319 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_67 : (245187622489 / 5000000000000 : ℝ) ≤ ex (57436 / 100000) 67 * sCG cZ 67 ∧ ex (57436 / 100000) 67 * sCG cZ 67 ≤ (49037545036591 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_67 sCB_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_67 : (2786106614327 / 200000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 67 * sCG cZ 67) ∧ kappa * (ex (57436 / 100000) 67 * sCG cZ 67) ≤ (3482634726569 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_67 : (-78534152650731 / 250000000000000 : ℝ) ≤ Real.log 67 * (ex (57436 / 100000) 67 * cCG cZ 67) ∧ Real.log 67 * (ex (57436 / 100000) 67 * cCG cZ 67) ≤ (-981676637671 / 3125000000000 : ℝ) := by
  exact mul_bounds_of lgB_67 eC_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_67 : (-89239627975347 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 67 * (ex (57436 / 100000) 67 * cCG cZ 67)) ∧ kappa * (Real.log 67 * (ex (57436 / 100000) 67 * cCG cZ 67)) ≤ (-17847920677763 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_68 : (1054876926217503 / 250000000000000 : ℝ) ≤ Real.log 68 ∧ Real.log 68 ≤ (421950770628823 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_68
  constructor <;> linarith [h.1, h.2]

theorem eC_68 : (27433564294279 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 68 * cCG cZ 68 ∧ ex (57436 / 100000) 68 * cCG cZ 68 ≤ (27433585268933 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_68 cCB_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_68 : (7793300713853 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 68 * cCG cZ 68) ∧ kappa * (ex (57436 / 100000) 68 * cCG cZ 68) ≤ (7793306672313 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_68 : (-8425580356151 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 68 * sCG cZ 68 ∧ ex (57436 / 100000) 68 * sCG cZ 68 ≤ (-10531972817571 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_68 sCB_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_68 : (-149595675711 / 6250000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 68 * sCG cZ 68) ∧ kappa * (ex (57436 / 100000) 68 * sCG cZ 68) ≤ (-478706042843 / 20000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_68 : (115756135911757 / 1000000000000000 : ℝ) ≤ Real.log 68 * (ex (57436 / 100000) 68 * cCG cZ 68) ∧ Real.log 68 * (ex (57436 / 100000) 68 * cCG cZ 68) ≤ (115756224453379 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_68 eC_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_68 : (4110486551059 / 125000000000000 : ℝ) ≤ kappa * (Real.log 68 * (ex (57436 / 100000) 68 * cCG cZ 68)) ∧ kappa * (Real.log 68 * (ex (57436 / 100000) 68 * cCG cZ 68)) ≤ (32883917561293 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_69 : (1058526626070719 / 250000000000000 : ℝ) ≤ Real.log 69 ∧ Real.log 69 ≤ (4234106505742537 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_69
  constructor <;> linarith [h.1, h.2]

theorem eC_69 : (6785633736879 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 69 * cCG cZ 69 ∧ ex (57436 / 100000) 69 * cCG cZ 69 ≤ (212051188039 / 6250000000000 : ℝ) := by
  exact mul_bounds_of exB_69 cCB_69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_69 : (20263796284861 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 69 * sCG cZ 69 ∧ ex (57436 / 100000) 69 * sCG cZ 69 ≤ (81055206580803 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_69 sCB_69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_69 : (143655479705003 / 1000000000000000 : ℝ) ≤ Real.log 69 * (ex (57436 / 100000) 69 * cCG cZ 69) ∧ Real.log 69 * (ex (57436 / 100000) 69 * cCG cZ 69) ≤ (143655570372219 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_69 eC_69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_71 : (852535975342409 / 200000000000000 : ℝ) ≤ Real.log 71 ∧ Real.log 71 ≤ (4262679878246141 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_71
  constructor <;> linarith [h.1, h.2]

theorem eC_71 : (20285301831917 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 71 * cCG cZ 71 ∧ ex (57436 / 100000) 71 * cCG cZ 71 ≤ (16228245905811 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_71 cCB_71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_71 : (-5959383795771 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 71 * sCG cZ 71 ∧ ex (57436 / 100000) 71 * sCG cZ 71 ≤ (-29796896822711 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_71 sCB_71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_71 : (34587899164777 / 100000000000000 : ℝ) ≤ Real.log 71 * (ex (57436 / 100000) 71 * cCG cZ 71) ∧ Real.log 71 * (ex (57436 / 100000) 71 * cCG cZ 71) ≤ (69175817281931 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_71 eC_71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_72 : (133645816208753 / 31250000000000 : ℝ) ≤ Real.log 72 ∧ Real.log 72 ≤ (106916653006191 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_72
  constructor <;> linarith [h.1, h.2]

theorem eC_72 : (-4230059931683 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 72 * cCG cZ 72 ∧ ex (57436 / 100000) 72 * cCG cZ 72 ≤ (-33840456983227 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_72 cCB_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_72 : (-4806685523121 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 72 * cCG cZ 72) ∧ kappa * (ex (57436 / 100000) 72 * cCG cZ 72) ≤ (-9613364662917 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_72 : (15757525084949 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 72 * sCG cZ 72 ∧ ex (57436 / 100000) 72 * sCG cZ 72 ≤ (2462113997983 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_72 sCB_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_72 : (11190956648559 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 72 * sCG cZ 72) ∧ kappa * (ex (57436 / 100000) 72 * sCG cZ 72) ≤ (1119095984597 / 50000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_72 : (-72362215985783 / 500000000000000 : ℝ) ≤ Real.log 72 * (ex (57436 / 100000) 72 * cCG cZ 72) ∧ Real.log 72 * (ex (57436 / 100000) 72 * cCG cZ 72) ≤ (-72362167910409 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_72 eC_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_72 : (-4111317825483 / 100000000000000 : ℝ) ≤ kappa * (Real.log 72 * (ex (57436 / 100000) 72 * cCG cZ 72)) ∧ kappa * (Real.log 72 * (ex (57436 / 100000) 72 * cCG cZ 72)) ≤ (-160598245861 / 3906250000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_73 : (4290459440806191 / 1000000000000000 : ℝ) ≤ Real.log 73 ∧ Real.log 73 ≤ (4290459442404939 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_73
  constructor <;> linarith [h.1, h.2]

theorem eC_73 : (-9051110971329 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 73 * cCG cZ 73 ∧ ex (57436 / 100000) 73 * cCG cZ 73 ≤ (-9051105293993 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_73 cCB_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_73 : (-2056984760343 / 200000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 73 * cCG cZ 73) ∧ kappa * (ex (57436 / 100000) 73 * cCG cZ 73) ≤ (-2056983470093 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_73 : (-76982642998657 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 73 * sCG cZ 73 ∧ ex (57436 / 100000) 73 * sCG cZ 73 ≤ (-76982620251857 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_73 sCB_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_73 : (-21869155615367 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 73 * sCG cZ 73) ∧ kappa * (ex (57436 / 100000) 73 * sCG cZ 73) ≤ (-21869149153477 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_73 : (-77666849062387 / 500000000000000 : ℝ) ≤ Real.log 73 * (ex (57436 / 100000) 73 * cCG cZ 73) ∧ Real.log 73 * (ex (57436 / 100000) 73 * cCG cZ 73) ≤ (-38833400158343 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_73 eC_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_73 : (-22063524219741 / 500000000000000 : ℝ) ≤ kappa * (Real.log 73 * (ex (57436 / 100000) 73 * cCG cZ 73)) ∧ kappa * (Real.log 73 * (ex (57436 / 100000) 73 * cCG cZ 73)) ≤ (-5515877593027 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_74 : (2152032546428071 / 500000000000000 : ℝ) ≤ Real.log 74 ∧ Real.log 74 ≤ (1076016273621007 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_74
  constructor <;> linarith [h.1, h.2]

theorem eC_74 : (10210817900873 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 74 * cCG cZ 74 ∧ ex (57436 / 100000) 74 * cCG cZ 74 ≤ (5105410386957 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_74 cCB_74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_74 : (21264126400403 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 74 * sCG cZ 74 ∧ ex (57436 / 100000) 74 * sCG cZ 74 ≤ (10632074664117 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_74 sCB_74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_74 : (21974012448329 / 62500000000000 : ℝ) ≤ Real.log 74 * (ex (57436 / 100000) 74 * cCG cZ 74) ∧ Real.log 74 * (ex (57436 / 100000) 74 * cCG cZ 74) ≤ (175792149116143 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_74 eC_74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_76 : (4330733339927761 / 1000000000000000 : ℝ) ≤ Real.log 76 ∧ Real.log 76 ≤ (4330733341608359 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_76
  constructor <;> linarith [h.1, h.2]

theorem eC_76 : (-1497494858617 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 76 * cCG cZ 76 ∧ ex (57436 / 100000) 76 * cCG cZ 76 ≤ (-187183945741 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_76 cCB_76 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_76 : (-83112335099837 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 76 * sCG cZ 76 ∧ ex (57436 / 100000) 76 * sCG cZ 76 ≤ (-20778077932091 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_76 sCB_76 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_76 : (-64852509131 / 10000000000000 : ℝ) ≤ Real.log 76 * (ex (57436 / 100000) 76 * cCG cZ 76) ∧ Real.log 76 * (ex (57436 / 100000) 76 * cCG cZ 76) ≤ (-3242575018079 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_76 eC_76 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_77 : (4343805421490343 / 1000000000000000 : ℝ) ≤ Real.log 77 ∧ Real.log 77 ≤ (4343805423194797 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_77
  constructor <;> linarith [h.1, h.2]

theorem eC_77 : (68674184143139 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 77 * cCG cZ 77 ∧ ex (57436 / 100000) 77 * cCG cZ 77 ≤ (4292137978389 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_77 cCB_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_77 : (19508896567903 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 77 * cCG cZ 77) ∧ kappa * (ex (57436 / 100000) 77 * cCG cZ 77) ≤ (1950890324691 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_77 : (45724932716123 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 77 * sCG cZ 77 ∧ ex (57436 / 100000) 77 * sCG cZ 77 ≤ (45724956204463 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_77 sCB_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_77 : (12989495165663 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 77 * sCG cZ 77) ∧ kappa * (ex (57436 / 100000) 77 * sCG cZ 77) ≤ (12989501838209 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_77 : (298307293397393 / 1000000000000000 : ℝ) ≤ Real.log 77 * (ex (57436 / 100000) 77 * cCG cZ 77) ∧ Real.log 77 * (ex (57436 / 100000) 77 * cCG cZ 77) ≤ (37288424455253 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_77 eC_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_77 : (10592856334869 / 125000000000000 : ℝ) ≤ kappa * (Real.log 77 * (ex (57436 / 100000) 77 * cCG cZ 77)) ∧ kappa * (Real.log 77 * (ex (57436 / 100000) 77 * cCG cZ 77)) ≤ (8474287972451 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_78 : (4356708826321779 / 1000000000000000 : ℝ) ≤ Real.log 78 ∧ Real.log 78 ≤ (4356708828048589 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_78
  constructor <;> linarith [h.1, h.2]

theorem eC_78 : (-15047337752357 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 78 * cCG cZ 78 ∧ ex (57436 / 100000) 78 * cCG cZ 78 ≤ (-3009466602777 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_78 cCB_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_78 : (-21373166605167 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 78 * cCG cZ 78) ∧ kappa * (ex (57436 / 100000) 78 * cCG cZ 78) ≤ (-21373159874663 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_78 : (16172559000479 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 78 * sCG cZ 78 ∧ ex (57436 / 100000) 78 * sCG cZ 78 ≤ (32345141650773 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_78 sCB_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_78 : (9188570194617 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 78 * sCG cZ 78) ∧ kappa * (ex (57436 / 100000) 78 * sCG cZ 78) ≤ (1837715382607 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_78 : (-327784346121613 / 1000000000000000 : ℝ) ≤ Real.log 78 * (ex (57436 / 100000) 78 * cCG cZ 78) ∧ Real.log 78 * (ex (57436 / 100000) 78 * cCG cZ 78) ≤ (-327784242770979 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_78 eC_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_78 : (-93116663632083 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 78 * (ex (57436 / 100000) 78 * cCG cZ 78)) ∧ kappa * (Real.log 78 * (ex (57436 / 100000) 78 * cCG cZ 78)) ≤ (-93116634272333 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_79 : (546180981511877 / 125000000000000 : ℝ) ≤ Real.log 79 ∧ Real.log 79 ≤ (4369447853842793 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_79
  constructor <;> linarith [h.1, h.2]

theorem eC_79 : (1866174069 / 160000000000 : ℝ) ≤ ex (57436 / 100000) 79 * cCG cZ 79 ∧ ex (57436 / 100000) 79 * cCG cZ 79 ≤ (583180581591 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_79 cCB_79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_79 : (-80456808276477 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 79 * sCG cZ 79 ∧ ex (57436 / 100000) 79 * sCG cZ 79 ≤ (-40228392253423 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_79 sCB_79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_79 : (50963439233921 / 1000000000000000 : ℝ) ≤ Real.log 79 * (ex (57436 / 100000) 79 * cCG cZ 79) ∧ Real.log 79 * (ex (57436 / 100000) 79 * cCG cZ 79) ≤ (6370442851589 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_79 eC_79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_81 : (4394449154292799 / 1000000000000000 : ℝ) ≤ Real.log 81 ∧ Real.log 81 ≤ (4394449156078747 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_81
  constructor <;> linarith [h.1, h.2]

theorem eC_81 : (-73616986594799 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 81 * cCG cZ 81 ∧ ex (57436 / 100000) 81 * cCG cZ 81 ≤ (-36808481345167 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_81 cCB_81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_81 : (31666369545857 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 81 * sCG cZ 81 ∧ ex (57436 / 100000) 81 * sCG cZ 81 ≤ (7916598351821 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_81 sCB_81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_81 : (-12940244184583 / 40000000000000 : ℝ) ≤ Real.log 81 * (ex (57436 / 100000) 81 * cCG cZ 81) ∧ Real.log 81 * (ex (57436 / 100000) 81 * cCG cZ 81) ≤ (-161752999718071 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_81 eC_81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_82 : (4406719246881137 / 1000000000000000 : ℝ) ≤ Real.log 82 ∧ Real.log 82 ≤ (4406719248684467 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_82
  constructor <;> linarith [h.1, h.2]

theorem eC_82 : (2611990328341 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 82 * cCG cZ 82 ∧ ex (57436 / 100000) 82 * cCG cZ 82 ≤ (1044800922629 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_82 cCB_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_82 : (1484023429991 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 82 * cCG cZ 82) ∧ kappa * (ex (57436 / 100000) 82 * cCG cZ 82) ≤ (1484030235521 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_82 : (-39702156421409 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 82 * sCG cZ 82 ∧ ex (57436 / 100000) 82 * sCG cZ 82 ≤ (-79404288809517 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_82 sCB_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_82 : (-22557101269193 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 82 * sCG cZ 82) ∧ kappa * (ex (57436 / 100000) 82 * sCG cZ 82) ≤ (-4511418888367 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_82 : (4604123221027 / 200000000000000 : ℝ) ≤ Real.log 82 * (ex (57436 / 100000) 82 * cCG cZ 82) ∧ Real.log 82 * (ex (57436 / 100000) 82 * cCG cZ 82) ≤ (23020721683963 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_82 eC_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_82 : (6539674611763 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 82 * (ex (57436 / 100000) 82 * cCG cZ 82)) ∧ kappa * (Real.log 82 * (ex (57436 / 100000) 82 * cCG cZ 82)) ≤ (6539704604497 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_83 : (4418840607410211 / 1000000000000000 : ℝ) ≤ Real.log 83 ∧ Real.log 83 ≤ (552355076153737 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_83
  constructor <;> linarith [h.1, h.2]

theorem eC_83 : (17214309108803 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 83 * cCG cZ 83 ∧ ex (57436 / 100000) 83 * cCG cZ 83 ≤ (13771452092221 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_83 cCB_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_83 : (2445112236001 / 125000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 83 * cCG cZ 83) ∧ kappa * (ex (57436 / 100000) 83 * cCG cZ 83) ≤ (19560904713261 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_83 : (9693589347511 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 83 * sCG cZ 83 ∧ ex (57436 / 100000) 83 * sCG cZ 83 ≤ (38774381384441 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_83 sCB_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_83 : (1101498237289 / 100000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 83 * sCG cZ 83) ∧ kappa * (ex (57436 / 100000) 83 * sCG cZ 83) ≤ (2753747297299 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_83 : (7606728811849 / 25000000000000 : ℝ) ≤ Real.log 83 * (ex (57436 / 100000) 83 * cCG cZ 83) ∧ Real.log 83 * (ex (57436 / 100000) 83 * cCG cZ 83) ≤ (304269258765851 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_83 eC_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_83 : (17287297980987 / 200000000000000 : ℝ) ≤ kappa * (Real.log 83 * (ex (57436 / 100000) 83 * cCG cZ 83)) ∧ kappa * (Real.log 83 * (ex (57436 / 100000) 83 * cCG cZ 83)) ≤ (17287304020047 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_84 : (4430816798453847 / 1000000000000000 : ℝ) ≤ Real.log 84 ∧ Real.log 84 ≤ (443081680028893 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_84
  constructor <;> linarith [h.1, h.2]

theorem eC_84 : (-15796525262521 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 84 * cCG cZ 84 ∧ ex (57436 / 100000) 84 * cCG cZ 84 ≤ (-63186076981783 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_84 cCB_84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_84 : (9310137542011 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 84 * sCG cZ 84 ∧ ex (57436 / 100000) 84 * sCG cZ 84 ≤ (46550711760153 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_84 sCB_84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_84 : (-279966038077467 / 1000000000000000 : ℝ) ≤ Real.log 84 * (ex (57436 / 100000) 84 * cCG cZ 84) ∧ Real.log 84 * (ex (57436 / 100000) 84 * cCG cZ 84) ≤ (-139982965659641 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_84 eC_84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_86 : (1113586823964601 / 250000000000000 : ℝ) ≤ Real.log 86 ∧ Real.log 86 ≤ (2227173648860837 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_86
  constructor <;> linarith [h.1, h.2]

theorem eC_86 : (191655970863 / 2500000000000 : ℝ) ≤ ex (57436 / 100000) 86 * cCG cZ 86 ∧ ex (57436 / 100000) 86 * cCG cZ 86 ≤ (76662412479397 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_86 cCB_86 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_86 : (84889177181 / 7812500000000 : ℝ) ≤ ex (57436 / 100000) 86 * sCG cZ 86 ∧ ex (57436 / 100000) 86 * sCG cZ 86 ≤ (5432919371473 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_86 sCB_86 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_86 : (10671278194359 / 31250000000000 : ℝ) ≤ Real.log 86 * (ex (57436 / 100000) 86 * cCG cZ 86) ∧ Real.log 86 * (ex (57436 / 100000) 86 * cCG cZ 86) ≤ (341481009864427 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_86 eC_86 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_87 : (2232954059128449 / 500000000000000 : ℝ) ≤ Real.log 87 ∧ Real.log 87 ≤ (178636324805323 / 40000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_87
  constructor <;> linarith [h.1, h.2]

theorem eC_87 : (-14605295953 / 400000000000 : ℝ) ≤ ex (57436 / 100000) 87 * cCG cZ 87 ∧ ex (57436 / 100000) 87 * cCG cZ 87 ≤ (-4564151977217 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_87 cCB_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_87 : (-10372646273337 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 87 * cCG cZ 87) ∧ kappa * (ex (57436 / 100000) 87 * cCG cZ 87) ≤ (-10372639437041 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_87 : (4231061531217 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 87 * sCG cZ 87 ∧ ex (57436 / 100000) 87 * sCG cZ 87 ≤ (541576068783 / 8000000000000 : ℝ) := by
  exact mul_bounds_of exB_87 sCB_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_87 : (19231294627489 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 87 * sCG cZ 87) ∧ kappa * (ex (57436 / 100000) 87 * sCG cZ 87) ≤ (19231301473341 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_87 : (-20383096810453 / 125000000000000 : ℝ) ≤ Real.log 87 * (ex (57436 / 100000) 87 * cCG cZ 87) ∧ Real.log 87 * (ex (57436 / 100000) 87 * cCG cZ 87) ≤ (-163064666944093 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_87 eC_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_87 : (-46323285219361 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 87 * (ex (57436 / 100000) 87 * cCG cZ 87)) ∧ kappa * (Real.log 87 * (ex (57436 / 100000) 87 * cCG cZ 87)) ≤ (-46323254669633 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_88 : (1119334203519521 / 250000000000000 : ℝ) ≤ Real.log 88 ∧ Real.log 88 ≤ (4477336815966447 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_88
  constructor <;> linarith [h.1, h.2]

theorem eC_88 : (-404430902943 / 7812500000000 : ℝ) ≤ ex (57436 / 100000) 88 * cCG cZ 88 ∧ ex (57436 / 100000) 88 * cCG cZ 88 ≤ (-51767131487179 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_88 cCB_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_88 : (-1838245507321 / 125000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 88 * cCG cZ 88) ∧ kappa * (ex (57436 / 100000) 88 * cCG cZ 88) ≤ (-7352978607619 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_88 : (-5620589128829 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 88 * sCG cZ 88 ∧ ex (57436 / 100000) 88 * sCG cZ 88 ≤ (-28102933594801 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_88 sCB_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_88 : (-997932240961 / 62500000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 88 * sCG cZ 88) ∧ kappa * (ex (57436 / 100000) 88 * sCG cZ 88) ≤ (-15966909009443 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_88 : (-1448618697009 / 6250000000000 : ℝ) ≤ Real.log 88 * (ex (57436 / 100000) 88 * cCG cZ 88) ∧ Real.log 88 * (ex (57436 / 100000) 88 * cCG cZ 88) ≤ (-231778883566767 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_88 eC_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_88 : (-32921777146853 / 500000000000000 : ℝ) ≤ kappa * (Real.log 88 * (ex (57436 / 100000) 88 * cCG cZ 88)) ∧ kappa * (Real.log 88 * (ex (57436 / 100000) 88 * cCG cZ 88)) ≤ (-13168704725209 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_89 : (897727273865943 / 200000000000000 : ℝ) ≤ Real.log 89 ∧ Real.log 89 ≤ (448863637122959 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_89
  constructor <;> linarith [h.1, h.2]

theorem eC_89 : (34440684324813 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 89 * cCG cZ 89 ∧ ex (57436 / 100000) 89 * cCG cZ 89 ≤ (68881392784119 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_89 cCB_89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_89 : (-31921691093999 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 89 * sCG cZ 89 ∧ ex (57436 / 100000) 89 * sCG cZ 89 ≤ (-31921666999847 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_89 sCB_89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_89 : (154591708244959 / 500000000000000 : ℝ) ≤ Real.log 89 * (ex (57436 / 100000) 89 * cCG cZ 89) ∧ Real.log 89 * (ex (57436 / 100000) 89 * cCG cZ 89) ≤ (77295881237937 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_89 eC_89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_91 : (4510859506110189 / 1000000000000000 : ℝ) ≤ Real.log 91 ∧ Real.log 91 ≤ (1127714877007811 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_91
  constructor <;> linarith [h.1, h.2]

theorem eC_91 : (-14875800478103 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 91 * cCG cZ 91 ∧ ex (57436 / 100000) 91 * cCG cZ 91 ≤ (-1859474457989 / 25000000000000 : ℝ) := by
  exact mul_bounds_of exB_91 cCB_91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_91 : (-4640347394639 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 91 * sCG cZ 91 ∧ ex (57436 / 100000) 91 * sCG cZ 91 ≤ (-2320167697539 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_91 sCB_91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_91 : (-167756615065567 / 500000000000000 : ℝ) ≤ Real.log 91 * (ex (57436 / 100000) 91 * cCG cZ 91) ∧ Real.log 91 * (ex (57436 / 100000) 91 * cCG cZ 91) ≤ (-6710262428151 / 20000000000000 : ℝ) := by
  exact mul_bounds_of lgB_91 eC_91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_92 : (452178857664043 / 100000000000000 : ℝ) ≤ Real.log 92 ∧ Real.log 92 ≤ (452178857857123 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_92
  constructor <;> linarith [h.1, h.2]

theorem eC_92 : (27130003723263 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 92 * cCG cZ 92 ∧ ex (57436 / 100000) 92 * cCG cZ 92 ≤ (27130027704469 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_92 cCB_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_92 : (7707065517091 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 92 * cCG cZ 92) ∧ kappa * (ex (57436 / 100000) 92 * cCG cZ 92) ≤ (154141446593 / 20000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_92 : (-17342568063197 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 92 * sCG cZ 92 ∧ ex (57436 / 100000) 92 * sCG cZ 92 ≤ (-34685124112367 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_92 sCB_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_92 : (-9853320306261 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 92 * sCG cZ 92) ∧ kappa * (ex (57436 / 100000) 92 * sCG cZ 92) ≤ (-9853316893327 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_92 : (61338070460031 / 500000000000000 : ℝ) ≤ Real.log 92 * (ex (57436 / 100000) 92 * cCG cZ 92) ∧ Real.log 92 * (ex (57436 / 100000) 92 * cCG cZ 92) ≤ (122676249410389 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_92 eC_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_92 : (17424860407301 / 500000000000000 : ℝ) ≤ kappa * (Real.log 92 * (ex (57436 / 100000) 92 * cCG cZ 92)) ∧ kappa * (Real.log 92 * (ex (57436 / 100000) 92 * cCG cZ 92)) ≤ (68065921161 / 1953125000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_93 : (11331498731857 / 2500000000000 : ℝ) ≤ Real.log 93 ∧ Real.log 93 ≤ (453259949468283 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_93
  constructor <;> linarith [h.1, h.2]

theorem eC_93 : (61020671403117 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 93 * cCG cZ 93 ∧ ex (57436 / 100000) 93 * cCG cZ 93 ≤ (6102069539591 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_93 cCB_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_93 : (17334693986697 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 93 * cCG cZ 93) ∧ kappa * (ex (57436 / 100000) 93 * cCG cZ 93) ≤ (4333675200637 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_93 : (10476967681483 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 93 * sCG cZ 93 ∧ ex (57436 / 100000) 93 * sCG cZ 93 ≤ (20953947348547 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_93 sCB_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_93 : (1190514784521 / 100000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 93 * sCG cZ 93) ∧ kappa * (ex (57436 / 100000) 93 * sCG cZ 93) ≤ (2976288663729 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_93 : (276582264248593 / 1000000000000000 : ℝ) ≤ Real.log 93 * (ex (57436 / 100000) 93 * cCG cZ 93) ∧ Real.log 93 * (ex (57436 / 100000) 93 * cCG cZ 93) ≤ (276582373116697 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_93 eC_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_93 : (19642806292739 / 250000000000000 : ℝ) ≤ kappa * (Real.log 93 * (ex (57436 / 100000) 93 * cCG cZ 93)) ∧ kappa * (Real.log 93 * (ex (57436 / 100000) 93 * cCG cZ 93)) ≤ (9821407012263 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_94 : (4543294781857799 / 1000000000000000 : ℝ) ≤ Real.log 94 ∧ Real.log 94 ≤ (181731791352263 / 40000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_94
  constructor <;> linarith [h.1, h.2]

theorem eC_94 : (-26682955652901 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 94 * cCG cZ 94 ∧ ex (57436 / 100000) 94 * cCG cZ 94 ≤ (-53365887318031 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_94 cCB_94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_94 : (2025818047731 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 94 * sCG cZ 94 ∧ ex (57436 / 100000) 94 * sCG cZ 94 ≤ (50645475172693 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_94 sCB_94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_94 : (-48491413293747 / 200000000000000 : ℝ) ≤ Real.log 94 * (ex (57436 / 100000) 94 * cCG cZ 94) ∧ Real.log 94 * (ex (57436 / 100000) 94 * cCG cZ 94) ≤ (-242456957381221 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_94 eC_94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_96 : (4564348191052399 / 1000000000000000 : ℝ) ≤ Real.log 96 ∧ Real.log 96 ≤ (570543524127167 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_96
  constructor <;> linarith [h.1, h.2]

theorem eC_96 : (8383248786223 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 96 * cCG cZ 96 ∧ ex (57436 / 100000) 96 * cCG cZ 96 ≤ (67066014145847 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_96 cCB_96 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_96 : (-1751892669801 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 96 * sCG cZ 96 ∧ ex (57436 / 100000) 96 * sCG cZ 96 ≤ (-5606051780963 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_96 sCB_96 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_96 : (306112531460313 / 1000000000000000 : ℝ) ≤ Real.log 96 * (ex (57436 / 100000) 96 * cCG cZ 96) ∧ Real.log 96 * (ex (57436 / 100000) 96 * cCG cZ 96) ≤ (19132040029967 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_96 eC_96 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_97 : (1143677744521613 / 250000000000000 : ℝ) ≤ Real.log 97 ∧ Real.log 97 ≤ (2287355490029429 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_97
  constructor <;> linarith [h.1, h.2]

theorem eC_97 : (17280227345591 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 97 * cCG cZ 97 ∧ ex (57436 / 100000) 97 * cCG cZ 97 ≤ (17280251103959 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_97 cCB_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_97 : (61361880771 / 12500000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 97 * cCG cZ 97) ∧ kappa * (ex (57436 / 100000) 97 * cCG cZ 97) ≤ (981791442187 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_97 : (2806396767757 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 97 * sCG cZ 97 ∧ ex (57436 / 100000) 97 * sCG cZ 97 ≤ (14031988602441 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_97 sCB_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_97 : (1993096276053 / 100000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 97 * sCG cZ 97) ∧ kappa * (ex (57436 / 100000) 97 * sCG cZ 97) ≤ (9965484763403 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_97 : (9881505717713 / 125000000000000 : ℝ) ≤ Real.log 97 * (ex (57436 / 100000) 97 * cCG cZ 97) ∧ Real.log 97 * (ex (57436 / 100000) 97 * cCG cZ 97) ≤ (2470379826983 / 31250000000000 : ℝ) := by
  exact mul_bounds_of lgB_97 eC_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_97 : (22457029567931 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 97 * (ex (57436 / 100000) 97 * cCG cZ 97)) ∧ kappa * (Real.log 97 * (ex (57436 / 100000) 97 * cCG cZ 97)) ≤ (175445784793 / 7812500000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_98 : (2292483739126111 / 500000000000000 : ℝ) ≤ Real.log 98 ∧ Real.log 98 ≤ (2292483740115861 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_98
  constructor <;> linarith [h.1, h.2]

theorem eC_98 : (-71438197880047 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 98 * cCG cZ 98 ∧ ex (57436 / 100000) 98 * cCG cZ 98 ≤ (-17859543520101 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_98 cCB_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_98 : (-10147047473723 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 98 * cCG cZ 98) ∧ kappa * (ex (57436 / 100000) 98 * cCG cZ 98) ≤ (-10147044093233 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_98 : (7513698686697 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 98 * sCG cZ 98 ∧ ex (57436 / 100000) 98 * sCG cZ 98 ≤ (7513722413657 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_98 sCB_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_98 : (2134484338621 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 98 * sCG cZ 98) ∧ kappa * (ex (57436 / 100000) 98 * sCG cZ 98) ≤ (1067245539477 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_98 : (-2620334513011 / 8000000000000 : ℝ) ≤ Real.log 98 * (ex (57436 / 100000) 98 * cCG cZ 98) ∧ Real.log 98 * (ex (57436 / 100000) 98 * cCG cZ 98) ≤ (-327541704864373 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_98 eC_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_98 : (-3721910614991 / 40000000000000 : ℝ) ≤ kappa * (Real.log 98 * (ex (57436 / 100000) 98 * cCG cZ 98)) ∧ kappa * (Real.log 98 * (ex (57436 / 100000) 98 * cCG cZ 98)) ≤ (-93047734335729 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_99 : (1148779962428723 / 250000000000000 : ℝ) ≤ Real.log 99 ∧ Real.log 99 ≤ (4595119851701133 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_99
  constructor <;> linarith [h.1, h.2]

theorem eC_99 : (130066355041 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 99 * cCG cZ 99 ∧ ex (57436 / 100000) 99 * cCG cZ 99 ≤ (208110892869 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_99 cCB_99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_99 : (-71407024528407 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 99 * sCG cZ 99 ∧ ex (57436 / 100000) 99 * sCG cZ 99 ≤ (-17851750206027 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_99 sCB_99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_99 : (4781363918631 / 1000000000000000 : ℝ) ≤ Real.log 99 * (ex (57436 / 100000) 99 * cCG cZ 99) ∧ Real.log 99 * (ex (57436 / 100000) 99 * cCG cZ 99) ≤ (298842029743 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_99 eC_99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_101 : (4615120516419061 / 1000000000000000 : ℝ) ≤ Real.log 101 ∧ Real.log 101 ≤ (2307560259208903 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_101
  constructor <;> linarith [h.1, h.2]

theorem eC_101 : (-1421092136493 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 101 * cCG cZ 101 ∧ ex (57436 / 100000) 101 * cCG cZ 101 ≤ (-14210897851109 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_101 cCB_101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_101 : (2766153732663 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 101 * sCG cZ 101 ∧ ex (57436 / 100000) 101 * sCG cZ 101 ≤ (17288466723369 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_101 sCB_101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_101 : (-65585114776911 / 1000000000000000 : ℝ) ≤ Real.log 101 * (ex (57436 / 100000) 101 * cCG cZ 101) ∧ Real.log 101 * (ex (57436 / 100000) 101 * cCG cZ 101) ≤ (-16396251557347 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_101 eC_101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_102 : (289060800803807 / 62500000000000 : ℝ) ≤ Real.log 102 ∧ Real.log 102 ≤ (4624972814865459 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_102
  constructor <;> linarith [h.1, h.2]

theorem eC_102 : (-67618097258187 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 102 * cCG cZ 102 ∧ ex (57436 / 100000) 102 * cCG cZ 102 ≤ (-33016637561 / 488281250000 : ℝ) := by
  exact mul_bounds_of exB_102 cCB_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_102 : (-9604442207707 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 102 * cCG cZ 102) ∧ kappa * (ex (57436 / 100000) 102 * cCG cZ 102) ≤ (-4802219432527 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_102 : (-4716392241733 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 102 * sCG cZ 102 ∧ ex (57436 / 100000) 102 * sCG cZ 102 ≤ (-18865545489809 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_102 sCB_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_102 : (-167478524801 / 31250000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 102 * sCG cZ 102) ∧ kappa * (ex (57436 / 100000) 102 * sCG cZ 102) ≤ (-334956632767 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_102 : (-78182965403011 / 250000000000000 : ℝ) ≤ Real.log 102 * (ex (57436 / 100000) 102 * cCG cZ 102) ∧ Real.log 102 * (ex (57436 / 100000) 102 * cCG cZ 102) ≤ (-39091469079477 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_102 eC_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_102 : (-44420284112591 / 500000000000000 : ℝ) ≤ kappa * (Real.log 102 * (ex (57436 / 100000) 102 * cCG cZ 102)) ∧ kappa * (Real.log 102 * (ex (57436 / 100000) 102 * cCG cZ 102)) ≤ (-44420268633659 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_103 : (1158682246951293 / 250000000000000 : ℝ) ≤ Real.log 103 ∧ Real.log 103 ≤ (4634728989815243 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_103
  constructor <;> linarith [h.1, h.2]

theorem eC_103 : (22322635429827 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 103 * cCG cZ 103 ∧ ex (57436 / 100000) 103 * cCG cZ 103 ≤ (22322658840081 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_103 cCB_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_103 : (6341392928903 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 103 * cCG cZ 103) ∧ kappa * (ex (57436 / 100000) 103 * cCG cZ 103) ≤ (3170699789633 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_103 : (-1033484097879 / 15625000000000 : ℝ) ≤ ex (57436 / 100000) 103 * sCG cZ 103 ∧ ex (57436 / 100000) 103 * sCG cZ 103 ≤ (-66142958803407 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_103 sCB_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_103 : (-1174364697399 / 62500000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 103 * sCG cZ 103) ∧ kappa * (ex (57436 / 100000) 103 * sCG cZ 103) ≤ (-18789828493647 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_103 : (4138374620433 / 40000000000000 : ℝ) ≤ Real.log 103 * (ex (57436 / 100000) 103 * cCG cZ 103) ∧ Real.log 103 * (ex (57436 / 100000) 103 * cCG cZ 103) ≤ (103459474055879 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_103 eC_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_103 : (587812752613 / 20000000000000 : ℝ) ≤ kappa * (Real.log 103 * (ex (57436 / 100000) 103 * cCG cZ 103)) ∧ kappa * (Real.log 103 * (ex (57436 / 100000) 103 * cCG cZ 103)) ≤ (29390668466027 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_104 : (290274431169741 / 62500000000000 : ℝ) ≤ Real.log 104 ∧ Real.log 104 ≤ (464439090073119 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_104
  constructor <;> linarith [h.1, h.2]

theorem eC_104 : (32446589724879 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 104 * cCG cZ 104 ∧ ex (57436 / 100000) 104 * cCG cZ 104 ≤ (32446601419623 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_104 cCB_104 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_104 : (24663304571859 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 104 * sCG cZ 104 ∧ ex (57436 / 100000) 104 * sCG cZ 104 ≤ (12331663957387 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_104 sCB_104 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_104 : (30138929202519 / 100000000000000 : ℝ) ≤ Real.log 104 * (ex (57436 / 100000) 104 * cCG cZ 104) ∧ Real.log 104 * (ex (57436 / 100000) 104 * cCG cZ 104) ≤ (150694700392949 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_104 eC_104 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_106 : (4663439093684591 / 1000000000000000 : ℝ) ≤ Real.log 106 ∧ Real.log 106 ≤ (4663439095709723 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_106
  constructor <;> linarith [h.1, h.2]

theorem eC_106 : (-31719320990487 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 106 * cCG cZ 106 ∧ ex (57436 / 100000) 106 * cCG cZ 106 ≤ (-63438618692001 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_106 cCB_106 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_106 : (-13139995722883 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 106 * sCG cZ 106 ∧ ex (57436 / 100000) 106 * sCG cZ 106 ≤ (-26279968200021 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_106 sCB_106 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_106 : (-295842243192807 / 1000000000000000 : ℝ) ≤ Real.log 106 * (ex (57436 / 100000) 106 * cCG cZ 106) ∧ Real.log 106 * (ex (57436 / 100000) 106 * cCG cZ 106) ≤ (-295842134457627 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_106 eC_106 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_107 : (2336414417016759 / 500000000000000 : ℝ) ≤ Real.log 107 ∧ Real.log 107 ≤ (4672828836063211 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_107
  constructor <;> linarith [h.1, h.2]

theorem eC_107 : (5131680520857 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 107 * cCG cZ 107 ∧ ex (57436 / 100000) 107 * cCG cZ 107 ≤ (25658425777763 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_107 cCB_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_107 : (7289014478297 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 107 * cCG cZ 107) ∧ kappa * (ex (57436 / 100000) 107 * cCG cZ 107) ≤ (3644510530699 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_107 : (-1582355800767 / 25000000000000 : ℝ) ≤ ex (57436 / 100000) 107 * sCG cZ 107 ∧ ex (57436 / 100000) 107 * sCG cZ 107 ≤ (-31647104406661 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_107 sCB_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_107 : (-17980564915889 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 107 * sCG cZ 107) ∧ kappa * (ex (57436 / 100000) 107 * sCG cZ 107) ≤ (-17980558320323 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_107 : (119897323524543 / 1000000000000000 : ℝ) ≤ Real.log 107 * (ex (57436 / 100000) 107 * cCG cZ 107) ∧ Real.log 107 * (ex (57436 / 100000) 107 * cCG cZ 107) ≤ (119897431862319 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_107 eC_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_107 : (8515079256469 / 250000000000000 : ℝ) ≤ kappa * (Real.log 107 * (ex (57436 / 100000) 107 * cCG cZ 107)) ∧ kappa * (Real.log 107 * (ex (57436 / 100000) 107 * cCG cZ 107)) ≤ (34060347802369 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_108 : (58526640333687 / 12500000000000 : ℝ) ≤ Real.log 108 ∧ Real.log 108 ≤ (292633201795563 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_108
  constructor <;> linarith [h.1, h.2]

theorem eC_108 : (12701303824167 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 108 * cCG cZ 108 ∧ ex (57436 / 100000) 108 * cCG cZ 108 ≤ (31753271121591 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_108 cCB_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_108 : (18040871229479 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 108 * cCG cZ 108) ∧ kappa * (ex (57436 / 100000) 108 * cCG cZ 108) ≤ (9020438899027 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_108 : (12060821632223 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 108 * sCG cZ 108 ∧ ex (57436 / 100000) 108 * sCG cZ 108 ≤ (964866653631 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_108 sCB_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_108 : (6852453354423 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 108 * sCG cZ 108) ∧ kappa * (ex (57436 / 100000) 108 * sCG cZ 108) ≤ (274098396397 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_108 : (148672928137181 / 500000000000000 : ℝ) ≤ Real.log 108 * (ex (57436 / 100000) 108 * cCG cZ 108) ∧ Real.log 108 * (ex (57436 / 100000) 108 * cCG cZ 108) ≤ (297345964665401 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_108 eC_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_108 : (84469726540329 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 108 * (ex (57436 / 100000) 108 * cCG cZ 108)) ∧ kappa * (Real.log 108 * (ex (57436 / 100000) 108 * cCG cZ 108)) ≤ (84469757331953 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_109 : (4691347881799053 / 1000000000000000 : ℝ) ≤ Real.log 109 ∧ Real.log 109 ≤ (4691347883837257 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_109
  constructor <;> linarith [h.1, h.2]

theorem eC_109 : (-5419649918641 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 109 * cCG cZ 109 ∧ ex (57436 / 100000) 109 * cCG cZ 109 ≤ (-21678576657181 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_109 cCB_109 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_109 : (12800576238547 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 109 * sCG cZ 109 ∧ ex (57436 / 100000) 109 * sCG cZ 109 ≤ (8000363032459 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_109 sCB_109 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_109 : (-101701852707821 / 1000000000000000 : ℝ) ≤ Real.log 109 * (ex (57436 / 100000) 109 * cCG cZ 109) ∧ Real.log 109 * (ex (57436 / 100000) 109 * cCG cZ 109) ≤ (-25425436170271 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_109 eC_109 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_111 : (4709530200880691 / 1000000000000000 : ℝ) ≤ Real.log 111 ∧ Real.log 111 ≤ (4709530202926659 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_111
  constructor <;> linarith [h.1, h.2]

theorem eC_111 : (14069153828959 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 111 * cCG cZ 111 ∧ ex (57436 / 100000) 111 * cCG cZ 111 ≤ (2813835336141 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_111 cCB_111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_111 : (-65375885968551 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 111 * sCG cZ 111 ∧ ex (57436 / 100000) 111 * sCG cZ 111 ≤ (-65375863056507 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_111 sCB_111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_111 : (33129552429159 / 500000000000000 : ℝ) ≤ Real.log 111 * (ex (57436 / 100000) 111 * cCG cZ 111) ∧ Real.log 111 * (ex (57436 / 100000) 111 * cCG cZ 111) ≤ (16564803127023 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_111 eC_111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_112 : (2359249435431363 / 500000000000000 : ℝ) ≤ Real.log 112 ∧ Real.log 112 ≤ (4718498872912321 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_112
  constructor <;> linarith [h.1, h.2]

theorem eC_112 : (32965088307877 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 112 * cCG cZ 112 ∧ ex (57436 / 100000) 112 * cCG cZ 112 ≤ (65930199416023 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_112 cCB_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_112 : (1170586345827 / 62500000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 112 * cCG cZ 112) ∧ kappa * (ex (57436 / 100000) 112 * cCG cZ 112) ≤ (2341173501289 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_112 : (4453111712653 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 112 * sCG cZ 112 ∧ ex (57436 / 100000) 112 * sCG cZ 112 ≤ (4453123079219 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_112 sCB_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_112 : (253007143489 / 100000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 112 * sCG cZ 112) ∧ kappa * (ex (57436 / 100000) 112 * sCG cZ 112) ≤ (2530077892897 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_112 : (62218292783443 / 200000000000000 : ℝ) ≤ Real.log 112 * (ex (57436 / 100000) 112 * cCG cZ 112) ∧ Real.log 112 * (ex (57436 / 100000) 112 * cCG cZ 112) ≤ (31109157163539 / 100000000000000 : ℝ) := by
  exact mul_bounds_of lgB_112 eC_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_112 : (22093641404129 / 250000000000000 : ℝ) ≤ kappa * (Real.log 112 * (ex (57436 / 100000) 112 * cCG cZ 112)) ∧ kappa * (Real.log 112 * (ex (57436 / 100000) 112 * cCG cZ 112)) ≤ (88374596216993 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_113 : (2363693909139639 / 500000000000000 : ℝ) ≤ Real.log 113 ∧ Real.log 113 ≤ (4727387820332341 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_113
  constructor <;> linarith [h.1, h.2]

theorem eC_113 : (-2865320320271 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 113 * cCG cZ 113 ∧ ex (57436 / 100000) 113 * cCG cZ 113 ≤ (-286529766807 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_113 cCB_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_113 : (-10174718211 / 12500000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 113 * cCG cZ 113) ∧ kappa * (ex (57436 / 100000) 113 * cCG cZ 113) ≤ (-813971021863 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_113 : (33064083768263 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 113 * sCG cZ 113 ∧ ex (57436 / 100000) 113 * sCG cZ 113 ≤ (8266023782917 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_113 sCB_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_113 : (9392813302347 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 113 * sCG cZ 113) ∧ kappa * (ex (57436 / 100000) 113 * sCG cZ 113) ≤ (9392816530453 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_113 : (-67727401917 / 5000000000000 : ℝ) ≤ Real.log 113 * (ex (57436 / 100000) 113 * cCG cZ 113) ∧ Real.log 113 * (ex (57436 / 100000) 113 * cCG cZ 113) ≤ (-6772686645889 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_113 eC_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_113 : (-961996778919 / 250000000000000 : ℝ) ≤ kappa * (Real.log 113 * (ex (57436 / 100000) 113 * cCG cZ 113)) ∧ kappa * (Real.log 113 * (ex (57436 / 100000) 113 * cCG cZ 113)) ≤ (-3847956693189 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_114 : (4736198447960769 / 1000000000000000 : ℝ) ≤ Real.log 114 ∧ Real.log 114 ≤ (4736198450017151 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_114
  constructor <;> linarith [h.1, h.2]

theorem eC_114 : (-65734818925461 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 114 * cCG cZ 114 ∧ ex (57436 / 100000) 114 * cCG cZ 114 ≤ (-65734796264667 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_114 cCB_114 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_114 : (3995410958589 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 114 * sCG cZ 114 ∧ ex (57436 / 100000) 114 * sCG cZ 114 ≤ (1997716773227 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_114 sCB_114 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_114 : (-311333147506927 / 1000000000000000 : ℝ) ≤ Real.log 114 * (ex (57436 / 100000) 114 * cCG cZ 114) ∧ Real.log 114 * (ex (57436 / 100000) 114 * cCG cZ 114) ≤ (-311333040045733 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_114 eC_114 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_116 : (950718038134279 / 200000000000000 : ℝ) ≤ Real.log 116 ∧ Real.log 116 ≤ (4753590192733993 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_116
  constructor <;> linarith [h.1, h.2]

theorem eC_116 : (62154312295443 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 116 * cCG cZ 116 ∧ ex (57436 / 100000) 116 * cCG cZ 116 ≤ (15538583695871 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_116 cCB_116 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_116 : (-393996150071 / 20000000000000 : ℝ) ≤ ex (57436 / 100000) 116 * sCG cZ 116 ∧ ex (57436 / 100000) 116 * sCG cZ 116 ≤ (-19699785065809 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_116 sCB_116 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_116 : (36932016154443 / 125000000000000 : ℝ) ≤ Real.log 116 * (ex (57436 / 100000) 116 * cCG cZ 116) ∧ Real.log 116 * (ex (57436 / 100000) 116 * cCG cZ 116) ≤ (11818249450507 / 40000000000000 : ℝ) := by
  exact mul_bounds_of lgB_116 eC_116 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_117 : (1190543483590551 / 250000000000000 : ℝ) ≤ Real.log 117 ∧ Real.log 117 ≤ (952434787285543 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_117
  constructor <;> linarith [h.1, h.2]

theorem eC_117 : (28145793826371 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 117 * cCG cZ 117 ∧ ex (57436 / 100000) 117 * cCG cZ 117 ≤ (14072908092441 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_117 cCB_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_117 : (1998907549581 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 117 * cCG cZ 117) ∧ kappa * (ex (57436 / 100000) 117 * cCG cZ 117) ≤ (799563654991 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_117 : (29229016619501 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 117 * sCG cZ 117 ∧ ex (57436 / 100000) 117 * sCG cZ 117 ≤ (29229027816743 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_117 sCB_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_117 : (8303351093663 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 117 * sCG cZ 117) ∧ kappa * (ex (57436 / 100000) 117 * sCG cZ 117) ≤ (16606708549131 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_117 : (33508791430469 / 250000000000000 : ℝ) ≤ Real.log 117 * (ex (57436 / 100000) 117 * cCG cZ 117) ∧ Real.log 117 * (ex (57436 / 100000) 117 * cCG cZ 117) ≤ (134035272255131 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_117 eC_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_117 : (38076581719261 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 117 * (ex (57436 / 100000) 117 * cCG cZ 117)) ∧ kappa * (Real.log 117 * (ex (57436 / 100000) 117 * cCG cZ 117)) ≤ (4759576497891 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_118 : (954136924805911 / 200000000000000 : ℝ) ≤ Real.log 118 ∧ Real.log 118 ≤ (74541947282779 / 15625000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_118
  constructor <;> linarith [h.1, h.2]

theorem eC_118 : (-53190357513381 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 118 * cCG cZ 118 ∧ ex (57436 / 100000) 118 * cCG cZ 118 ≤ (-13297583804501 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_118 cCB_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_118 : (-3777566475983 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 118 * cCG cZ 118) ∧ kappa * (ex (57436 / 100000) 118 * cCG cZ 118) ≤ (-15110259570281 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_118 : (457466189379 / 12500000000000 : ℝ) ≤ ex (57436 / 100000) 118 * sCG cZ 118 ∧ ex (57436 / 100000) 118 * sCG cZ 118 ≤ (4574664678211 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_118 sCB_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_118 : (1299565576681 / 125000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 118 * sCG cZ 118) ∧ kappa * (ex (57436 / 100000) 118 * sCG cZ 118) ≤ (5198265470707 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_118 : (-31719302605717 / 125000000000000 : ℝ) ≤ Real.log 118 * (ex (57436 / 100000) 118 * cCG cZ 118) ∧ Real.log 118 * (ex (57436 / 100000) 118 * cCG cZ 118) ≤ (-253754314371509 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_118 eC_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_118 : (-14417262648827 / 200000000000000 : ℝ) ≤ kappa * (Real.log 118 * (ex (57436 / 100000) 118 * cCG cZ 118)) ∧ kappa * (Real.log 118 * (ex (57436 / 100000) 118 * cCG cZ 118)) ≤ (-72086282997037 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_119 : (955824698534977 / 200000000000000 : ℝ) ≤ Real.log 119 ∧ Real.log 119 ≤ (238956174737293 / 50000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_119
  constructor <;> linarith [h.1, h.2]

theorem eC_119 : (-4466166623933 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 119 * cCG cZ 119 ∧ ex (57436 / 100000) 119 * cCG cZ 119 ≤ (-22330821996061 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_119 cCB_119 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_119 : (-11547994554471 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 119 * sCG cZ 119 ∧ ex (57436 / 100000) 119 * sCG cZ 119 ≤ (-9238391192699 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_119 sCB_119 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_119 : (-1334022615243 / 6250000000000 : ℝ) ≤ Real.log 119 * (ex (57436 / 100000) 119 * cCG cZ 119) ∧ Real.log 119 * (ex (57436 / 100000) 119 * cCG cZ 119) ≤ (-26680439003029 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_119 eC_119 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_121 : (4795790545159091 / 1000000000000000 : ℝ) ≤ Real.log 121 ∧ Real.log 121 ≤ (1198947636808773 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_121
  constructor <;> linarith [h.1, h.2]

theorem eC_121 : (28851757033703 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 121 * cCG cZ 121 ∧ ex (57436 / 100000) 121 * cCG cZ 121 ≤ (7212942022617 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_121 cCB_121 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_121 : (6709950712293 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 121 * sCG cZ 121 ∧ ex (57436 / 100000) 121 * sCG cZ 121 ≤ (2683982492589 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_121 sCB_121 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_121 : (6918349179673 / 25000000000000 : ℝ) ≤ Real.log 121 * (ex (57436 / 100000) 121 * cCG cZ 121) ∧ Real.log 121 * (ex (57436 / 100000) 121 * cCG cZ 121) ≤ (276734073358571 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_121 eC_121 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_122 : (4804021044295607 / 1000000000000000 : ℝ) ≤ Real.log 122 ∧ Real.log 122 ≤ (4804021046371607 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_122
  constructor <;> linarith [h.1, h.2]

theorem eC_122 : (-14734652432563 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 122 * cCG cZ 122 ∧ ex (57436 / 100000) 122 * cCG cZ 122 ≤ (-14734630522043 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_122 cCB_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_122 : (-1046451493591 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 122 * cCG cZ 122) ∧ kappa * (ex (57436 / 100000) 122 * cCG cZ 122) ≤ (-4185799750043 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_122 : (2464094247071 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 122 * sCG cZ 122 ∧ ex (57436 / 100000) 122 * sCG cZ 122 ≤ (30801189071593 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_122 sCB_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_122 : (8749969220507 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 122 * sCG cZ 122) ∧ kappa * (ex (57436 / 100000) 122 * sCG cZ 122) ≤ (4374986170303 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_122 : (-17696395099251 / 250000000000000 : ℝ) ≤ Real.log 122 * (ex (57436 / 100000) 122 * cCG cZ 122) ∧ Real.log 122 * (ex (57436 / 100000) 122 * cCG cZ 122) ≤ (-35392737553907 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_122 eC_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_122 : (-2010869999687 / 100000000000000 : ℝ) ≤ kappa * (Real.log 122 * (ex (57436 / 100000) 122 * cCG cZ 122)) ∧ kappa * (Real.log 122 * (ex (57436 / 100000) 122 * cCG cZ 122)) ≤ (-20108670086417 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_123 : (300761522183423 / 62500000000000 : ℝ) ≤ Real.log 123 ∧ Real.log 123 ≤ (300761522313173 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_123
  constructor <;> linarith [h.1, h.2]

theorem eC_123 : (-12605417810159 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 123 * cCG cZ 123 ∧ ex (57436 / 100000) 123 * cCG cZ 123 ≤ (-63027067154677 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_123 cCB_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_123 : (-3580935038719 / 200000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 123 * cCG cZ 123) ∧ kappa * (ex (57436 / 100000) 123 * cCG cZ 123) ≤ (-8952334486683 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_123 : (-3625434453 / 2500000000000 : ℝ) ≤ ex (57436 / 100000) 123 * sCG cZ 123 ∧ ex (57436 / 100000) 123 * sCG cZ 123 ≤ (-725075979257 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_123 sCB_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_123 : (-205981990583 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 123 * sCG cZ 123) ∧ kappa * (ex (57436 / 100000) 123 * sCG cZ 123) ≤ (-411957781797 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_123 : (-303297971998161 / 1000000000000000 : ℝ) ≤ Real.log 123 * (ex (57436 / 100000) 123 * cCG cZ 123) ∧ Real.log 123 * (ex (57436 / 100000) 123 * cCG cZ 123) ≤ (-303297866499159 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_123 eC_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_123 : (-43080298941987 / 500000000000000 : ℝ) ≤ kappa * (Real.log 123 * (ex (57436 / 100000) 123 * cCG cZ 123)) ∧ kappa * (Real.log 123 * (ex (57436 / 100000) 123 * cCG cZ 123)) ≤ (-43080283956959 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_124 : (4820281565167387 / 1000000000000000 : ℝ) ≤ Real.log 124 ∧ Real.log 124 ≤ (1205070391810847 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_124
  constructor <;> linarith [h.1, h.2]

theorem eC_124 : (-6226424520337 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 124 * cCG cZ 124 ∧ ex (57436 / 100000) 124 * cCG cZ 124 ≤ (-6226413644049 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_124 cCB_124 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_124 : (-61503223012429 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 124 * sCG cZ 124 ∧ ex (57436 / 100000) 124 * sCG cZ 124 ≤ (-61503201201359 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_124 sCB_124 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_124 : (-30013119345213 / 500000000000000 : ℝ) ≤ Real.log 124 * (ex (57436 / 100000) 124 * cCG cZ 124) ∧ Real.log 124 * (ex (57436 / 100000) 124 * cCG cZ 124) ≤ (-7503266726379 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_124 eC_124 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_126 : (1209070476628457 / 250000000000000 : ℝ) ≤ Real.log 126 ∧ Real.log 126 ≤ (4836281908589829 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_126
  constructor <;> linarith [h.1, h.2]

theorem eC_126 : (7796481209219 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 126 * cCG cZ 126 ∧ ex (57436 / 100000) 126 * cCG cZ 126 ≤ (2436401724403 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_126 cCB_126 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_126 : (4843939061017 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 126 * sCG cZ 126 ∧ ex (57436 / 100000) 126 * sCG cZ 126 ≤ (9687882433391 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_126 sCB_126 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_126 : (11783119064569 / 62500000000000 : ℝ) ≤ Real.log 126 * (ex (57436 / 100000) 126 * cCG cZ 126) ∧ Real.log 126 * (ex (57436 / 100000) 126 * cCG cZ 126) ≤ (188530009308597 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_126 eC_126 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_127 : (4844187086020941 / 1000000000000000 : ℝ) ≤ Real.log 127 ∧ Real.log 127 ≤ (2422093544048471 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_127
  constructor <;> linarith [h.1, h.2]

theorem eC_127 : (-7376932454563 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 127 * cCG cZ 127 ∧ ex (57436 / 100000) 127 * cCG cZ 127 ≤ (-18442320399979 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_127 cCB_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_127 : (-5239079795419 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 127 * cCG cZ 127) ∧ kappa * (ex (57436 / 100000) 127 * cCG cZ 127) ≤ (-10478153490849 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_127 : (49704911213899 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 127 * sCG cZ 127 ∧ ex (57436 / 100000) 127 * sCG cZ 127 ≤ (3106558293913 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_127 sCB_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_127 : (14120123651817 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 127 * sCG cZ 127) ∧ kappa * (ex (57436 / 100000) 127 * sCG cZ 127) ≤ (14120129756309 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_127 : (-178676204730787 / 1000000000000000 : ℝ) ≤ Real.log 127 * (ex (57436 / 100000) 127 * cCG cZ 127) ∧ Real.log 127 * (ex (57436 / 100000) 127 * cCG cZ 127) ≤ (-178676100635677 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_127 eC_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_127 : (-12689541349239 / 250000000000000 : ℝ) ≤ kappa * (Real.log 127 * (ex (57436 / 100000) 127 * cCG cZ 127)) ∧ kappa * (Real.log 127 * (ex (57436 / 100000) 127 * cCG cZ 127)) ≤ (-12689533956429 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_128 : (4852030263481967 / 1000000000000000 : ℝ) ≤ Real.log 128 ∧ Real.log 128 ≤ (303251891597373 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_128
  constructor <;> linarith [h.1, h.2]

theorem eC_128 : (-57372824067869 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 128 * cCG cZ 128 ∧ ex (57436 / 100000) 128 * cCG cZ 128 ≤ (-28686401341117 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_128 cCB_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_128 : (-130387336029 / 8000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 128 * cCG cZ 128) ∧ kappa * (ex (57436 / 100000) 128 * cCG cZ 128) ≤ (-16298410928413 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_128 : (-280918201111 / 12500000000000 : ℝ) ≤ ex (57436 / 100000) 128 * sCG cZ 128 ∧ ex (57436 / 100000) 128 * sCG cZ 128 ≤ (-702294835777 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_128 sCB_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_128 : (-6384237917519 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 128 * sCG cZ 128) ∧ kappa * (ex (57436 / 100000) 128 * sCG cZ 128) ≤ (-638423185413 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_128 : (-139187339398917 / 500000000000000 : ℝ) ≤ Real.log 128 * (ex (57436 / 100000) 128 * cCG cZ 128) ∧ Real.log 128 * (ex (57436 / 100000) 128 * cCG cZ 128) ≤ (-139187287457489 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_128 eC_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_128 : (-79080412582271 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 128 * (ex (57436 / 100000) 128 * cCG cZ 128)) ∧ kappa * (Real.log 128 * (ex (57436 / 100000) 128 * cCG cZ 128)) ≤ (-2471261970979 / 31250000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_129 : (2429906201962011 / 500000000000000 : ℝ) ≤ Real.log 129 ∧ Real.log 129 ≤ (4859812406000023 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_129
  constructor <;> linarith [h.1, h.2]

theorem eC_129 : (150212720167 / 25000000000000 : ℝ) ≤ ex (57436 / 100000) 129 * cCG cZ 129 ∧ ex (57436 / 100000) 129 * cCG cZ 129 ≤ (3004265016227 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_129 cCB_129 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_129 : (-476934098971 / 7812500000000 : ℝ) ≤ ex (57436 / 100000) 129 * sCG cZ 129 ∧ ex (57436 / 100000) 129 * sCG cZ 129 ≤ (-15261885844219 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_129 sCB_129 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_129 : (2920022562779 / 100000000000000 : ℝ) ≤ Real.log 129 * (ex (57436 / 100000) 129 * cCG cZ 129) ∧ Real.log 129 * (ex (57436 / 100000) 129 * cCG cZ 129) ≤ (3650041099193 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_129 eC_129 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_131 : (2437598661381751 / 500000000000000 : ℝ) ≤ Real.log 131 ∧ Real.log 131 ≤ (2437598662419751 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_131
  constructor <;> linarith [h.1, h.2]

theorem eC_131 : (28196843555631 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 131 * cCG cZ 131 ∧ ex (57436 / 100000) 131 * cCG cZ 131 ≤ (14098432323533 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_131 cCB_131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_131 : (13467379404351 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 131 * sCG cZ 131 ∧ ex (57436 / 100000) 131 * sCG cZ 131 ≤ (2154781549579 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_131 sCB_131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_131 : (137465176212793 / 1000000000000000 : ℝ) ≤ Real.log 131 * (ex (57436 / 100000) 131 * cCG cZ 131) ∧ Real.log 131 * (ex (57436 / 100000) 131 * cCG cZ 131) ≤ (68732639548119 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_131 eC_131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_132 : (4882801922148721 / 1000000000000000 : ℝ) ≤ Real.log 132 ∧ Real.log 132 ≤ (2441400962112361 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_132
  constructor <;> linarith [h.1, h.2]

theorem eC_132 : (-21369015263087 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 132 * cCG cZ 132 ∧ ex (57436 / 100000) 132 * cCG cZ 132 ≤ (-10684502383121 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_132 cCB_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_132 : (-6070489423749 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 132 * cCG cZ 132) ∧ kappa * (ex (57436 / 100000) 132 * cCG cZ 132) ≤ (-1214097288363 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_132 : (8575068023321 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 132 * sCG cZ 132 ∧ ex (57436 / 100000) 132 * sCG cZ 132 ≤ (42875361116843 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_132 sCB_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_132 : (12179985624657 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 132 * sCG cZ 132) ∧ kappa * (ex (57436 / 100000) 132 * sCG cZ 132) ≤ (6089995795193 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_132 : (-104340668845389 / 500000000000000 : ℝ) ≤ Real.log 132 * (ex (57436 / 100000) 132 * cCG cZ 132) ∧ Real.log 132 * (ex (57436 / 100000) 132 * cCG cZ 132) ≤ (-208681235094023 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_132 eC_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_132 : (-11856398975707 / 200000000000000 : ℝ) ≤ kappa * (Real.log 132 * (ex (57436 / 100000) 132 * cCG cZ 132)) ∧ kappa * (Real.log 132 * (ex (57436 / 100000) 132 * cCG cZ 132)) ≤ (-29640982866473 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_133 : (611293640973013 / 125000000000000 : ℝ) ≤ Real.log 133 ∧ Real.log 133 ≤ (978069825972021 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_133
  constructor <;> linarith [h.1, h.2]

theorem eC_133 : (-10751033596709 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 133 * cCG cZ 133 ∧ ex (57436 / 100000) 133 * cCG cZ 133 ≤ (-13438786761251 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_133 cCB_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_133 : (-15270716722247 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 133 * cCG cZ 133) ∧ kappa * (ex (57436 / 100000) 133 * cCG cZ 133) ≤ (-3054142154809 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_133 : (-13634352281503 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 133 * sCG cZ 133 ∧ ex (57436 / 100000) 133 * sCG cZ 133 ≤ (-5453736731213 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_133 sCB_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_133 : (-3873233759513 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 133 * sCG cZ 133) ∧ kappa * (ex (57436 / 100000) 133 * sCG cZ 133) ≤ (-7746461579801 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_133 : (-131440769486907 / 500000000000000 : ℝ) ≤ Real.log 133 * (ex (57436 / 100000) 133 * cCG cZ 133) ∧ Real.log 133 * (ex (57436 / 100000) 133 * cCG cZ 133) ≤ (-262881436465441 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_133 eC_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_133 : (-37339568117489 / 500000000000000 : ℝ) ≤ kappa * (Real.log 133 * (ex (57436 / 100000) 133 * cCG cZ 133)) ∧ kappa * (Real.log 133 * (ex (57436 / 100000) 133 * cCG cZ 133)) ≤ (-145857631083 / 1953125000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_134 : (2448919899756631 / 500000000000000 : ℝ) ≤ Real.log 134 ∧ Real.log 134 ≤ (2448919900794631 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_134
  constructor <;> linarith [h.1, h.2]

theorem eC_134 : (435670579977 / 50000000000000 : ℝ) ≤ ex (57436 / 100000) 134 * cCG cZ 134 ∧ ex (57436 / 100000) 134 * cCG cZ 134 ≤ (217835809533 / 25000000000000 : ℝ) := by
  exact mul_bounds_of exB_134 cCB_134 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_134 : (-11876275076089 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 134 * sCG cZ 134 ∧ ex (57436 / 100000) 134 * sCG cZ 134 ≤ (-46391683233 / 781250000000 : ℝ) := by
  exact mul_bounds_of exB_134 sCB_134 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_134 : (42676894121767 / 1000000000000000 : ℝ) ≤ Real.log 134 * (ex (57436 / 100000) 134 * cCG cZ 134) ∧ Real.log 134 * (ex (57436 / 100000) 134 * cCG cZ 134) ≤ (21338497962843 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_134 eC_134 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_136 : (2456327442649201 / 500000000000000 : ℝ) ≤ Real.log 136 ∧ Real.log 136 ≤ (4912654887374403 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_136
  constructor <;> linarith [h.1, h.2]

theorem eC_136 : (15028733707549 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 136 * cCG cZ 136 ∧ ex (57436 / 100000) 136 * cCG cZ 136 ≤ (30057488050137 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_136 cCB_136 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_136 : (12839963148181 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 136 * sCG cZ 136 ∧ ex (57436 / 100000) 136 * sCG cZ 136 ≤ (2054394930129 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_136 sCB_136 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_136 : (73830982068239 / 500000000000000 : ℝ) ≤ Real.log 136 * (ex (57436 / 100000) 136 * cCG cZ 136) ∧ Real.log 136 * (ex (57436 / 100000) 136 * cCG cZ 136) ≤ (18457758196463 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_136 eC_136 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_137 : (196799237015619 / 40000000000000 : ℝ) ≤ Real.log 137 ∧ Real.log 137 ≤ (1229995231866619 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_137
  constructor <;> linarith [h.1, h.2]

theorem eC_137 : (-1509081189133 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 137 * cCG cZ 137 ∧ ex (57436 / 100000) 137 * cCG cZ 137 ≤ (-37727009182861 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_137 cCB_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_137 : (-5358729266081 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 137 * cCG cZ 137) ∧ kappa * (ex (57436 / 100000) 137 * cCG cZ 137) ≤ (-17147924313 / 1600000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_137 : (45697720418091 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 137 * sCG cZ 137 ∧ ex (57436 / 100000) 137 * sCG cZ 137 ≤ (11424435243607 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_137 sCB_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_137 : (12981764722057 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 137 * sCG cZ 137) ∧ kappa * (ex (57436 / 100000) 137 * sCG cZ 137) ≤ (12981770561683 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_137 : (-4640406667833 / 25000000000000 : ℝ) ≤ Real.log 137 * (ex (57436 / 100000) 137 * cCG cZ 137) ∧ Real.log 137 * (ex (57436 / 100000) 137 * cCG cZ 137) ≤ (-185616165551707 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_137 eC_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_137 : (-13182422892287 / 250000000000000 : ℝ) ≤ kappa * (Real.log 137 * (ex (57436 / 100000) 137 * cCG cZ 137)) ∧ kappa * (Real.log 137 * (ex (57436 / 100000) 137 * cCG cZ 137)) ≤ (-13182415707813 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_138 : (985450736943911 / 200000000000000 : ℝ) ≤ Real.log 138 ∧ Real.log 138 ≤ (1231813421698889 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_138
  constructor <;> linarith [h.1, h.2]

theorem eC_138 : (-55825568701921 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 138 * cCG cZ 138 ∧ ex (57436 / 100000) 138 * cCG cZ 138 ≤ (-27912774116479 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_138 cCB_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_138 : (-1585887417869 / 100000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 138 * cCG cZ 138) ∧ kappa * (ex (57436 / 100000) 138 * cCG cZ 138) ≤ (-3171773672777 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_138 : (-4782147357113 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 138 * sCG cZ 138 ∧ ex (57436 / 100000) 138 * sCG cZ 138 ≤ (-19128569003253 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_138 sCB_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_138 : (-5434031394851 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 138 * sCG cZ 138) ∧ kappa * (ex (57436 / 100000) 138 * sCG cZ 138) ≤ (-5434025592479 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_138 : (-275066739203999 / 1000000000000000 : ℝ) ≤ Real.log 138 * (ex (57436 / 100000) 138 * cCG cZ 138) ∧ Real.log 138 * (ex (57436 / 100000) 138 * cCG cZ 138) ≤ (-275066638232331 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_138 eC_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_138 : (-78140696265373 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 138 * (ex (57436 / 100000) 138 * cCG cZ 138)) ∧ kappa * (Real.log 138 * (ex (57436 / 100000) 138 * cCG cZ 138)) ≤ (-78140667581437 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_139 : (2467236966346521 / 500000000000000 : ℝ) ≤ Real.log 139 ∧ Real.log 139 ≤ (4934473934769043 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_139
  constructor <;> linarith [h.1, h.2]

theorem eC_139 : (-2271588699297 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 139 * cCG cZ 139 ∧ ex (57436 / 100000) 139 * cCG cZ 139 ≤ (-567892090549 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_139 cCB_139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_139 : (-58723700153221 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 139 * sCG cZ 139 ∧ ex (57436 / 100000) 139 * sCG cZ 139 ≤ (-14680919937199 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_139 sCB_139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_139 : (-11209095227197 / 1000000000000000 : ℝ) ≤ Real.log 139 * (ex (57436 / 100000) 139 * cCG cZ 139) ∧ Real.log 139 * (ex (57436 / 100000) 139 * cCG cZ 139) ≤ (-5604497434793 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_139 eC_139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_141 : (2474379944970259 / 500000000000000 : ℝ) ≤ Real.log 141 ∧ Real.log 141 ≤ (4948759892016519 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_141
  constructor <;> linarith [h.1, h.2]

theorem eC_141 : (8378296000249 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 141 * cCG cZ 141 ∧ ex (57436 / 100000) 141 * cCG cZ 141 ≤ (20945750115337 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_141 cCB_141 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_141 : (10132005376097 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 141 * sCG cZ 141 ∧ ex (57436 / 100000) 141 * sCG cZ 141 ≤ (8105608345461 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_141 sCB_141 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_141 : (103655437980203 / 500000000000000 : ℝ) ≤ Real.log 141 * (ex (57436 / 100000) 141 * cCG cZ 141) ∧ Real.log 141 * (ex (57436 / 100000) 141 * cCG cZ 141) ≤ (207310976157961 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_141 eC_141 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_142 : (4955827057163611 / 1000000000000000 : ℝ) ≤ Real.log 142 ∧ Real.log 142 ≤ (1238956764809903 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_142
  constructor <;> linarith [h.1, h.2]

theorem eC_142 : (-10620426167673 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 142 * cCG cZ 142 ∧ ex (57436 / 100000) 142 * cCG cZ 142 ≤ (-21240832198867 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_142 cCB_142 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_142 : (-6034081021781 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 142 * cCG cZ 142) ∧ kappa * (ex (57436 / 100000) 142 * cCG cZ 142) ≤ (-1508518825357 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_142 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_142 : (3376605268337 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 142 * sCG cZ 142 ∧ ex (57436 / 100000) 142 * sCG cZ 142 ≤ (5402570446897 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_142 sCB_142 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_142 : (1534756473689 / 100000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 142 * sCG cZ 142) ∧ kappa * (ex (57436 / 100000) 142 * sCG cZ 142) ≤ (306951409367 / 20000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_142 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_142 : (-105265990764821 / 1000000000000000 : ℝ) ≤ Real.log 142 * (ex (57436 / 100000) 142 * cCG cZ 142) ∧ Real.log 142 * (ex (57436 / 100000) 142 * cCG cZ 142) ≤ (-105265890927817 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_142 eC_142 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_142 : (-5980772401077 / 200000000000000 : ℝ) ≤ kappa * (Real.log 142 * (ex (57436 / 100000) 142 * cCG cZ 142)) ∧ kappa * (Real.log 142 * (ex (57436 / 100000) 142 * cCG cZ 142)) ≤ (-29903833643783 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_142 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_143 : (4962844629822257 / 1000000000000000 : ℝ) ≤ Real.log 143 ∧ Real.log 143 ≤ (2481422315949129 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_143
  constructor <;> linarith [h.1, h.2]

theorem eC_143 : (-28897615090973 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 143 * cCG cZ 143 ∧ ex (57436 / 100000) 143 * cCG cZ 143 ≤ (-3612200631027 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_143 cCB_143 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_143 : (-1026150858039 / 62500000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 143 * cCG cZ 143) ∧ kappa * (ex (57436 / 100000) 143 * cCG cZ 143) ≤ (-65673632091 / 4000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_143 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_143 : (1613942699819 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 143 * sCG cZ 143 ∧ ex (57436 / 100000) 143 * sCG cZ 143 ≤ (161396271833 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_143 sCB_143 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_143 : (458487298977 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 143 * sCG cZ 143) ∧ kappa * (ex (57436 / 100000) 143 * sCG cZ 143) ≤ (229246492909 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_143 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_143 : (-57365749571559 / 200000000000000 : ℝ) ≤ Real.log 143 * (ex (57436 / 100000) 143 * cCG cZ 143) ∧ Real.log 143 * (ex (57436 / 100000) 143 * cCG cZ 143) ≤ (-143414324028263 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_143 eC_143 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_143 : (-40741018218693 / 500000000000000 : ℝ) ≤ kappa * (Real.log 143 * (ex (57436 / 100000) 143 * cCG cZ 143)) ∧ kappa * (Real.log 143 * (ex (57436 / 100000) 143 * cCG cZ 143)) ≤ (-16296401617187 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_143 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_144 : (4969813299138351 / 1000000000000000 : ℝ) ≤ Real.log 144 ∧ Real.log 144 ≤ (4969813301214351 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_144
  constructor <;> linarith [h.1, h.2]

theorem eC_144 : (-12227119343039 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 144 * cCG cZ 144 ∧ ex (57436 / 100000) 144 * cCG cZ 144 ≤ (-24454218723037 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_144 cCB_144 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_144 : (-1629270487809 / 31250000000000 : ℝ) ≤ ex (57436 / 100000) 144 * sCG cZ 144 ∧ ex (57436 / 100000) 144 * sCG cZ 144 ≤ (-26068317806913 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_144 sCB_144 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_144 : (-121533000693141 / 1000000000000000 : ℝ) ≤ Real.log 144 * (ex (57436 / 100000) 144 * cCG cZ 144) ∧ Real.log 144 * (ex (57436 / 100000) 144 * cCG cZ 144) ≤ (-121532901429787 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_144 eC_144 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_146 : (4983606621270687 / 1000000000000000 : ℝ) ≤ Real.log 146 ∧ Real.log 146 ≤ (4983606623346687 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_146
  constructor <;> linarith [h.1, h.2]

theorem eC_146 : (54796617239523 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 146 * cCG cZ 146 ∧ ex (57436 / 100000) 146 * cCG cZ 146 ≤ (6849579635943 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_146 cCB_146 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_146 : (8084519733783 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 146 * sCG cZ 146 ∧ ex (57436 / 100000) 146 * sCG cZ 146 ≤ (16169059269519 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_146 sCB_146 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_146 : (136542392249061 / 500000000000000 : ℝ) ≤ Real.log 146 * (ex (57436 / 100000) 146 * cCG cZ 146) ∧ Real.log 146 * (ex (57436 / 100000) 146 * cCG cZ 146) ≤ (273084883526609 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_146 eC_146 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_147 : (2495216293170543 / 500000000000000 : ℝ) ≤ Real.log 147 ∧ Real.log 147 ≤ (4990432588417087 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_147
  constructor <;> linarith [h.1, h.2]

theorem eC_147 : (8362687835681 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 147 * cCG cZ 147 ∧ ex (57436 / 100000) 147 * cCG cZ 147 ≤ (4181353763543 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_147 cCB_147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_147 : (296958045537 / 125000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 147 * cCG cZ 147) ∧ kappa * (ex (57436 / 100000) 147 * cCG cZ 147) ≤ (593917489553 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_147 : (28145508029751 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 147 * sCG cZ 147 ∧ ex (57436 / 100000) 147 * sCG cZ 147 ≤ (56291035808067 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_147 sCB_147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_147 : (3997774504747 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 147 * sCG cZ 147) ∧ kappa * (ex (57436 / 100000) 147 * sCG cZ 147) ≤ (15991103629143 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_147 : (2086671494229 / 50000000000000 : ℝ) ≤ Real.log 147 * (ex (57436 / 100000) 147 * cCG cZ 147) ∧ Real.log 147 * (ex (57436 / 100000) 147 * cCG cZ 147) ≤ (41733528170571 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_147 eC_147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_147 : (185243638403 / 15625000000000 : ℝ) ≤ kappa * (Real.log 147 * (ex (57436 / 100000) 147 * cCG cZ 147)) ∧ kappa * (Real.log 147 * (ex (57436 / 100000) 147 * cCG cZ 147)) ≤ (11855620778783 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_148 : (999442454665293 / 200000000000000 : ℝ) ≤ Real.log 148 ∧ Real.log 148 ≤ (2498606137701233 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_148
  constructor <;> linarith [h.1, h.2]

theorem eC_148 : (-47116640901189 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 148 * cCG cZ 148 ∧ ex (57436 / 100000) 148 * cCG cZ 148 ≤ (-9423324240793 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_148 cCB_148 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_148 : (-6692425148091 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 148 * cCG cZ 148) ∧ kappa * (ex (57436 / 100000) 148 * cCG cZ 148) ≤ (-13384844700613 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_148 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_148 : (31520033727383 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 148 * sCG cZ 148 ∧ ex (57436 / 100000) 148 * sCG cZ 148 ≤ (15760026702903 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_148 sCB_148 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_148 : (2238545260773 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 148 * sCG cZ 148) ∧ kappa * (ex (57436 / 100000) 148 * sCG cZ 148) ≤ (8954186633321 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_148 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_148 : (-14715741017947 / 62500000000000 : ℝ) ≤ Real.log 148 * (ex (57436 / 100000) 148 * cCG cZ 148) ∧ Real.log 148 * (ex (57436 / 100000) 148 * cCG cZ 148) ≤ (-235451757758127 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_148 eC_148 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_148 : (-13377387640901 / 200000000000000 : ℝ) ≤ kappa * (Real.log 148 * (ex (57436 / 100000) 148 * cCG cZ 148)) ∧ kappa * (Real.log 148 * (ex (57436 / 100000) 148 * cCG cZ 148)) ≤ (-66886910214473 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_148 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_149 : (5003946305507809 / 1000000000000000 : ℝ) ≤ Real.log 149 ∧ Real.log 149 ≤ (500394630758381 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_149
  constructor <;> linarith [h.1, h.2]

theorem eC_149 : (-380308940827 / 7812500000000 : ℝ) ≤ ex (57436 / 100000) 149 * cCG cZ 149 ∧ ex (57436 / 100000) 149 * cCG cZ 149 ≤ (-24339762397531 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_149 cCB_149 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_149 : (-14309362566877 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 149 * sCG cZ 149 ∧ ex (57436 / 100000) 149 * sCG cZ 149 ≤ (-14309352763471 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_149 sCB_149 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_149 : (-1948718612677 / 8000000000000 : ℝ) ≤ Real.log 149 * (ex (57436 / 100000) 149 * cCG cZ 149) ∧ Real.log 149 * (ex (57436 / 100000) 149 * cCG cZ 149) ≤ (-121794864126063 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_149 eC_149 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_151 : (2508639918188637 / 500000000000000 : ℝ) ≤ Real.log 151 ∧ Real.log 151 ≤ (200691193538131 / 40000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_151
  constructor <;> linarith [h.1, h.2]

theorem eC_151 : (10364476446969 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 151 * cCG cZ 151 ∧ ex (57436 / 100000) 151 * cCG cZ 151 ≤ (1619450052273 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_151 cCB_151 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_151 : (-5330924281547 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 151 * sCG cZ 151 ∧ ex (57436 / 100000) 151 * sCG cZ 151 ≤ (-5205976007 / 244140625000 : ℝ) := by
  exact mul_bounds_of exB_151 sCB_151 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_151 : (260007393459923 / 1000000000000000 : ℝ) ≤ Real.log 151 * (ex (57436 / 100000) 151 * cCG cZ 151) ∧ Real.log 151 * (ex (57436 / 100000) 151 * cCG cZ 151) ≤ (130003745546423 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_151 eC_151 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_152 : (5023880520408627 / 1000000000000000 : ℝ) ≤ Real.log 152 ∧ Real.log 152 ≤ (5023880522484627 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_152
  constructor <;> linarith [h.1, h.2]

theorem eC_152 : (42390204571027 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 152 * cCG cZ 152 ∧ ex (57436 / 100000) 152 * cCG cZ 152 ≤ (42390223918677 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_152 cCB_152 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_152 : (752635548921 / 62500000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 152 * cCG cZ 152) ∧ kappa * (ex (57436 / 100000) 152 * cCG cZ 152) ≤ (12042174278999 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_152 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_152 : (36326416245599 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 152 * sCG cZ 152 ∧ ex (57436 / 100000) 152 * sCG cZ 152 ≤ (18163217792127 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_152 sCB_152 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_152 : (5159786796599 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 152 * sCG cZ 152) ∧ kappa * (ex (57436 / 100000) 152 * sCG cZ 152) ≤ (5159789543453 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_152 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_152 : (212963323000519 / 1000000000000000 : ℝ) ≤ Real.log 152 * (ex (57436 / 100000) 152 * cCG cZ 152) ∧ Real.log 152 * (ex (57436 / 100000) 152 * cCG cZ 152) ≤ (53240855072201 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_152 eC_152 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_152 : (7562302146383 / 125000000000000 : ℝ) ≤ kappa * (Real.log 152 * (ex (57436 / 100000) 152 * cCG cZ 152)) ∧ kappa * (Real.log 152 * (ex (57436 / 100000) 152 * cCG cZ 152)) ≤ (15124611202157 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_152 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_153 : (2515218960477393 / 500000000000000 : ℝ) ≤ Real.log 153 ∧ Real.log 153 ≤ (2515218961515393 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_153
  constructor <;> linarith [h.1, h.2]

theorem eC_153 : (-12646310576349 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 153 * cCG cZ 153 ∧ ex (57436 / 100000) 153 * cCG cZ 153 ≤ (-12646291285549 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_153 cCB_153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_153 : (-3592551816639 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 153 * cCG cZ 153) ∧ kappa * (ex (57436 / 100000) 153 * cCG cZ 153) ≤ (-1796273168263 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_153 : (10831845651093 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 153 * sCG cZ 153 ∧ ex (57436 / 100000) 153 * sCG cZ 153 ≤ (211559560921 / 3906250000000 : ℝ) := by
  exact mul_bounds_of exB_153 sCB_153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_153 : (15385501777947 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 153 * sCG cZ 153) ∧ kappa * (ex (57436 / 100000) 153 * sCG cZ 153) ≤ (123084058177 / 8000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_153 : (-15904120077423 / 250000000000000 : ℝ) ≤ Real.log 153 * (ex (57436 / 100000) 153 * cCG cZ 153) ∧ Real.log 153 * (ex (57436 / 100000) 153 * cCG cZ 153) ≤ (-12723276648453 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_153 eC_153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_153 : (-1807210889887 / 100000000000000 : ℝ) ≤ kappa * (Real.log 153 * (ex (57436 / 100000) 153 * cCG cZ 153)) ∧ kappa * (Real.log 153 * (ex (57436 / 100000) 153 * cCG cZ 153)) ≤ (-18072081324047 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_154 : (5036952601975979 / 1000000000000000 : ℝ) ≤ Real.log 154 ∧ Real.log 154 ≤ (251847630202599 / 50000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_154
  constructor <;> linarith [h.1, h.2]

theorem eC_154 : (-10718162031381 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 154 * cCG cZ 154 ∧ ex (57436 / 100000) 154 * cCG cZ 154 ≤ (-10718158188569 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_154 cCB_154 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_154 : (879711565729 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 154 * sCG cZ 154 ∧ ex (57436 / 100000) 154 * sCG cZ 154 ≤ (3518851054649 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_154 sCB_154 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_154 : (-134967185386539 / 500000000000000 : ℝ) ≤ Real.log 154 * (ex (57436 / 100000) 154 * cCG cZ 154) ∧ Real.log 154 * (ex (57436 / 100000) 154 * cCG cZ 154) ≤ (-269934273881513 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_154 eC_154 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_156 : (5049856006811887 / 1000000000000000 : ℝ) ≤ Real.log 156 ∧ Real.log 156 ≤ (315616000555493 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_156
  constructor <;> linarith [h.1, h.2]

theorem eC_156 : (17327491586073 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 156 * cCG cZ 156 ∧ ex (57436 / 100000) 156 * cCG cZ 156 ≤ (3465502124467 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_156 cCB_156 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_156 : (-52198456152573 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 156 * sCG cZ 156 ∧ ex (57436 / 100000) 156 * sCG cZ 156 ≤ (-26099218537361 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_156 sCB_156 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_156 : (87501337468913 / 1000000000000000 : ℝ) ≤ Real.log 156 * (ex (57436 / 100000) 156 * cCG cZ 156) ∧ Real.log 156 * (ex (57436 / 100000) 156 * cCG cZ 156) ≤ (21875358408817 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_156 eC_156 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_157 : (2528122902455329 / 500000000000000 : ℝ) ≤ Real.log 157 ∧ Real.log 157 ≤ (5056245806986659 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_157
  constructor <;> linarith [h.1, h.2]

theorem eC_157 : (10769472675979 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 157 * cCG cZ 157 ∧ ex (57436 / 100000) 157 * cCG cZ 157 ≤ (53847382419883 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_157 cCB_157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_157 : (15296907502287 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 157 * cCG cZ 157) ∧ kappa * (ex (57436 / 100000) 157 * cCG cZ 157) ≤ (305938258223 / 20000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_157 : (-10161636346791 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 157 * sCG cZ 157 ∧ ex (57436 / 100000) 157 * sCG cZ 157 ≤ (-2032323471781 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_157 sCB_157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_157 : (-2886707937251 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 157 * sCG cZ 157) ∧ kappa * (ex (57436 / 100000) 157 * sCG cZ 157) ≤ (-2886702543189 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_157 : (272265505195093 / 1000000000000000 : ℝ) ≤ Real.log 157 * (ex (57436 / 100000) 157 * cCG cZ 157) ∧ Real.log 157 * (ex (57436 / 100000) 157 * cCG cZ 157) ≤ (272265601577741 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_157 eC_157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_157 : (19336231096637 / 250000000000000 : ℝ) ≤ kappa * (Real.log 157 * (ex (57436 / 100000) 157 * cCG cZ 157)) ∧ kappa * (Real.log 157 * (ex (57436 / 100000) 157 * cCG cZ 157)) ≤ (1933623794171 / 25000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_158 : (5062595032589317 / 1000000000000000 : ℝ) ≤ Real.log 158 ∧ Real.log 158 ≤ (2531297517332659 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_158
  constructor <;> linarith [h.1, h.2]

theorem eC_158 : (35185701352049 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 158 * cCG cZ 158 ∧ ex (57436 / 100000) 158 * cCG cZ 158 ≤ (7037144056203 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_158 cCB_158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_158 : (624720024809 / 62500000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 158 * cCG cZ 158) ∧ kappa * (ex (57436 / 100000) 158 * cCG cZ 158) ≤ (9995525774267 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_158 : (20874278441621 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 158 * sCG cZ 158 ∧ ex (57436 / 100000) 158 * sCG cZ 158 ≤ (1304642994423 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_158 sCB_158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_158 : (2964972530277 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 158 * sCG cZ 158) ∧ kappa * (ex (57436 / 100000) 158 * sCG cZ 158) ≤ (11859895501081 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_158 : (89065478441527 / 500000000000000 : ℝ) ≤ Real.log 158 * (ex (57436 / 100000) 158 * cCG cZ 158) ∧ Real.log 158 * (ex (57436 / 100000) 158 * cCG cZ 158) ≤ (17813105278579 / 100000000000000 : ℝ) := by
  exact mul_bounds_of lgB_158 eC_158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_158 : (10120654381943 / 200000000000000 : ℝ) ≤ kappa * (Real.log 158 * (ex (57436 / 100000) 158 * cCG cZ 158)) ∧ kappa * (Real.log 158 * (ex (57436 / 100000) 158 * cCG cZ 158)) ≤ (25301649576837 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_159 : (2534452100891291 / 500000000000000 : ℝ) ≤ Real.log 159 ∧ Real.log 159 ≤ (2534452101929291 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_159
  constructor <;> linarith [h.1, h.2]

theorem eC_159 : (-1865631975671 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 159 * cCG cZ 159 ∧ ex (57436 / 100000) 159 * cCG cZ 159 ≤ (-2332037614047 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_159 cCB_159 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_159 : (10220355610431 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 159 * sCG cZ 159 ∧ ex (57436 / 100000) 159 * sCG cZ 159 ≤ (25550898467593 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_159 sCB_159 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_159 : (-47283548821659 / 500000000000000 : ℝ) ≤ Real.log 159 * (ex (57436 / 100000) 159 * cCG cZ 159) ∧ Real.log 159 * (ex (57436 / 100000) 159 * cCG cZ 159) ≤ (-47283501042231 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_159 eC_159 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_161 : (5081404364546813 / 1000000000000000 : ℝ) ≤ Real.log 161 ∧ Real.log 161 ≤ (2540702183311407 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_161
  constructor <;> linarith [h.1, h.2]

theorem eC_161 : (-35228233392077 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 161 * cCG cZ 161 ∧ ex (57436 / 100000) 161 * cCG cZ 161 ≤ (-1409128586893 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_161 cCB_161 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_161 : (-40941811610991 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 161 * sCG cZ 161 ∧ ex (57436 / 100000) 161 * sCG cZ 161 ≤ (-2047089644133 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_161 sCB_161 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_161 : (-44752224746727 / 250000000000000 : ℝ) ≤ Real.log 161 * (ex (57436 / 100000) 161 * cCG cZ 161) ∧ Real.log 161 * (ex (57436 / 100000) 161 * cCG cZ 161) ≤ (-22376100473893 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_161 eC_161 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_162 : (2543798167397367 / 500000000000000 : ℝ) ≤ Real.log 162 ∧ Real.log 162 ≤ (1017519267374147 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_162
  constructor <;> linarith [h.1, h.2]

theorem eC_162 : (16945638097389 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 162 * cCG cZ 162 ∧ ex (57436 / 100000) 162 * cCG cZ 162 ≤ (4236414192703 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_162 cCB_162 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_162 : (4813900667971 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 162 * cCG cZ 162) ∧ kappa * (ex (57436 / 100000) 162 * cCG cZ 162) ≤ (4813905972701 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_162 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_162 : (-2554128302157 / 50000000000000 : ℝ) ≤ ex (57436 / 100000) 162 * sCG cZ 162 ∧ ex (57436 / 100000) 162 * sCG cZ 162 ≤ (-51082547329003 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_162 sCB_162 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_162 : (-290229730369 / 20000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 162 * sCG cZ 162) ∧ kappa * (ex (57436 / 100000) 162 * sCG cZ 162) ≤ (-2902296240431 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_162 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_162 : (43106283137517 / 500000000000000 : ℝ) ≤ Real.log 162 * (ex (57436 / 100000) 162 * cCG cZ 162) ∧ Real.log 162 * (ex (57436 / 100000) 162 * cCG cZ 162) ≤ (21553165328263 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_162 eC_162 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_162 : (24491183394439 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 162 * (ex (57436 / 100000) 162 * cCG cZ 162)) ∧ kappa * (Real.log 162 * (ex (57436 / 100000) 162 * cCG cZ 162)) ≤ (97964841571 / 4000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_162 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_163 : (5093750200369113 / 1000000000000000 : ℝ) ≤ Real.log 163 ∧ Real.log 163 ≤ (5093750202445113 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_163
  constructor <;> linarith [h.1, h.2]

theorem eC_163 : (10453250305057 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 163 * cCG cZ 163 ∧ ex (57436 / 100000) 163 * cCG cZ 163 ≤ (10453254032551 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_163 cCB_163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_163 : (593909870337 / 40000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 163 * cCG cZ 163) ∧ kappa * (ex (57436 / 100000) 163 * cCG cZ 163) ≤ (14847752052941 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_163 : (-12017355293637 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 163 * sCG cZ 163 ∧ ex (57436 / 100000) 163 * sCG cZ 163 ≤ (-3004334176043 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_163 sCB_163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_163 : (-3413878801307 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 163 * sCG cZ 163) ∧ kappa * (ex (57436 / 100000) 163 * sCG cZ 163) ≤ (-3413873520429 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_163 : (133115614589731 / 500000000000000 : ℝ) ≤ Real.log 163 * (ex (57436 / 100000) 163 * cCG cZ 163) ∧ Real.log 163 * (ex (57436 / 100000) 163 * cCG cZ 163) ≤ (53246264844517 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_163 eC_163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_163 : (75630713025759 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 163 * (ex (57436 / 100000) 163 * cCG cZ 163)) ∧ kappa * (Real.log 163 * (ex (57436 / 100000) 163 * cCG cZ 163)) ≤ (75630740025519 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_164 : (5099866427386549 / 1000000000000000 : ℝ) ≤ Real.log 164 ∧ Real.log 164 ≤ (5099866429462549 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_164
  constructor <;> linarith [h.1, h.2]

theorem eC_164 : (7506039240841 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 164 * cCG cZ 164 ∧ ex (57436 / 100000) 164 * cCG cZ 164 ≤ (4691276843191 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_164 cCB_164 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_164 : (19023175808611 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 164 * sCG cZ 164 ∧ ex (57436 / 100000) 164 * sCG cZ 164 ≤ (9511592541091 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_164 sCB_164 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_164 : (38279797527011 / 200000000000000 : ℝ) ≤ Real.log 164 * (ex (57436 / 100000) 164 * cCG cZ 164) ∧ Real.log 164 * (ex (57436 / 100000) 164 * cCG cZ 164) ≤ (191399082271239 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_164 eC_164 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_166 : (5111987787918893 / 1000000000000000 : ℝ) ≤ Real.log 166 ∧ Real.log 166 ≤ (2555993894997447 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_166
  constructor <;> linarith [h.1, h.2]

theorem eC_166 : (-12545825968609 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 166 * cCG cZ 166 ∧ ex (57436 / 100000) 166 * cCG cZ 166 ≤ (-10036657091647 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_166 cCB_166 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_166 : (4317018894189 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 166 * sCG cZ 166 ∧ ex (57436 / 100000) 166 * sCG cZ 166 ≤ (8634046976849 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_166 sCB_166 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_166 : (-256536436667721 / 1000000000000000 : ℝ) ≤ Real.log 166 * (ex (57436 / 100000) 166 * cCG cZ 166) ∧ Real.log 166 * (ex (57436 / 100000) 166 * cCG cZ 166) ≤ (-51307268484029 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_166 eC_166 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_167 : (1023598762395821 / 200000000000000 : ℝ) ≤ Real.log 167 ∧ Real.log 167 ≤ (2558996907027553 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_167
  constructor <;> linarith [h.1, h.2]

theorem eC_167 : (-41505315350503 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 167 * cCG cZ 167 ∧ ex (57436 / 100000) 167 * cCG cZ 167 ≤ (-41505296970823 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_167 cCB_167 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_167 : (-5895395149533 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 167 * cCG cZ 167) ∧ kappa * (ex (57436 / 100000) 167 * cCG cZ 167) ≤ (-11790785077783 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_167 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_167 : (-4097435943449 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 167 * sCG cZ 167 ∧ ex (57436 / 100000) 167 * sCG cZ 167 ≤ (-16389734589577 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_167 sCB_167 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_167 : (-9311965480099 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 167 * sCG cZ 167) ∧ kappa * (ex (57436 / 100000) 167 * sCG cZ 167) ≤ (-931196026201 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_167 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_167 : (-212423947214281 / 1000000000000000 : ℝ) ≤ Real.log 167 * (ex (57436 / 100000) 167 * cCG cZ 167) ∧ Real.log 167 * (ex (57436 / 100000) 167 * cCG cZ 167) ≤ (-212423853061027 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_167 eC_167 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_167 : (-188578724417 / 3125000000000 : ℝ) ≤ kappa * (Real.log 167 * (ex (57436 / 100000) 167 * cCG cZ 167)) ∧ kappa * (Real.log 167 * (ex (57436 / 100000) 167 * cCG cZ 167)) ≤ (-7543145633309 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_167 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_168 : (5123963978965609 / 1000000000000000 : ℝ) ≤ Real.log 168 ∧ Real.log 168 ≤ (512396398104161 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_168
  constructor <;> linarith [h.1, h.2]

theorem eC_168 : (4820313918713 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 168 * cCG cZ 168 ∧ ex (57436 / 100000) 168 * cCG cZ 168 ≤ (1205083041129 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_168 cCB_168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_168 : (684675084519 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 168 * cCG cZ 168) ∧ kappa * (ex (57436 / 100000) 168 * cCG cZ 168) ≤ (1369355352289 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_168 : (-52486498117549 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 168 * sCG cZ 168 ∧ ex (57436 / 100000) 168 * sCG cZ 168 ≤ (-26243239907447 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_168 sCB_168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_168 : (-2982062839953 / 200000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 168 * sCG cZ 168) ∧ kappa * (ex (57436 / 100000) 168 * sCG cZ 168) ≤ (-3727577250091 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_168 : (24699114886791 / 1000000000000000 : ℝ) ≤ Real.log 168 * (ex (57436 / 100000) 168 * cCG cZ 168) ∧ Real.log 168 * (ex (57436 / 100000) 168 * cCG cZ 168) ≤ (24699208387637 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_168 eC_168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_168 : (877062617593 / 125000000000000 : ℝ) ≤ kappa * (Real.log 168 * (ex (57436 / 100000) 168 * cCG cZ 168)) ∧ kappa * (Real.log 168 * (ex (57436 / 100000) 168 * cCG cZ 168)) ≤ (877065937797 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_169 : (320618669655339 / 62500000000000 : ℝ) ≤ Real.log 169 ∧ Real.log 169 ≤ (320618669785089 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_169
  constructor <;> linarith [h.1, h.2]

theorem eC_169 : (9263481154677 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 169 * cCG cZ 169 ∧ ex (57436 / 100000) 169 * cCG cZ 169 ≤ (2894839000231 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_169 cCB_169 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_169 : (-24776802140749 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 169 * sCG cZ 169 ∧ ex (57436 / 100000) 169 * sCG cZ 169 ≤ (-24776783936151 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_169 sCB_169 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_169 : (237603600335187 / 1000000000000000 : ℝ) ≤ Real.log 169 * (ex (57436 / 100000) 169 * cCG cZ 169) ∧ Real.log 169 * (ex (57436 / 100000) 169 * cCG cZ 169) ≤ (14850230871937 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_169 eC_169 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_171 : (514166355606501 / 100000000000000 : ℝ) ≤ Real.log 171 ∧ Real.log 171 ≤ (5141663558141011 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_171
  constructor <;> linarith [h.1, h.2]

theorem eC_171 : (5385039408053 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 171 * cCG cZ 171 ∧ ex (57436 / 100000) 171 * cCG cZ 171 ≤ (336566093249 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_171 cCB_171 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_171 : (810868918399 / 15625000000000 : ℝ) ≤ ex (57436 / 100000) 171 * sCG cZ 171 ∧ ex (57436 / 100000) 171 * sCG cZ 171 ≤ (25947814458471 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_171 sCB_171 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_171 : (692201521809 / 25000000000000 : ℝ) ≤ Real.log 171 * (ex (57436 / 100000) 171 * cCG cZ 171) ∧ Real.log 171 * (ex (57436 / 100000) 171 * cCG cZ 171) ≤ (27688153865029 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_171 eC_171 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_172 : (5147494476375803 / 1000000000000000 : ℝ) ≤ Real.log 172 ∧ Real.log 172 ≤ (1286873619612951 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_172
  constructor <;> linarith [h.1, h.2]

theorem eC_172 : (-39655335340567 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 172 * cCG cZ 172 ∧ ex (57436 / 100000) 172 * cCG cZ 172 ≤ (-4956914660407 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_172 cCB_172 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_172 : (-70407810917 / 6250000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 172 * cCG cZ 172) ∧ kappa * (ex (57436 / 100000) 172 * cCG cZ 172) ≤ (-2253048923403 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_172 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_172 : (33636829157319 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 172 * sCG cZ 172 ∧ ex (57436 / 100000) 172 * sCG cZ 172 ≤ (4204605900743 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_172 sCB_172 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_172 : (4777759132417 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 172 * sCG cZ 172) ∧ kappa * (ex (57436 / 100000) 172 * sCG cZ 172) ≤ (9555523392071 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_172 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_172 : (-51031404926681 / 250000000000000 : ℝ) ≤ Real.log 172 * (ex (57436 / 100000) 172 * cCG cZ 172) ∧ Real.log 172 * (ex (57436 / 100000) 172 * cCG cZ 172) ≤ (-20412552667449 / 100000000000000 : ℝ) := by
  exact mul_bounds_of lgB_172 eC_172 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_172 : (-28993905434809 / 500000000000000 : ℝ) ≤ kappa * (Real.log 172 * (ex (57436 / 100000) 172 * cCG cZ 172)) ∧ kappa * (Real.log 172 * (ex (57436 / 100000) 172 * cCG cZ 172)) ≤ (-57987784441109 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_172 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_173 : (5153291594060129 / 1000000000000000 : ℝ) ≤ Real.log 173 ∧ Real.log 173 ≤ (515329159613613 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_173
  constructor <;> linarith [h.1, h.2]

theorem eC_173 : (-25031615323727 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 173 * cCG cZ 173 ∧ ex (57436 / 100000) 173 * cCG cZ 173 ≤ (-50063212646997 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_173 cCB_173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_173 : (-14221914693891 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 173 * cCG cZ 173) ∧ kappa * (ex (57436 / 100000) 173 * cCG cZ 173) ≤ (-7110954790169 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_173 : (-13405564432889 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 173 * sCG cZ 173 ∧ ex (57436 / 100000) 173 * sCG cZ 173 ≤ (-6702773238077 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_173 sCB_173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_173 : (-3808239926237 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 173 * sCG cZ 173) ∧ kappa * (ex (57436 / 100000) 173 * sCG cZ 173) ≤ (-238014676569 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_173 : (-5159808515419 / 20000000000000 : ℝ) ≤ Real.log 173 * (ex (57436 / 100000) 173 * cCG cZ 173) ∧ Real.log 173 * (ex (57436 / 100000) 173 * cCG cZ 173) ≤ (-128995166452707 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_173 eC_173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_173 : (-73289673472993 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 173 * (ex (57436 / 100000) 173 * cCG cZ 173)) ∧ kappa * (Real.log 173 * (ex (57436 / 100000) 173 * cCG cZ 173)) ≤ (-73289647091839 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_174 : (5159055298776879 / 1000000000000000 : ℝ) ≤ Real.log 174 ∧ Real.log 174 ≤ (64488191260661 / 12500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_174
  constructor <;> linarith [h.1, h.2]

theorem eC_174 : (-1105899593147 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 174 * cCG cZ 174 ∧ ex (57436 / 100000) 174 * cCG cZ 174 ≤ (-17694375594177 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_174 cCB_174 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_174 : (-48530603993359 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 174 * sCG cZ 174 ∧ ex (57436 / 100000) 174 * sCG cZ 174 ≤ (-48530586060403 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_174 sCB_174 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_174 : (-45643177265889 / 500000000000000 : ℝ) ≤ Real.log 174 * (ex (57436 / 100000) 174 * cCG cZ 174) ∧ Real.log 174 * (ex (57436 / 100000) 174 * cCG cZ 174) ≤ (-91286262167687 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_174 eC_174 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_176 : (2585241997300251 / 500000000000000 : ℝ) ≤ Real.log 176 ∧ Real.log 176 ≤ (5170483996676503 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_176
  constructor <;> linarith [h.1, h.2]

theorem eC_176 : (51309599556471 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 176 * cCG cZ 176 ∧ ex (57436 / 100000) 176 * cCG cZ 176 ≤ (25654808694141 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_176 cCB_176 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_176 : (-456172454133 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 176 * sCG cZ 176 ∧ ex (57436 / 100000) 176 * sCG cZ 176 ≤ (-114040892071 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_176 sCB_176 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_176 : (132647731638047 / 500000000000000 : ℝ) ≤ Real.log 176 * (ex (57436 / 100000) 176 * cCG cZ 176) ∧ Real.log 176 * (ex (57436 / 100000) 176 * cCG cZ 176) ≤ (265295555581707 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_176 eC_176 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_177 : (5176149732136179 / 1000000000000000 : ℝ) ≤ Real.log 177 ∧ Real.log 177 ≤ (258807486710609 / 50000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_177
  constructor <;> linarith [h.1, h.2]

theorem eC_177 : (7691521412827 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 177 * cCG cZ 177 ∧ ex (57436 / 100000) 177 * cCG cZ 177 ≤ (1922881461187 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_177 cCB_177 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_177 : (1748000038907 / 200000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 177 * cCG cZ 177) ∧ kappa * (ex (57436 / 100000) 177 * cCG cZ 177) ≤ (43700026153 / 5000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_177 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_177 : (40864053320899 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 177 * sCG cZ 177 ∧ ex (57436 / 100000) 177 * sCG cZ 177 ≤ (40864071061157 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_177 sCB_177 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_177 : (2902155298711 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 177 * sCG cZ 177) ∧ kappa * (ex (57436 / 100000) 177 * sCG cZ 177) ≤ (11608626234481 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_177 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_177 : (9953116625181 / 62500000000000 : ℝ) ≤ Real.log 177 * (ex (57436 / 100000) 177 * cCG cZ 177) ∧ Real.log 177 * (ex (57436 / 100000) 177 * cCG cZ 177) ≤ (79624978913957 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_177 eC_177 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_177 : (5654943708227 / 125000000000000 : ℝ) ≤ kappa * (Real.log 177 * (ex (57436 / 100000) 177 * cCG cZ 177)) ∧ kappa * (Real.log 177 * (ex (57436 / 100000) 177 * cCG cZ 177)) ≤ (2261978787569 / 50000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_177 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_178 : (1036356709970887 / 200000000000000 : ℝ) ≤ Real.log 178 ∧ Real.log 178 ≤ (1295445887982609 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_178
  constructor <;> linarith [h.1, h.2]

theorem eC_178 : (-14704849114663 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 178 * cCG cZ 178 ∧ ex (57436 / 100000) 178 * cCG cZ 178 ≤ (-1838103928423 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_178 cCB_178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_178 : (-522167434539 / 125000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 178 * cCG cZ 178) ∧ kappa * (ex (57436 / 100000) 178 * cCG cZ 178) ≤ (-167093378069 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_178 : (48819186530729 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 178 * sCG cZ 178 ∧ ex (57436 / 100000) 178 * sCG cZ 178 ≤ (48819204258699 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_178 sCB_178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_178 : (3467126957679 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 178 * sCG cZ 178) ∧ kappa * (ex (57436 / 100000) 178 * sCG cZ 178) ≤ (6934256433431 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_178 : (-3809867263799 / 50000000000000 : ℝ) ≤ Real.log 178 * (ex (57436 / 100000) 178 * cCG cZ 178) ∧ Real.log 178 * (ex (57436 / 100000) 178 * cCG cZ 178) ≤ (-380986267969 / 5000000000000 : ℝ) := by
  exact mul_bounds_of lgB_178 eC_178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_178 : (-21646068989179 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 178 * (ex (57436 / 100000) 178 * cCG cZ 178)) ∧ kappa * (Real.log 178 * (ex (57436 / 100000) 178 * cCG cZ 178)) ≤ (-338219421003 / 15625000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_179 : (1037477161080621 / 200000000000000 : ℝ) ≤ Real.log 179 ∧ Real.log 179 ≤ (2593692903739553 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_179
  constructor <;> linarith [h.1, h.2]

theorem eC_179 : (-47817494910069 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 179 * cCG cZ 179 ∧ ex (57436 / 100000) 179 * cCG cZ 179 ≤ (-9563495455967 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_179 cCB_179 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_179 : (17215063818587 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 179 * sCG cZ 179 ∧ ex (57436 / 100000) 179 * sCG cZ 179 ≤ (17215081412319 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_179 sCB_179 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_179 : (-248047794445697 / 1000000000000000 : ℝ) ≤ Real.log 179 * (ex (57436 / 100000) 179 * cCG cZ 179) ∧ Real.log 179 * (ex (57436 / 100000) 179 * cCG cZ 179) ≤ (-248047702891601 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_179 eC_179 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_181 : (324906064426761 / 62500000000000 : ℝ) ≤ Real.log 181 ∧ Real.log 181 ≤ (5198497032904177 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_181
  constructor <;> linarith [h.1, h.2]

theorem eC_181 : (-1679791045457 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 181 * cCG cZ 181 ∧ ex (57436 / 100000) 181 * cCG cZ 181 ≤ (-1679782309889 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_181 cCB_181 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_181 : (-25193388995969 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 181 * sCG cZ 181 ∧ ex (57436 / 100000) 181 * sCG cZ 181 ≤ (-50386760464709 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_181 sCB_181 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_181 : (-3492955506283 / 200000000000000 : ℝ) ≤ Real.log 181 * (ex (57436 / 100000) 181 * cCG cZ 181) ∧ Real.log 181 * (ex (57436 / 100000) 181 * cCG cZ 181) ≤ (-17464686700791 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_181 eC_181 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_182 : (2602003343319573 / 500000000000000 : ℝ) ≤ Real.log 182 ∧ Real.log 182 ≤ (2602003344357573 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_182
  constructor <;> linarith [h.1, h.2]

theorem eC_182 : (37840902315771 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 182 * cCG cZ 182 ∧ ex (57436 / 100000) 182 * cCG cZ 182 ≤ (37840919770141 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_182 cCB_182 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_182 : (5374903673961 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 182 * cCG cZ 182) ∧ kappa * (ex (57436 / 100000) 182 * cCG cZ 182) ≤ (1343726538293 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_182 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_182 : (-8299436898419 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 182 * sCG cZ 182 ∧ ex (57436 / 100000) 182 * sCG cZ 182 ≤ (-16598865073387 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_182 sCB_182 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_182 : (-9430784394067 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 182 * sCG cZ 182) ∧ kappa * (ex (57436 / 100000) 182 * sCG cZ 182) ≤ (-9430779437767 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_182 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_182 : (196924308679731 / 1000000000000000 : ℝ) ≤ Real.log 182 * (ex (57436 / 100000) 182 * cCG cZ 182) ∧ Real.log 182 * (ex (57436 / 100000) 182 * cCG cZ 182) ≤ (196924399590947 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_182 eC_182 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_182 : (3496379332417 / 62500000000000 : ℝ) ≤ kappa * (Real.log 182 * (ex (57436 / 100000) 182 * cCG cZ 182)) ∧ kappa * (Real.log 182 * (ex (57436 / 100000) 182 * cCG cZ 182)) ≤ (13985523786161 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_182 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_183 : (5209486152403771 / 1000000000000000 : ℝ) ≤ Real.log 183 ∧ Real.log 183 ≤ (1302371538619943 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_183
  constructor <;> linarith [h.1, h.2]

theorem eC_183 : (49257969597989 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 183 * cCG cZ 183 ∧ ex (57436 / 100000) 183 * cCG cZ 183 ≤ (24628993512089 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_183 cCB_183 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_183 : (3498289226229 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 183 * cCG cZ 183) ∧ kappa * (ex (57436 / 100000) 183 * cCG cZ 183) ≤ (3498290463833 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_183 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_183 : (9579969812039 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 183 * sCG cZ 183 ∧ ex (57436 / 100000) 183 * sCG cZ 183 ≤ (9579987190901 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_183 sCB_183 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_183 : (85045895757 / 31250000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 183 * sCG cZ 183) ∧ kappa * (ex (57436 / 100000) 183 * sCG cZ 183) ≤ (544294720239 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_183 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_183 : (256608710516249 / 1000000000000000 : ℝ) ≤ Real.log 183 * (ex (57436 / 100000) 183 * cCG cZ 183) ∧ Real.log 183 * (ex (57436 / 100000) 183 * cCG cZ 183) ≤ (1283044007 / 5000000000 : ℝ) := by
  exact mul_bounds_of lgB_183 eC_183 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_183 : (72897157124577 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 183 * (ex (57436 / 100000) 183 * cCG cZ 183)) ∧ kappa * (Real.log 183 * (ex (57436 / 100000) 183 * cCG cZ 183)) ≤ (72897182942747 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_183 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_184 : (651866969646417 / 125000000000000 : ℝ) ≤ Real.log 184 ∧ Real.log 184 ≤ (651866969905917 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_184
  constructor <;> linarith [h.1, h.2]

theorem eC_184 : (22720398281039 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 184 * cCG cZ 184 ∧ ex (57436 / 100000) 184 * cCG cZ 184 ≤ (2840051955121 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_184 cCB_184 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_184 : (44566717973437 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 184 * sCG cZ 184 ∧ ex (57436 / 100000) 184 * sCG cZ 184 ≤ (44566735359437 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_184 sCB_184 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_184 : (29621354353241 / 250000000000000 : ℝ) ≤ Real.log 184 * (ex (57436 / 100000) 184 * cCG cZ 184) ∧ Real.log 184 * (ex (57436 / 100000) 184 * cCG cZ 184) ≤ (118485507991047 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_184 eC_184 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_186 : (5225746673275551 / 1000000000000000 : ℝ) ≤ Real.log 186 ∧ Real.log 186 ≤ (318954264853 / 61035156250 : ℝ) := by
  have h := PsiOmega.Num.log_bound_186
  constructor <;> linarith [h.1, h.2]

theorem eC_186 : (-48260261489703 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 186 * cCG cZ 186 ∧ ex (57436 / 100000) 186 * cCG cZ 186 ≤ (-6032530529519 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_186 cCB_186 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_186 : (11936216249479 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 186 * sCG cZ 186 ∧ ex (57436 / 100000) 186 * sCG cZ 186 ≤ (11936233459703 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_186 sCB_186 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_186 : (-63048975257853 / 250000000000000 : ℝ) ≤ Real.log 186 * (ex (57436 / 100000) 186 * cCG cZ 186) ∧ Real.log 186 * (ex (57436 / 100000) 186 * cCG cZ 186) ≤ (-31524476346067 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_186 eC_186 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_187 : (5231108616416937 / 1000000000000000 : ℝ) ≤ Real.log 187 ∧ Real.log 187 ≤ (5231108618492937 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_187
  constructor <;> linarith [h.1, h.2]

theorem eC_187 : (-39449528137329 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 187 * cCG cZ 187 ∧ ex (57436 / 100000) 187 * cCG cZ 187 ≤ (-1232797216217 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_187 cCB_187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_187 : (-1400848029151 / 125000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 187 * cCG cZ 187) ∧ kappa * (ex (57436 / 100000) 187 * cCG cZ 187) ≤ (-448271173673 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_187 : (-30001418938759 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 187 * sCG cZ 187 ∧ ex (57436 / 100000) 187 * sCG cZ 187 ≤ (-6000280346441 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_187 sCB_187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_187 : (-8522774405979 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 187 * sCG cZ 187) ∧ kappa * (ex (57436 / 100000) 187 * sCG cZ 187) ≤ (-2130692379489 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_187 : (-103182383317331 / 500000000000000 : ℝ) ≤ Real.log 187 * (ex (57436 / 100000) 187 * cCG cZ 187) ∧ Real.log 187 * (ex (57436 / 100000) 187 * cCG cZ 187) ≤ (-206364676481521 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_187 eC_187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_187 : (-2344956223517 / 40000000000000 : ℝ) ≤ kappa * (Real.log 187 * (ex (57436 / 100000) 187 * cCG cZ 187)) ∧ kappa * (Real.log 187 * (ex (57436 / 100000) 187 * cCG cZ 187)) ≤ (-29311939988653 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_188 : (5236441962392299 / 1000000000000000 : ℝ) ≤ Real.log 188 ∧ Real.log 188 ≤ (52364419644683 / 10000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_188
  constructor <;> linarith [h.1, h.2]

theorem eC_188 : (-323247821049 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 188 * cCG cZ 188 ∧ ex (57436 / 100000) 188 * cCG cZ 188 ≤ (-404055500591 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_188 cCB_188 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_188 : (-114784914909 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 188 * cCG cZ 188) ∧ kappa * (ex (57436 / 100000) 188 * cCG cZ 188) ≤ (-91826960213 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_188 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_188 : (-49383549776043 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 188 * sCG cZ 188 ∧ ex (57436 / 100000) 188 * sCG cZ 188 ≤ (-9876706523237 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_188 sCB_188 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_188 : (-438400987557 / 31250000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 188 * sCG cZ 188) ∧ kappa * (ex (57436 / 100000) 188 * sCG cZ 188) ≤ (-14028826727067 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_188 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_188 : (-211583556883 / 25000000000000 : ℝ) ≤ Real.log 188 * (ex (57436 / 100000) 188 * cCG cZ 188) ∧ Real.log 188 * (ex (57436 / 100000) 188 * cCG cZ 188) ≤ (-211581317843 / 25000000000000 : ℝ) := by
  exact mul_bounds_of lgB_188 eC_188 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_188 : (-601064545317 / 250000000000000 : ℝ) ≤ kappa * (Real.log 188 * (ex (57436 / 100000) 188 * cCG cZ 188)) ∧ kappa * (Real.log 188 * (ex (57436 / 100000) 188 * cCG cZ 188)) ≤ (-2404232738693 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_188 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_189 : (5241747014621993 / 1000000000000000 : ℝ) ≤ Real.log 189 ∧ Real.log 189 ≤ (5241747016697993 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_189
  constructor <;> linarith [h.1, h.2]

theorem eC_189 : (37022920855997 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 189 * cCG cZ 189 ∧ ex (57436 / 100000) 189 * cCG cZ 189 ≤ (9255734489783 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_189 cCB_189 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_189 : (-32493341219539 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 189 * sCG cZ 189 ∧ ex (57436 / 100000) 189 * sCG cZ 189 ≤ (-16246662061851 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_189 sCB_189 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_189 : (48516196217377 / 250000000000000 : ℝ) ≤ Real.log 189 * (ex (57436 / 100000) 189 * cCG cZ 189) ∧ Real.log 189 * (ex (57436 / 100000) 189 * cCG cZ 189) ≤ (48516218649169 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_189 eC_189 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_191 : (262613671380449 / 50000000000000 : ℝ) ≤ Real.log 191 ∧ Real.log 191 ≤ (5252273429684981 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_191
  constructor <;> linarith [h.1, h.2]

theorem eC_191 : (2511878342411 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 191 * cCG cZ 191 ∧ ex (57436 / 100000) 191 * cCG cZ 191 ≤ (25118800402957 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_191 cCB_191 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_191 : (2101425149653 / 50000000000000 : ℝ) ≤ ex (57436 / 100000) 191 * sCG cZ 191 ∧ ex (57436 / 100000) 191 * sCG cZ 191 ≤ (5253564999017 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_191 sCB_191 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_191 : (131930718712317 / 1000000000000000 : ℝ) ≤ Real.log 191 * (ex (57436 / 100000) 191 * cCG cZ 191) ∧ Real.log 191 * (ex (57436 / 100000) 191 * cCG cZ 191) ≤ (32982701985503 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_191 eC_191 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_192 : (1314373842897533 / 250000000000000 : ℝ) ≤ Real.log 192 ∧ Real.log 192 ≤ (1314373843416533 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_192
  constructor <;> linarith [h.1, h.2]

theorem eC_192 : (-15848446159599 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 192 * cCG cZ 192 ∧ ex (57436 / 100000) 192 * cCG cZ 192 ≤ (-15848429227027 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_192 cCB_192 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_192 : (-281388214461 / 62500000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 192 * cCG cZ 192) ∧ kappa * (ex (57436 / 100000) 192 * cCG cZ 192) ≤ (-2251103310593 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_192 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_192 : (23085916408609 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 192 * sCG cZ 192 ∧ ex (57436 / 100000) 192 * sCG cZ 192 ≤ (46171849785961 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_192 sCB_192 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_192 : (6558225059537 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 192 * sCG cZ 192) ∧ kappa * (ex (57436 / 100000) 192 * sCG cZ 192) ≤ (13116454939539 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_192 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_192 : (-83323132363889 / 1000000000000000 : ℝ) ≤ Real.log 192 * (ex (57436 / 100000) 192 * cCG cZ 192) ∧ Real.log 192 * (ex (57436 / 100000) 192 * cCG cZ 192) ≤ (-20830760827017 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_192 eC_192 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_192 : (-11835177885861 / 500000000000000 : ℝ) ≤ kappa * (Real.log 192 * (ex (57436 / 100000) 192 * cCG cZ 192)) ∧ kappa * (Real.log 192 * (ex (57436 / 100000) 192 * cCG cZ 192)) ≤ (-23670330472829 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_192 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_193 : (1315672547116809 / 250000000000000 : ℝ) ≤ Real.log 193 ∧ Real.log 193 ≤ (1315672547635809 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_193
  constructor <;> linarith [h.1, h.2]

theorem eC_193 : (-9056549828183 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 193 * cCG cZ 193 ∧ ex (57436 / 100000) 193 * cCG cZ 193 ≤ (-5660341532631 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_193 cCB_193 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_193 : (-12863880078417 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 193 * cCG cZ 193) ∧ kappa * (ex (57436 / 100000) 193 * cCG cZ 193) ≤ (-12863875283199 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_193 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_193 : (8920579913327 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 193 * sCG cZ 193 ∧ ex (57436 / 100000) 193 * sCG cZ 193 ≤ (4460294168447 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_193 sCB_193 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_193 : (5068299624559 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 193 * sCG cZ 193) ∧ kappa * (ex (57436 / 100000) 193 * sCG cZ 193) ≤ (2534152205239 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_193 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_193 : (-59577269926181 / 250000000000000 : ℝ) ≤ Real.log 193 * (ex (57436 / 100000) 193 * cCG cZ 193) ∧ Real.log 193 * (ex (57436 / 100000) 193 * cCG cZ 193) ≤ (-119154495388603 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_193 eC_193 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_193 : (-67698615501007 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 193 * (ex (57436 / 100000) 193 * cCG cZ 193)) ∧ kappa * (Real.log 193 * (ex (57436 / 100000) 193 * cCG cZ 193)) ≤ (-33849295119281 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_193 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_194 : (2633929079312839 / 500000000000000 : ℝ) ≤ Real.log 194 ∧ Real.log 194 ≤ (5267858160701679 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_194
  constructor <;> linarith [h.1, h.2]

theorem eC_194 : (-21464588994521 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 194 * cCG cZ 194 ∧ ex (57436 / 100000) 194 * cCG cZ 194 ≤ (-21464580577127 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_194 cCB_194 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_194 : (-22625198942953 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 194 * sCG cZ 194 ∧ ex (57436 / 100000) 194 * sCG cZ 194 ≤ (-56562955331 / 2500000000000 : ℝ) := by
  exact mul_bounds_of exB_194 sCB_194 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_194 : (-22614482060179 / 100000000000000 : ℝ) ≤ Real.log 194 * (ex (57436 / 100000) 194 * cCG cZ 194) ∧ Real.log 194 * (ex (57436 / 100000) 194 * cCG cZ 194) ≤ (-226144731829393 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_194 eC_194 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_196 : (5278114658792867 / 1000000000000000 : ℝ) ≤ Real.log 196 ∧ Real.log 196 ≤ (1319528665217217 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_196
  constructor <;> linarith [h.1, h.2]

theorem eC_196 : (7024552230051 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 196 * cCG cZ 196 ∧ ex (57436 / 100000) 196 * cCG cZ 196 ≤ (5619645128779 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_196 cCB_196 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_196 : (-39213804234631 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 196 * sCG cZ 196 ∧ ex (57436 / 100000) 196 * sCG cZ 196 ≤ (-39213787497361 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_196 sCB_196 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_196 : (148305568387553 / 1000000000000000 : ℝ) ≤ Real.log 196 * (ex (57436 / 100000) 196 * cCG cZ 196) ∧ Real.log 196 * (ex (57436 / 100000) 196 * cCG cZ 196) ≤ (37076414178861 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_196 eC_196 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_197 : (5283203728300339 / 1000000000000000 : ℝ) ≤ Real.log 197 ∧ Real.log 197 ≤ (5283203730376339 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_197
  constructor <;> linarith [h.1, h.2]

theorem eC_197 : (23925700386943 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 197 * cCG cZ 197 ∧ ex (57436 / 100000) 197 * cCG cZ 197 ≤ (9570283500029 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_197 cCB_197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_197 : (13593580178269 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 197 * cCG cZ 197) ∧ kappa * (ex (57436 / 100000) 197 * cCG cZ 197) ≤ (271871698597 / 20000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_197 : (-4889704940829 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 197 * sCG cZ 197 ∧ ex (57436 / 100000) 197 * sCG cZ 197 ≤ (-4889688265817 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_197 sCB_197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_197 : (-1389062704253 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 197 * sCG cZ 197) ∧ kappa * (ex (57436 / 100000) 197 * sCG cZ 197) ≤ (-138905796723 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_197 : (63202174743247 / 250000000000000 : ℝ) ≤ Real.log 197 * (ex (57436 / 100000) 197 * cCG cZ 197) ∧ Real.log 197 * (ex (57436 / 100000) 197 * cCG cZ 197) ≤ (126404393720281 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_197 eC_197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_197 : (561075417803 / 7812500000000 : ℝ) ≤ kappa * (Real.log 197 * (ex (57436 / 100000) 197 * cCG cZ 197)) ∧ kappa * (Real.log 197 * (ex (57436 / 100000) 197 * cCG cZ 197)) ≤ (7181767861057 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_198 : (1057653406051377 / 200000000000000 : ℝ) ≤ Real.log 198 ∧ Real.log 198 ≤ (2644133516166443 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_198
  constructor <;> linarith [h.1, h.2]

theorem eC_198 : (35381906127941 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 198 * cCG cZ 198 ∧ ex (57436 / 100000) 198 * cCG cZ 198 ≤ (8845480697277 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_198 cCB_198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_198 : (2512814515519 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 198 * cCG cZ 198) ∧ kappa * (ex (57436 / 100000) 198 * cCG cZ 198) ≤ (5025631397583 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_198 : (16189256642781 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 198 * sCG cZ 198 ∧ ex (57436 / 100000) 198 * sCG cZ 198 ≤ (16189264970277 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_198 sCB_198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_198 : (287439284223 / 31250000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 198 * sCG cZ 198) ∧ kappa * (ex (57436 / 100000) 198 * sCG cZ 198) ≤ (9198061826471 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_198 : (93554483822017 / 500000000000000 : ℝ) ≤ Real.log 198 * (ex (57436 / 100000) 198 * cCG cZ 198) ∧ Real.log 198 * (ex (57436 / 100000) 198 * cCG cZ 198) ≤ (46777263956547 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_198 eC_198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_198 : (53153736622283 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 198 * (ex (57436 / 100000) 198 * cCG cZ 198)) ∧ kappa * (Real.log 198 * (ex (57436 / 100000) 198 * cCG cZ 198)) ≤ (26576880836493 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_199 : (5293304824286843 / 1000000000000000 : ℝ) ≤ Real.log 199 ∧ Real.log 199 ≤ (5293304826362843 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_199
  constructor <;> linarith [h.1, h.2]

theorem eC_199 : (-430193420331 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 199 * cCG cZ 199 ∧ ex (57436 / 100000) 199 * cCG cZ 199 ≤ (-430176874043 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_199 cCB_199 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_199 : (9564077687303 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 199 * sCG cZ 199 ∧ ex (57436 / 100000) 199 * sCG cZ 199 ≤ (23910202519667 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_199 sCB_199 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_199 : (-569286227027 / 250000000000000 : ℝ) ≤ Real.log 199 * (ex (57436 / 100000) 199 * cCG cZ 199) ∧ Real.log 199 * (ex (57436 / 100000) 199 * cCG cZ 199) ≤ (-569264330667 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_199 eC_199 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_201 : (2651652453810713 / 500000000000000 : ℝ) ≤ Real.log 201 ∧ Real.log 201 ≤ (5303304909697427 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_201
  constructor <;> linarith [h.1, h.2]

theorem eC_201 : (-9459284837187 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 201 * cCG cZ 201 ∧ ex (57436 / 100000) 201 * cCG cZ 201 ≤ (-4729640764893 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_201 cCB_201 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_201 : (-4889138861053 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 201 * sCG cZ 201 ∧ ex (57436 / 100000) 201 * sCG cZ 201 ≤ (-1222280593659 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_201 sCB_201 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_201 : (-125413679298201 / 500000000000000 : ℝ) ≤ Real.log 201 * (ex (57436 / 100000) 201 * cCG cZ 201) ∧ Real.log 201 * (ex (57436 / 100000) 201 * cCG cZ 201) ≤ (-125413635398717 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_201 eC_201 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_202 : (1061653539392711 / 200000000000000 : ℝ) ≤ Real.log 202 ∧ Real.log 202 ≤ (1327066924759889 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_202
  constructor <;> linarith [h.1, h.2]

theorem eC_202 : (-5675053162937 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 202 * cCG cZ 202 ∧ ex (57436 / 100000) 202 * cCG cZ 202 ≤ (-3546906173573 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_202 cCB_202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_202 : (-4030409190677 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 202 * cCG cZ 202) ∧ kappa * (ex (57436 / 100000) 202 * cCG cZ 202) ≤ (-4030406857521 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_202 : (-18992418232641 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 202 * sCG cZ 202 ∧ ex (57436 / 100000) 202 * sCG cZ 202 ≤ (-37984820027261 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_202 sCB_202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_202 : (-2697674005873 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 202 * sCG cZ 202) ∧ kappa * (ex (57436 / 100000) 202 * sCG cZ 202) ≤ (-5395345676897 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_202 : (-75311753487877 / 500000000000000 : ℝ) ≤ Real.log 202 * (ex (57436 / 100000) 202 * cCG cZ 202) ∧ Real.log 202 * (ex (57436 / 100000) 202 * cCG cZ 202) ≤ (-30124683944541 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_202 eC_202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_202 : (-21394490920781 / 500000000000000 : ℝ) ≤ kappa * (Real.log 202 * (ex (57436 / 100000) 202 * cCG cZ 202)) ∧ kappa * (Real.log 202 * (ex (57436 / 100000) 202 * cCG cZ 202)) ≤ (-42788957054799 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_203 : (2656602989302069 / 500000000000000 : ℝ) ≤ Real.log 203 ∧ Real.log 203 ≤ (2656602990340069 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_203
  constructor <;> linarith [h.1, h.2]

theorem eC_203 : (848910730651 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 203 * cCG cZ 203 ∧ ex (57436 / 100000) 203 * cCG cZ 203 ≤ (1061140459103 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_203 cCB_203 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_203 : (602894371673 / 250000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 203 * cCG cZ 203) ∧ kappa * (ex (57436 / 100000) 203 * cCG cZ 203) ≤ (2411582136019 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_203 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_203 : (-46510449945559 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 203 * sCG cZ 203 ∧ ex (57436 / 100000) 203 * sCG cZ 203 ≤ (-4651043353389 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_203 sCB_203 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_203 : (-6606322074561 / 500000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 203 * sCG cZ 203) ∧ kappa * (ex (57436 / 100000) 203 * sCG cZ 203) ≤ (-1321263948691 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_203 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_203 : (45104375693961 / 1000000000000000 : ℝ) ≤ Real.log 203 * (ex (57436 / 100000) 203 * cCG cZ 203) ∧ Real.log 203 * (ex (57436 / 100000) 203 * cCG cZ 203) ≤ (22552231334591 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_203 eC_203 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_203 : (12813207920159 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 203 * (ex (57436 / 100000) 203 * cCG cZ 203)) ∧ kappa * (Real.log 203 * (ex (57436 / 100000) 203 * cCG cZ 203)) ≤ (12813232627997 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_203 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_204 : (5318119993406567 / 1000000000000000 : ℝ) ≤ Real.log 204 ∧ Real.log 204 ≤ (5318119995482567 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_204
  constructor <;> linarith [h.1, h.2]

theorem eC_204 : (4954537639663 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 204 * cCG cZ 204 ∧ ex (57436 / 100000) 204 * cCG cZ 204 ≤ (39636317460019 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_204 cCB_204 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_204 : (-12763888676713 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 204 * sCG cZ 204 ∧ ex (57436 / 100000) 204 * sCG cZ 204 ≤ (-25527761027657 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_204 sCB_204 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_204 : (210790605436617 / 1000000000000000 : ℝ) ≤ Real.log 204 * (ex (57436 / 100000) 204 * cCG cZ 204) ∧ Real.log 204 * (ex (57436 / 100000) 204 * cCG cZ 204) ≤ (105395346215711 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_204 eC_204 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_206 : (5327876168351931 / 1000000000000000 : ℝ) ≤ Real.log 206 ∧ Real.log 206 ≤ (1331969042606983 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_206
  constructor <;> linarith [h.1, h.2]

theorem lgB_207 : (5332718792827719 / 1000000000000000 : ℝ) ≤ Real.log 207 ∧ Real.log 207 ≤ (133317969872593 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_207
  constructor <;> linarith [h.1, h.2]

theorem lgB_208 : (1334384519815917 / 250000000000000 : ℝ) ≤ Real.log 208 ∧ Real.log 208 ≤ (5337538081339669 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_208
  constructor <;> linarith [h.1, h.2]

theorem lgB_209 : (5342334251527161 / 1000000000000000 : ℝ) ≤ Real.log 209 ∧ Real.log 209 ≤ (2671167126801581 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_209
  constructor <;> linarith [h.1, h.2]

theorem PReB_0 : (809081692868633 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 1 * cCG cZ 1 + kappa * (ex (57436 / 100000) 2 * cCG cZ 2) - kappa * (ex (57436 / 100000) 3 * cCG cZ 3) - ex (57436 / 100000) 4 * cCG cZ 4 ∧ ex (57436 / 100000) 1 * cCG cZ 1 + kappa * (ex (57436 / 100000) 2 * cCG cZ 2) - kappa * (ex (57436 / 100000) 3 * cCG cZ 3) - ex (57436 / 100000) 4 * cCG cZ 4 ≤ (202270432066163 / 250000000000000 : ℝ) := by
  have h0 : ex (57436 / 100000) 1 * cCG cZ 1 = (1 : ℝ) := by rw [ex_oneG, cCG_one]; norm_num
  have h1 := keC_2
  have h2 := keC_3
  have h3 := eC_4
  constructor <;> linarith [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_1 : (-567055951769837 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 6 * cCG cZ 6 + kappa * (ex (57436 / 100000) 7 * cCG cZ 7) - kappa * (ex (57436 / 100000) 8 * cCG cZ 8) - ex (57436 / 100000) 9 * cCG cZ 9 ∧ ex (57436 / 100000) 6 * cCG cZ 6 + kappa * (ex (57436 / 100000) 7 * cCG cZ 7) - kappa * (ex (57436 / 100000) 8 * cCG cZ 8) - ex (57436 / 100000) 9 * cCG cZ 9 ≤ (-567055898085037 / 1000000000000000 : ℝ) := by
  have h0 := eC_6
  have h1 := keC_7
  have h2 := keC_8
  have h3 := eC_9
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_2 : (-468277930785753 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 11 * cCG cZ 11 + kappa * (ex (57436 / 100000) 12 * cCG cZ 12) - kappa * (ex (57436 / 100000) 13 * cCG cZ 13) - ex (57436 / 100000) 14 * cCG cZ 14 ∧ ex (57436 / 100000) 11 * cCG cZ 11 + kappa * (ex (57436 / 100000) 12 * cCG cZ 12) - kappa * (ex (57436 / 100000) 13 * cCG cZ 13) - ex (57436 / 100000) 14 * cCG cZ 14 ≤ (-58534735744077 / 125000000000000 : ℝ) := by
  have h0 := eC_11
  have h1 := keC_12
  have h2 := keC_13
  have h3 := eC_14
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_3 : (-17734379083691 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 16 * cCG cZ 16 + kappa * (ex (57436 / 100000) 17 * cCG cZ 17) - kappa * (ex (57436 / 100000) 18 * cCG cZ 18) - ex (57436 / 100000) 19 * cCG cZ 19 ∧ ex (57436 / 100000) 16 * cCG cZ 16 + kappa * (ex (57436 / 100000) 17 * cCG cZ 17) - kappa * (ex (57436 / 100000) 18 * cCG cZ 18) - ex (57436 / 100000) 19 * cCG cZ 19 ≤ (-283750018271927 / 1000000000000000 : ℝ) := by
  have h0 := eC_16
  have h1 := keC_17
  have h2 := keC_18
  have h3 := eC_19
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_4 : (-66345044718787 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 21 * cCG cZ 21 + kappa * (ex (57436 / 100000) 22 * cCG cZ 22) - kappa * (ex (57436 / 100000) 23 * cCG cZ 23) - ex (57436 / 100000) 24 * cCG cZ 24 ∧ ex (57436 / 100000) 21 * cCG cZ 21 + kappa * (ex (57436 / 100000) 22 * cCG cZ 22) - kappa * (ex (57436 / 100000) 23 * cCG cZ 23) - ex (57436 / 100000) 24 * cCG cZ 24 ≤ (-8293127675941 / 62500000000000 : ℝ) := by
  have h0 := eC_21
  have h1 := keC_22
  have h2 := keC_23
  have h3 := eC_24
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_5 : (-107730830949401 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 26 * cCG cZ 26 + kappa * (ex (57436 / 100000) 27 * cCG cZ 27) - kappa * (ex (57436 / 100000) 28 * cCG cZ 28) - ex (57436 / 100000) 29 * cCG cZ 29 ∧ ex (57436 / 100000) 26 * cCG cZ 26 + kappa * (ex (57436 / 100000) 27 * cCG cZ 27) - kappa * (ex (57436 / 100000) 28 * cCG cZ 28) - ex (57436 / 100000) 29 * cCG cZ 29 ≤ (-13466348554763 / 125000000000000 : ℝ) := by
  have h0 := eC_26
  have h1 := keC_27
  have h2 := keC_28
  have h3 := eC_29
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_6 : (18845825153529 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 31 * cCG cZ 31 + kappa * (ex (57436 / 100000) 32 * cCG cZ 32) - kappa * (ex (57436 / 100000) 33 * cCG cZ 33) - ex (57436 / 100000) 34 * cCG cZ 34 ∧ ex (57436 / 100000) 31 * cCG cZ 31 + kappa * (ex (57436 / 100000) 32 * cCG cZ 32) - kappa * (ex (57436 / 100000) 33 * cCG cZ 33) - ex (57436 / 100000) 34 * cCG cZ 34 ≤ (30153324143003 / 100000000000000 : ℝ) := by
  have h0 := eC_31
  have h1 := keC_32
  have h2 := keC_33
  have h3 := eC_34
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_7 : (5093320988991 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 36 * cCG cZ 36 + kappa * (ex (57436 / 100000) 37 * cCG cZ 37) - kappa * (ex (57436 / 100000) 38 * cCG cZ 38) - ex (57436 / 100000) 39 * cCG cZ 39 ∧ ex (57436 / 100000) 36 * cCG cZ 36 + kappa * (ex (57436 / 100000) 37 * cCG cZ 37) - kappa * (ex (57436 / 100000) 38 * cCG cZ 38) - ex (57436 / 100000) 39 * cCG cZ 39 ≤ (10186659961469 / 500000000000000 : ℝ) := by
  have h0 := eC_36
  have h1 := keC_37
  have h2 := keC_38
  have h3 := eC_39
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_8 : (-1975787494723 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 41 * cCG cZ 41 + kappa * (ex (57436 / 100000) 42 * cCG cZ 42) - kappa * (ex (57436 / 100000) 43 * cCG cZ 43) - ex (57436 / 100000) 44 * cCG cZ 44 ∧ ex (57436 / 100000) 41 * cCG cZ 41 + kappa * (ex (57436 / 100000) 42 * cCG cZ 42) - kappa * (ex (57436 / 100000) 43 * cCG cZ 43) - ex (57436 / 100000) 44 * cCG cZ 44 ≤ (-31612566498527 / 1000000000000000 : ℝ) := by
  have h0 := eC_41
  have h1 := keC_42
  have h2 := keC_43
  have h3 := eC_44
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_9 : (-31088296532839 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 46 * cCG cZ 46 + kappa * (ex (57436 / 100000) 47 * cCG cZ 47) - kappa * (ex (57436 / 100000) 48 * cCG cZ 48) - ex (57436 / 100000) 49 * cCG cZ 49 ∧ ex (57436 / 100000) 46 * cCG cZ 46 + kappa * (ex (57436 / 100000) 47 * cCG cZ 47) - kappa * (ex (57436 / 100000) 48 * cCG cZ 48) - ex (57436 / 100000) 49 * cCG cZ 49 ≤ (-62176577381599 / 500000000000000 : ℝ) := by
  have h0 := eC_46
  have h1 := keC_47
  have h2 := keC_48
  have h3 := eC_49
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_10 : (61900960762917 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 51 * cCG cZ 51 + kappa * (ex (57436 / 100000) 52 * cCG cZ 52) - kappa * (ex (57436 / 100000) 53 * cCG cZ 53) - ex (57436 / 100000) 54 * cCG cZ 54 ∧ ex (57436 / 100000) 51 * cCG cZ 51 + kappa * (ex (57436 / 100000) 52 * cCG cZ 52) - kappa * (ex (57436 / 100000) 53 * cCG cZ 53) - ex (57436 / 100000) 54 * cCG cZ 54 ≤ (61900990422533 / 1000000000000000 : ℝ) := by
  have h0 := eC_51
  have h1 := keC_52
  have h2 := keC_53
  have h3 := eC_54
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_11 : (-105218223732281 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 56 * cCG cZ 56 + kappa * (ex (57436 / 100000) 57 * cCG cZ 57) - kappa * (ex (57436 / 100000) 58 * cCG cZ 58) - ex (57436 / 100000) 59 * cCG cZ 59 ∧ ex (57436 / 100000) 56 * cCG cZ 56 + kappa * (ex (57436 / 100000) 57 * cCG cZ 57) - kappa * (ex (57436 / 100000) 58 * cCG cZ 58) - ex (57436 / 100000) 59 * cCG cZ 59 ≤ (-105218192097921 / 1000000000000000 : ℝ) := by
  have h0 := eC_56
  have h1 := keC_57
  have h2 := keC_58
  have h3 := eC_59
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_12 : (1243746840403 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 61 * cCG cZ 61 + kappa * (ex (57436 / 100000) 62 * cCG cZ 62) - kappa * (ex (57436 / 100000) 63 * cCG cZ 63) - ex (57436 / 100000) 64 * cCG cZ 64 ∧ ex (57436 / 100000) 61 * cCG cZ 61 + kappa * (ex (57436 / 100000) 62 * cCG cZ 62) - kappa * (ex (57436 / 100000) 63 * cCG cZ 63) - ex (57436 / 100000) 64 * cCG cZ 64 ≤ (31093715684863 / 1000000000000000 : ℝ) := by
  have h0 := eC_61
  have h1 := keC_62
  have h2 := keC_63
  have h3 := eC_64
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_13 : (27048841530433 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 66 * cCG cZ 66 + kappa * (ex (57436 / 100000) 67 * cCG cZ 67) - kappa * (ex (57436 / 100000) 68 * cCG cZ 68) - ex (57436 / 100000) 69 * cCG cZ 69 ∧ ex (57436 / 100000) 66 * cCG cZ 66 + kappa * (ex (57436 / 100000) 67 * cCG cZ 67) - kappa * (ex (57436 / 100000) 68 * cCG cZ 68) - ex (57436 / 100000) 69 * cCG cZ 69 ≤ (5409778949879 / 200000000000000 : ℝ) := by
  have h0 := eC_66
  have h1 := keC_67
  have h2 := keC_68
  have h3 := eC_69
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_14 : (126187440579 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 71 * cCG cZ 71 + kappa * (ex (57436 / 100000) 72 * cCG cZ 72) - kappa * (ex (57436 / 100000) 73 * cCG cZ 73) - ex (57436 / 100000) 74 * cCG cZ 74 ∧ ex (57436 / 100000) 71 * cCG cZ 71 + kappa * (ex (57436 / 100000) 72 * cCG cZ 72) - kappa * (ex (57436 / 100000) 73 * cCG cZ 73) - ex (57436 / 100000) 74 * cCG cZ 74 ≤ (126245460869 / 1000000000000000 : ℝ) := by
  have h0 := eC_71
  have h1 := keC_72
  have h2 := keC_73
  have h3 := eC_74
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_15 : (27720949952129 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 76 * cCG cZ 76 + kappa * (ex (57436 / 100000) 77 * cCG cZ 77) - kappa * (ex (57436 / 100000) 78 * cCG cZ 78) - ex (57436 / 100000) 79 * cCG cZ 79 ∧ ex (57436 / 100000) 76 * cCG cZ 76 + kappa * (ex (57436 / 100000) 77 * cCG cZ 77) - kappa * (ex (57436 / 100000) 78 * cCG cZ 78) - ex (57436 / 100000) 79 * cCG cZ 79 ≤ (27721010354899 / 1000000000000000 : ℝ) := by
  have h0 := eC_76
  have h1 := keC_77
  have h2 := keC_78
  have h3 := eC_79
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_16 : (-14253895448143 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 81 * cCG cZ 81 + kappa * (ex (57436 / 100000) 82 * cCG cZ 82) - kappa * (ex (57436 / 100000) 83 * cCG cZ 83) - ex (57436 / 100000) 84 * cCG cZ 84 ∧ ex (57436 / 100000) 81 * cCG cZ 81 + kappa * (ex (57436 / 100000) 82 * cCG cZ 82) - kappa * (ex (57436 / 100000) 83 * cCG cZ 83) - ex (57436 / 100000) 84 * cCG cZ 84 ≤ (-28507729292737 / 1000000000000000 : ℝ) := by
  have h0 := eC_81
  have h1 := keC_82
  have h2 := keC_83
  have h3 := eC_84
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_17 : (6057153251491 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 86 * cCG cZ 86 + kappa * (ex (57436 / 100000) 87 * cCG cZ 87) - kappa * (ex (57436 / 100000) 88 * cCG cZ 88) - ex (57436 / 100000) 89 * cCG cZ 89 ∧ ex (57436 / 100000) 86 * cCG cZ 86 + kappa * (ex (57436 / 100000) 87 * cCG cZ 87) - kappa * (ex (57436 / 100000) 88 * cCG cZ 88) - ex (57436 / 100000) 89 * cCG cZ 89 ≤ (6057184225649 / 500000000000000 : ℝ) := by
  have h0 := eC_86
  have h1 := keC_87
  have h2 := keC_88
  have h3 := eC_89
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_18 : (-30640750357941 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 91 * cCG cZ 91 + kappa * (ex (57436 / 100000) 92 * cCG cZ 92) - kappa * (ex (57436 / 100000) 93 * cCG cZ 93) - ex (57436 / 100000) 94 * cCG cZ 94 ∧ ex (57436 / 100000) 91 * cCG cZ 91 + kappa * (ex (57436 / 100000) 92 * cCG cZ 92) - kappa * (ex (57436 / 100000) 93 * cCG cZ 93) - ex (57436 / 100000) 94 * cCG cZ 94 ≤ (-6128137734161 / 200000000000000 : ℝ) := by
  have h0 := eC_91
  have h1 := keC_92
  have h2 := keC_93
  have h3 := eC_94
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_19 : (18245694894717 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 96 * cCG cZ 96 + kappa * (ex (57436 / 100000) 97 * cCG cZ 97) - kappa * (ex (57436 / 100000) 98 * cCG cZ 98) - ex (57436 / 100000) 99 * cCG cZ 99 ∧ ex (57436 / 100000) 96 * cCG cZ 96 + kappa * (ex (57436 / 100000) 97 * cCG cZ 97) - kappa * (ex (57436 / 100000) 98 * cCG cZ 98) - ex (57436 / 100000) 99 * cCG cZ 99 ≤ (912285354639 / 10000000000000 : ℝ) := by
  have h0 := eC_96
  have h1 := keC_97
  have h2 := keC_98
  have h3 := eC_99
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_20 : (-13081801024857 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 101 * cCG cZ 101 + kappa * (ex (57436 / 100000) 102 * cCG cZ 102) - kappa * (ex (57436 / 100000) 103 * cCG cZ 103) - ex (57436 / 100000) 104 * cCG cZ 104 ∧ ex (57436 / 100000) 101 * cCG cZ 101 + kappa * (ex (57436 / 100000) 102 * cCG cZ 102) - kappa * (ex (57436 / 100000) 103 * cCG cZ 103) - ex (57436 / 100000) 104 * cCG cZ 104 ≤ (-52327173979939 / 500000000000000 : ℝ) := by
  have h0 := eC_101
  have h1 := keC_102
  have h2 := keC_103
  have h3 := eC_104
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_21 : (-1050238572871 / 20000000000000 : ℝ) ≤ ex (57436 / 100000) 106 * cCG cZ 106 + kappa * (ex (57436 / 100000) 107 * cCG cZ 107) - kappa * (ex (57436 / 100000) 108 * cCG cZ 108) - ex (57436 / 100000) 109 * cCG cZ 109 ∧ ex (57436 / 100000) 106 * cCG cZ 106 + kappa * (ex (57436 / 100000) 107 * cCG cZ 107) - kappa * (ex (57436 / 100000) 108 * cCG cZ 108) - ex (57436 / 100000) 109 * cCG cZ 109 ≤ (-26255934592759 / 500000000000000 : ℝ) := by
  have h0 := eC_106
  have h1 := keC_107
  have h2 := keC_108
  have h3 := eC_109
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_22 : (99347302648721 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 111 * cCG cZ 111 + kappa * (ex (57436 / 100000) 112 * cCG cZ 112) - kappa * (ex (57436 / 100000) 113 * cCG cZ 113) - ex (57436 / 100000) 114 * cCG cZ 114 ∧ ex (57436 / 100000) 111 * cCG cZ 111 + kappa * (ex (57436 / 100000) 112 * cCG cZ 112) - kappa * (ex (57436 / 100000) 113 * cCG cZ 113) - ex (57436 / 100000) 114 * cCG cZ 114 ≤ (49673680536679 / 500000000000000 : ℝ) := by
  have h0 := eC_111
  have h1 := keC_112
  have h2 := keC_113
  have h3 := eC_114
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_23 : (12992184605617 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 116 * cCG cZ 116 + kappa * (ex (57436 / 100000) 117 * cCG cZ 117) - kappa * (ex (57436 / 100000) 118 * cCG cZ 118) - ex (57436 / 100000) 119 * cCG cZ 119 ∧ ex (57436 / 100000) 116 * cCG cZ 116 + kappa * (ex (57436 / 100000) 117 * cCG cZ 117) - kappa * (ex (57436 / 100000) 118 * cCG cZ 118) - ex (57436 / 100000) 119 * cCG cZ 119 ≤ (8120118967291 / 62500000000000 : ℝ) := by
  have h0 := eC_116
  have h1 := keC_117
  have h2 := keC_118
  have h3 := eC_119
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_24 : (41937602177253 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 121 * cCG cZ 121 + kappa * (ex (57436 / 100000) 122 * cCG cZ 122) - kappa * (ex (57436 / 100000) 123 * cCG cZ 123) - ex (57436 / 100000) 124 * cCG cZ 124 ∧ ex (57436 / 100000) 121 * cCG cZ 121 + kappa * (ex (57436 / 100000) 122 * cCG cZ 122) - kappa * (ex (57436 / 100000) 123 * cCG cZ 123) - ex (57436 / 100000) 124 * cCG cZ 124 ≤ (41937630332581 / 500000000000000 : ℝ) := by
  have h0 := eC_121
  have h1 := keC_122
  have h2 := keC_123
  have h3 := eC_124
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_25 : (2424632959451 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 126 * cCG cZ 126 + kappa * (ex (57436 / 100000) 127 * cCG cZ 127) - kappa * (ex (57436 / 100000) 128 * cCG cZ 128) - ex (57436 / 100000) 129 * cCG cZ 129 ∧ ex (57436 / 100000) 126 * cCG cZ 126 + kappa * (ex (57436 / 100000) 127 * cCG cZ 127) - kappa * (ex (57436 / 100000) 128 * cCG cZ 128) - ex (57436 / 100000) 129 * cCG cZ 129 ≤ (1212318196767 / 31250000000000 : ℝ) := by
  have h0 := eC_126
  have h1 := keC_127
  have h2 := keC_128
  have h3 := eC_129
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_26 : (11306571550429 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 131 * cCG cZ 131 + kappa * (ex (57436 / 100000) 132 * cCG cZ 132) - kappa * (ex (57436 / 100000) 133 * cCG cZ 133) - ex (57436 / 100000) 134 * cCG cZ 134 ∧ ex (57436 / 100000) 131 * cCG cZ 131 + kappa * (ex (57436 / 100000) 132 * cCG cZ 132) - kappa * (ex (57436 / 100000) 133 * cCG cZ 133) - ex (57436 / 100000) 134 * cCG cZ 134 ≤ (22613196886143 / 1000000000000000 : ℝ) := by
  have h0 := eC_131
  have h1 := keC_132
  have h2 := keC_133
  have h3 := eC_134
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_27 : (37470445609017 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 136 * cCG cZ 136 + kappa * (ex (57436 / 100000) 137 * cCG cZ 137) - kappa * (ex (57436 / 100000) 138 * cCG cZ 138) - ex (57436 / 100000) 139 * cCG cZ 139 ∧ ex (57436 / 100000) 136 * cCG cZ 136 + kappa * (ex (57436 / 100000) 137 * cCG cZ 137) - kappa * (ex (57436 / 100000) 138 * cCG cZ 138) - ex (57436 / 100000) 139 * cCG cZ 139 ≤ (37470498232499 / 1000000000000000 : ℝ) := by
  have h0 := eC_136
  have h1 := keC_137
  have h2 := keC_138
  have h3 := eC_139
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_28 : (76730025725251 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 141 * cCG cZ 141 + kappa * (ex (57436 / 100000) 142 * cCG cZ 142) - kappa * (ex (57436 / 100000) 143 * cCG cZ 143) - ex (57436 / 100000) 144 * cCG cZ 144 ∧ ex (57436 / 100000) 141 * cCG cZ 141 + kappa * (ex (57436 / 100000) 142 * cCG cZ 142) - kappa * (ex (57436 / 100000) 143 * cCG cZ 143) - ex (57436 / 100000) 144 * cCG cZ 144 ≤ (19182519335987 / 250000000000000 : ℝ) := by
  have h0 := eC_141
  have h1 := keC_142
  have h2 := keC_143
  have h3 := eC_144
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_29 : (59618325549747 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 146 * cCG cZ 146 + kappa * (ex (57436 / 100000) 147 * cCG cZ 147) - kappa * (ex (57436 / 100000) 148 * cCG cZ 148) - ex (57436 / 100000) 149 * cCG cZ 149 ∧ ex (57436 / 100000) 146 * cCG cZ 146 + kappa * (ex (57436 / 100000) 147 * cCG cZ 147) - kappa * (ex (57436 / 100000) 148 * cCG cZ 148) - ex (57436 / 100000) 149 * cCG cZ 149 ≤ (59618350883897 / 500000000000000 : ℝ) := by
  have h0 := eC_146
  have h1 := keC_147
  have h2 := keC_148
  have h3 := eC_149
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_30 : (15130986037119 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 151 * cCG cZ 151 + kappa * (ex (57436 / 100000) 152 * cCG cZ 152) - kappa * (ex (57436 / 100000) 153 * cCG cZ 153) - ex (57436 / 100000) 154 * cCG cZ 154 ∧ ex (57436 / 100000) 151 * cCG cZ 151 + kappa * (ex (57436 / 100000) 152 * cCG cZ 152) - kappa * (ex (57436 / 100000) 153 * cCG cZ 153) - ex (57436 / 100000) 154 * cCG cZ 154 ≤ (121047937925279 / 1000000000000000 : ℝ) := by
  have h0 := eC_151
  have h1 := keC_152
  have h2 := keC_153
  have h3 := eC_154
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_31 : (41285174226469 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 156 * cCG cZ 156 + kappa * (ex (57436 / 100000) 157 * cCG cZ 157) - kappa * (ex (57436 / 100000) 158 * cCG cZ 158) - ex (57436 / 100000) 159 * cCG cZ 159 ∧ ex (57436 / 100000) 156 * cCG cZ 156 + kappa * (ex (57436 / 100000) 157 * cCG cZ 157) - kappa * (ex (57436 / 100000) 158 * cCG cZ 158) - ex (57436 / 100000) 159 * cCG cZ 159 ≤ (41285222893251 / 1000000000000000 : ℝ) := by
  have h0 := eC_156
  have h1 := keC_157
  have h2 := keC_158
  have h3 := eC_159
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_32 : (-3311691980903 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 161 * cCG cZ 161 + kappa * (ex (57436 / 100000) 162 * cCG cZ 162) - kappa * (ex (57436 / 100000) 163 * cCG cZ 163) - ex (57436 / 100000) 164 * cCG cZ 164 ∧ ex (57436 / 100000) 161 * cCG cZ 161 + kappa * (ex (57436 / 100000) 162 * cCG cZ 162) - kappa * (ex (57436 / 100000) 163 * cCG cZ 163) - ex (57436 / 100000) 164 * cCG cZ 164 ≤ (-41396125831127 / 500000000000000 : ℝ) := by
  have h0 := eC_161
  have h1 := keC_162
  have h2 := keC_163
  have h3 := eC_164
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_33 : (-109660873529487 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 166 * cCG cZ 166 + kappa * (ex (57436 / 100000) 167 * cCG cZ 167) - kappa * (ex (57436 / 100000) 168 * cCG cZ 168) - ex (57436 / 100000) 169 * cCG cZ 169 ∧ ex (57436 / 100000) 166 * cCG cZ 166 + kappa * (ex (57436 / 100000) 167 * cCG cZ 167) - kappa * (ex (57436 / 100000) 168 * cCG cZ 168) - ex (57436 / 100000) 169 * cCG cZ 169 ≤ (-109660826478441 / 1000000000000000 : ℝ) := by
  have h0 := eC_166
  have h1 := keC_167
  have h2 := keC_168
  have h3 := eC_169
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_34 : (3254509354481 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 171 * cCG cZ 171 + kappa * (ex (57436 / 100000) 172 * cCG cZ 172) - kappa * (ex (57436 / 100000) 173 * cCG cZ 173) - ex (57436 / 100000) 174 * cCG cZ 174 ∧ ex (57436 / 100000) 171 * cCG cZ 171 + kappa * (ex (57436 / 100000) 172 * cCG cZ 172) - kappa * (ex (57436 / 100000) 173 * cCG cZ 173) - ex (57436 / 100000) 174 * cCG cZ 174 ≤ (6509030264803 / 250000000000000 : ℝ) := by
  have h0 := eC_171
  have h1 := keC_172
  have h2 := keC_173
  have h3 := eC_174
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_35 : (56022205741283 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 176 * cCG cZ 176 + kappa * (ex (57436 / 100000) 177 * cCG cZ 177) - kappa * (ex (57436 / 100000) 178 * cCG cZ 178) - ex (57436 / 100000) 179 * cCG cZ 179 ∧ ex (57436 / 100000) 176 * cCG cZ 176 + kappa * (ex (57436 / 100000) 177 * cCG cZ 177) - kappa * (ex (57436 / 100000) 178 * cCG cZ 178) - ex (57436 / 100000) 179 * cCG cZ 179 ≤ (112044457005263 / 1000000000000000 : ℝ) := by
  have h0 := eC_176
  have h1 := keC_177
  have h2 := keC_178
  have h3 := eC_179
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_36 : (-7330838059823 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 181 * cCG cZ 181 + kappa * (ex (57436 / 100000) 182 * cCG cZ 182) - kappa * (ex (57436 / 100000) 183 * cCG cZ 183) - ex (57436 / 100000) 184 * cCG cZ 184 ∧ ex (57436 / 100000) 181 * cCG cZ 181 + kappa * (ex (57436 / 100000) 182 * cCG cZ 182) - kappa * (ex (57436 / 100000) 183 * cCG cZ 183) - ex (57436 / 100000) 184 * cCG cZ 184 ≤ (-29323307499389 / 1000000000000000 : ℝ) := by
  have h0 := eC_181
  have h1 := keC_182
  have h2 := keC_183
  have h3 := eC_184
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_37 : (-48015424440489 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 186 * cCG cZ 186 + kappa * (ex (57436 / 100000) 187 * cCG cZ 187) - kappa * (ex (57436 / 100000) 188 * cCG cZ 188) - ex (57436 / 100000) 189 * cCG cZ 189 ∧ ex (57436 / 100000) 186 * cCG cZ 186 + kappa * (ex (57436 / 100000) 187 * cCG cZ 187) - kappa * (ex (57436 / 100000) 188 * cCG cZ 188) - ex (57436 / 100000) 189 * cCG cZ 189 ≤ (-48015402387169 / 500000000000000 : ℝ) := by
  have h0 := eC_186
  have h1 := keC_187
  have h2 := keC_188
  have h3 := eC_189
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_38 : (76409608430187 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 191 * cCG cZ 191 + kappa * (ex (57436 / 100000) 192 * cCG cZ 192) - kappa * (ex (57436 / 100000) 193 * cCG cZ 193) - ex (57436 / 100000) 194 * cCG cZ 194 ∧ ex (57436 / 100000) 191 * cCG cZ 191 + kappa * (ex (57436 / 100000) 192 * cCG cZ 192) - kappa * (ex (57436 / 100000) 193 * cCG cZ 193) - ex (57436 / 100000) 194 * cCG cZ 194 ≤ (7640965184923 / 100000000000000 : ℝ) := by
  have h0 := eC_191
  have h1 := keC_192
  have h2 := keC_193
  have h3 := eC_194
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_39 : (641414063547 / 20000000000000 : ℝ) ≤ ex (57436 / 100000) 196 * cCG cZ 196 + kappa * (ex (57436 / 100000) 197 * cCG cZ 197) - kappa * (ex (57436 / 100000) 198 * cCG cZ 198) - ex (57436 / 100000) 199 * cCG cZ 199 ∧ ex (57436 / 100000) 196 * cCG cZ 196 + kappa * (ex (57436 / 100000) 197 * cCG cZ 197) - kappa * (ex (57436 / 100000) 198 * cCG cZ 198) - ex (57436 / 100000) 199 * cCG cZ 199 ≤ (8017686483 / 250000000000 : ℝ) := by
  have h0 := eC_196
  have h1 := keC_197
  have h2 := keC_198
  have h3 := eC_199
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_40 : (-97405142163327 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 201 * cCG cZ 201 + kappa * (ex (57436 / 100000) 202 * cCG cZ 202) - kappa * (ex (57436 / 100000) 203 * cCG cZ 203) - ex (57436 / 100000) 204 * cCG cZ 204 ∧ ex (57436 / 100000) 201 * cCG cZ 201 + kappa * (ex (57436 / 100000) 202 * cCG cZ 202) - kappa * (ex (57436 / 100000) 203 * cCG cZ 203) - ex (57436 / 100000) 204 * cCG cZ 204 ≤ (-3043909373999 / 31250000000000 : ℝ) := by
  have h0 := eC_201
  have h1 := keC_202
  have h2 := keC_203
  have h3 := eC_204
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_0 : (49501887548697 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 1 * sCG cZ 1 + kappa * (ex (57436 / 100000) 2 * sCG cZ 2) - kappa * (ex (57436 / 100000) 3 * sCG cZ 3) - ex (57436 / 100000) 4 * sCG cZ 4 ∧ ex (57436 / 100000) 1 * sCG cZ 1 + kappa * (ex (57436 / 100000) 2 * sCG cZ 2) - kappa * (ex (57436 / 100000) 3 * sCG cZ 3) - ex (57436 / 100000) 4 * sCG cZ 4 ≤ (495018910952113 / 1000000000000000 : ℝ) := by
  have h0 : ex (57436 / 100000) 1 * sCG cZ 1 = (0 : ℝ) := by rw [sCG_one]; norm_num
  have h1 := keS_2
  have h2 := keS_3
  have h3 := eS_4
  constructor <;> linarith [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_1 : (-18935929851603 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 6 * sCG cZ 6 + kappa * (ex (57436 / 100000) 7 * sCG cZ 7) - kappa * (ex (57436 / 100000) 8 * sCG cZ 8) - ex (57436 / 100000) 9 * sCG cZ 9 ∧ ex (57436 / 100000) 6 * sCG cZ 6 + kappa * (ex (57436 / 100000) 7 * sCG cZ 7) - kappa * (ex (57436 / 100000) 8 * sCG cZ 8) - ex (57436 / 100000) 9 * sCG cZ 9 ≤ (-12118992958567 / 40000000000000 : ℝ) := by
  have h0 := eS_6
  have h1 := keS_7
  have h2 := keS_8
  have h3 := eS_9
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_2 : (2084643132123 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 11 * sCG cZ 11 + kappa * (ex (57436 / 100000) 12 * sCG cZ 12) - kappa * (ex (57436 / 100000) 13 * sCG cZ 13) - ex (57436 / 100000) 14 * sCG cZ 14 ∧ ex (57436 / 100000) 11 * sCG cZ 11 + kappa * (ex (57436 / 100000) 12 * sCG cZ 12) - kappa * (ex (57436 / 100000) 13 * sCG cZ 13) - ex (57436 / 100000) 14 * sCG cZ 14 ≤ (1042332754547 / 250000000000000 : ℝ) := by
  have h0 := eS_11
  have h1 := keS_12
  have h2 := keS_13
  have h3 := eS_14
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_3 : (79498428981543 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 16 * sCG cZ 16 + kappa * (ex (57436 / 100000) 17 * sCG cZ 17) - kappa * (ex (57436 / 100000) 18 * sCG cZ 18) - ex (57436 / 100000) 19 * sCG cZ 19 ∧ ex (57436 / 100000) 16 * sCG cZ 16 + kappa * (ex (57436 / 100000) 17 * sCG cZ 17) - kappa * (ex (57436 / 100000) 18 * sCG cZ 18) - ex (57436 / 100000) 19 * sCG cZ 19 ≤ (79498475930429 / 1000000000000000 : ℝ) := by
  have h0 := eS_16
  have h1 := keS_17
  have h2 := keS_18
  have h3 := eS_19
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_4 : (-356538475698023 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 21 * sCG cZ 21 + kappa * (ex (57436 / 100000) 22 * sCG cZ 22) - kappa * (ex (57436 / 100000) 23 * sCG cZ 23) - ex (57436 / 100000) 24 * sCG cZ 24 ∧ ex (57436 / 100000) 21 * sCG cZ 21 + kappa * (ex (57436 / 100000) 22 * sCG cZ 22) - kappa * (ex (57436 / 100000) 23 * sCG cZ 23) - ex (57436 / 100000) 24 * sCG cZ 24 ≤ (-89134607255337 / 250000000000000 : ℝ) := by
  have h0 := eS_21
  have h1 := keS_22
  have h2 := keS_23
  have h3 := eS_24
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_5 : (-8164552137209 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 26 * sCG cZ 26 + kappa * (ex (57436 / 100000) 27 * sCG cZ 27) - kappa * (ex (57436 / 100000) 28 * sCG cZ 28) - ex (57436 / 100000) 29 * sCG cZ 29 ∧ ex (57436 / 100000) 26 * sCG cZ 26 + kappa * (ex (57436 / 100000) 27 * sCG cZ 27) - kappa * (ex (57436 / 100000) 28 * sCG cZ 28) - ex (57436 / 100000) 29 * sCG cZ 29 ≤ (-2041127384717 / 250000000000000 : ℝ) := by
  have h0 := eS_26
  have h1 := keS_27
  have h2 := keS_28
  have h3 := eS_29
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_6 : (-13705366772731 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 31 * sCG cZ 31 + kappa * (ex (57436 / 100000) 32 * sCG cZ 32) - kappa * (ex (57436 / 100000) 33 * sCG cZ 33) - ex (57436 / 100000) 34 * sCG cZ 34 ∧ ex (57436 / 100000) 31 * sCG cZ 31 + kappa * (ex (57436 / 100000) 32 * sCG cZ 32) - kappa * (ex (57436 / 100000) 33 * sCG cZ 33) - ex (57436 / 100000) 34 * sCG cZ 34 ≤ (-68526794955781 / 1000000000000000 : ℝ) := by
  have h0 := eS_31
  have h1 := keS_32
  have h2 := keS_33
  have h3 := eS_34
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_7 : (-14764229251577 / 100000000000000 : ℝ) ≤ ex (57436 / 100000) 36 * sCG cZ 36 + kappa * (ex (57436 / 100000) 37 * sCG cZ 37) - kappa * (ex (57436 / 100000) 38 * sCG cZ 38) - ex (57436 / 100000) 39 * sCG cZ 39 ∧ ex (57436 / 100000) 36 * sCG cZ 36 + kappa * (ex (57436 / 100000) 37 * sCG cZ 37) - kappa * (ex (57436 / 100000) 38 * sCG cZ 38) - ex (57436 / 100000) 39 * sCG cZ 39 ≤ (-147642256599169 / 1000000000000000 : ℝ) := by
  have h0 := eS_36
  have h1 := keS_37
  have h2 := keS_38
  have h3 := eS_39
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_8 : (-6295014704241 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 41 * sCG cZ 41 + kappa * (ex (57436 / 100000) 42 * sCG cZ 42) - kappa * (ex (57436 / 100000) 43 * sCG cZ 43) - ex (57436 / 100000) 44 * sCG cZ 44 ∧ ex (57436 / 100000) 41 * sCG cZ 41 + kappa * (ex (57436 / 100000) 42 * sCG cZ 42) - kappa * (ex (57436 / 100000) 43 * sCG cZ 43) - ex (57436 / 100000) 44 * sCG cZ 44 ≤ (-3147490631943 / 500000000000000 : ℝ) := by
  have h0 := eS_41
  have h1 := keS_42
  have h2 := keS_43
  have h3 := eS_44
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_9 : (-3537652576799 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 46 * sCG cZ 46 + kappa * (ex (57436 / 100000) 47 * sCG cZ 47) - kappa * (ex (57436 / 100000) 48 * sCG cZ 48) - ex (57436 / 100000) 49 * sCG cZ 49 ∧ ex (57436 / 100000) 46 * sCG cZ 46 + kappa * (ex (57436 / 100000) 47 * sCG cZ 47) - kappa * (ex (57436 / 100000) 48 * sCG cZ 48) - ex (57436 / 100000) 49 * sCG cZ 49 ≤ (-4422057891443 / 250000000000000 : ℝ) := by
  have h0 := eS_46
  have h1 := keS_47
  have h2 := keS_48
  have h3 := eS_49
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_10 : (133572252705739 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 51 * sCG cZ 51 + kappa * (ex (57436 / 100000) 52 * sCG cZ 52) - kappa * (ex (57436 / 100000) 53 * sCG cZ 53) - ex (57436 / 100000) 54 * sCG cZ 54 ∧ ex (57436 / 100000) 51 * sCG cZ 51 + kappa * (ex (57436 / 100000) 52 * sCG cZ 52) - kappa * (ex (57436 / 100000) 53 * sCG cZ 53) - ex (57436 / 100000) 54 * sCG cZ 54 ≤ (66786141209881 / 500000000000000 : ℝ) := by
  have h0 := eS_51
  have h1 := keS_52
  have h2 := keS_53
  have h3 := eS_54
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_11 : (-17853614947557 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 56 * sCG cZ 56 + kappa * (ex (57436 / 100000) 57 * sCG cZ 57) - kappa * (ex (57436 / 100000) 58 * sCG cZ 58) - ex (57436 / 100000) 59 * sCG cZ 59 ∧ ex (57436 / 100000) 56 * sCG cZ 56 + kappa * (ex (57436 / 100000) 57 * sCG cZ 57) - kappa * (ex (57436 / 100000) 58 * sCG cZ 58) - ex (57436 / 100000) 59 * sCG cZ 59 ≤ (-71414428187117 / 1000000000000000 : ℝ) := by
  have h0 := eS_56
  have h1 := keS_57
  have h2 := keS_58
  have h3 := eS_59
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_12 : (-83462729624091 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 61 * sCG cZ 61 + kappa * (ex (57436 / 100000) 62 * sCG cZ 62) - kappa * (ex (57436 / 100000) 63 * sCG cZ 63) - ex (57436 / 100000) 64 * sCG cZ 64 ∧ ex (57436 / 100000) 61 * sCG cZ 61 + kappa * (ex (57436 / 100000) 62 * sCG cZ 62) - kappa * (ex (57436 / 100000) 63 * sCG cZ 63) - ex (57436 / 100000) 64 * sCG cZ 64 ≤ (-2086567122901 / 25000000000000 : ℝ) := by
  have h0 := eS_61
  have h1 := keS_62
  have h2 := keS_63
  have h3 := eS_64
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_13 : (-38030535736041 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 66 * sCG cZ 66 + kappa * (ex (57436 / 100000) 67 * sCG cZ 67) - kappa * (ex (57436 / 100000) 68 * sCG cZ 68) - ex (57436 / 100000) 69 * sCG cZ 69 ∧ ex (57436 / 100000) 66 * sCG cZ 66 + kappa * (ex (57436 / 100000) 67 * sCG cZ 67) - kappa * (ex (57436 / 100000) 68 * sCG cZ 68) - ex (57436 / 100000) 69 * sCG cZ 69 ≤ (-9507620633709 / 250000000000000 : ℝ) := by
  have h0 := eS_66
  have h1 := keS_67
  have h2 := keS_68
  have h3 := eS_69
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_14 : (-3405002928247 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 71 * sCG cZ 71 + kappa * (ex (57436 / 100000) 72 * sCG cZ 72) - kappa * (ex (57436 / 100000) 73 * sCG cZ 73) - ex (57436 / 100000) 74 * sCG cZ 74 ∧ ex (57436 / 100000) 71 * sCG cZ 71 + kappa * (ex (57436 / 100000) 72 * sCG cZ 72) - kappa * (ex (57436 / 100000) 73 * sCG cZ 73) - ex (57436 / 100000) 74 * sCG cZ 74 ≤ (-6809947915807 / 1000000000000000 : ℝ) := by
  have h0 := eS_71
  have h1 := keS_72
  have h2 := keS_73
  have h3 := eS_74
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_15 : (1145367659637 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 76 * sCG cZ 76 + kappa * (ex (57436 / 100000) 77 * sCG cZ 77) - kappa * (ex (57436 / 100000) 78 * sCG cZ 78) - ex (57436 / 100000) 79 * sCG cZ 79 ∧ ex (57436 / 100000) 76 * sCG cZ 76 + kappa * (ex (57436 / 100000) 77 * sCG cZ 77) - kappa * (ex (57436 / 100000) 78 * sCG cZ 78) - ex (57436 / 100000) 79 * sCG cZ 79 ≤ (229085638341 / 200000000000000 : ℝ) := by
  have h0 := eS_76
  have h1 := keS_77
  have h2 := keS_78
  have h3 := eS_79
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_16 : (-9691286534537 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 81 * sCG cZ 81 + kappa * (ex (57436 / 100000) 82 * sCG cZ 82) - kappa * (ex (57436 / 100000) 83 * sCG cZ 83) - ex (57436 / 100000) 84 * sCG cZ 84 ∧ ex (57436 / 100000) 81 * sCG cZ 81 + kappa * (ex (57436 / 100000) 82 * sCG cZ 82) - kappa * (ex (57436 / 100000) 83 * sCG cZ 83) - ex (57436 / 100000) 84 * sCG cZ 84 ≤ (-6057046389687 / 125000000000000 : ℝ) := by
  have h0 := eS_81
  have h1 := keS_82
  have h2 := keS_83
  have h3 := eS_84
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_17 : (77985685315947 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 86 * sCG cZ 86 + kappa * (ex (57436 / 100000) 87 * sCG cZ 87) - kappa * (ex (57436 / 100000) 88 * sCG cZ 88) - ex (57436 / 100000) 89 * sCG cZ 89 ∧ ex (57436 / 100000) 86 * sCG cZ 86 + kappa * (ex (57436 / 100000) 87 * sCG cZ 87) - kappa * (ex (57436 / 100000) 88 * sCG cZ 88) - ex (57436 / 100000) 89 * sCG cZ 89 ≤ (38992873582831 / 500000000000000 : ℝ) := by
  have h0 := eS_86
  have h1 := keS_87
  have h2 := keS_88
  have h3 := eS_89
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_18 : (-91537965229409 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 91 * sCG cZ 91 + kappa * (ex (57436 / 100000) 92 * sCG cZ 92) - kappa * (ex (57436 / 100000) 93 * sCG cZ 93) - ex (57436 / 100000) 94 * sCG cZ 94 ∧ ex (57436 / 100000) 91 * sCG cZ 91 + kappa * (ex (57436 / 100000) 92 * sCG cZ 92) - kappa * (ex (57436 / 100000) 93 * sCG cZ 93) - ex (57436 / 100000) 94 * sCG cZ 94 ≤ (-18307580723059 / 200000000000000 : ℝ) := by
  have h0 := eS_91
  have h1 := keS_92
  have h2 := keS_93
  have h3 := eS_94
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_19 : (15293297447217 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 96 * sCG cZ 96 + kappa * (ex (57436 / 100000) 97 * sCG cZ 97) - kappa * (ex (57436 / 100000) 98 * sCG cZ 98) - ex (57436 / 100000) 99 * sCG cZ 99 ∧ ex (57436 / 100000) 96 * sCG cZ 96 + kappa * (ex (57436 / 100000) 97 * sCG cZ 97) - kappa * (ex (57436 / 100000) 98 * sCG cZ 98) - ex (57436 / 100000) 99 * sCG cZ 99 ≤ (61173250811777 / 1000000000000000 : ℝ) := by
  have h0 := eS_96
  have h1 := keS_97
  have h2 := keS_98
  have h3 := eS_99
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_20 : (7240128887727 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 101 * sCG cZ 101 + kappa * (ex (57436 / 100000) 102 * sCG cZ 102) - kappa * (ex (57436 / 100000) 103 * sCG cZ 103) - ex (57436 / 100000) 104 * sCG cZ 104 ∧ ex (57436 / 100000) 101 * sCG cZ 101 + kappa * (ex (57436 / 100000) 102 * sCG cZ 102) - kappa * (ex (57436 / 100000) 103 * sCG cZ 103) - ex (57436 / 100000) 104 * sCG cZ 104 ≤ (57921091355729 / 1000000000000000 : ℝ) := by
  have h0 := eS_101
  have h1 := keS_102
  have h2 := keS_103
  have h3 := eS_104
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_21 : (-28778980132813 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 106 * sCG cZ 106 + kappa * (ex (57436 / 100000) 107 * sCG cZ 107) - kappa * (ex (57436 / 100000) 108 * sCG cZ 108) - ex (57436 / 100000) 109 * sCG cZ 109 ∧ ex (57436 / 100000) 106 * sCG cZ 106 + kappa * (ex (57436 / 100000) 107 * sCG cZ 107) - kappa * (ex (57436 / 100000) 108 * sCG cZ 108) - ex (57436 / 100000) 109 * sCG cZ 109 ≤ (-57557930533751 / 500000000000000 : ℝ) := by
  have h0 := eS_106
  have h1 := keS_107
  have h2 := keS_108
  have h3 := eS_109
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_22 : (-85626881141021 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 111 * sCG cZ 111 + kappa * (ex (57436 / 100000) 112 * sCG cZ 112) - kappa * (ex (57436 / 100000) 113 * sCG cZ 113) - ex (57436 / 100000) 114 * sCG cZ 114 ∧ ex (57436 / 100000) 111 * sCG cZ 111 + kappa * (ex (57436 / 100000) 112 * sCG cZ 112) - kappa * (ex (57436 / 100000) 113 * sCG cZ 113) - ex (57436 / 100000) 114 * sCG cZ 114 ≤ (-85626822726893 / 1000000000000000 : ℝ) := by
  have h0 := eS_111
  have h1 := keS_112
  have h2 := keS_113
  have h3 := eS_114
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_23 : (32702319705857 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 116 * sCG cZ 116 + kappa * (ex (57436 / 100000) 117 * sCG cZ 117) - kappa * (ex (57436 / 100000) 118 * sCG cZ 118) - ex (57436 / 100000) 119 * sCG cZ 119 ∧ ex (57436 / 100000) 116 * sCG cZ 116 + kappa * (ex (57436 / 100000) 117 * sCG cZ 117) - kappa * (ex (57436 / 100000) 118 * sCG cZ 118) - ex (57436 / 100000) 119 * sCG cZ 119 ≤ (16351188543879 / 500000000000000 : ℝ) := by
  have h0 := eS_116
  have h1 := keS_117
  have h2 := keS_118
  have h3 := eS_119
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_24 : (53127450136671 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 121 * sCG cZ 121 + kappa * (ex (57436 / 100000) 122 * sCG cZ 122) - kappa * (ex (57436 / 100000) 123 * sCG cZ 123) - ex (57436 / 100000) 124 * sCG cZ 124 ∧ ex (57436 / 100000) 121 * sCG cZ 121 + kappa * (ex (57436 / 100000) 122 * sCG cZ 122) - kappa * (ex (57436 / 100000) 123 * sCG cZ 123) - ex (57436 / 100000) 124 * sCG cZ 124 ≤ (106254956600697 / 1000000000000000 : ℝ) := by
  have h0 := eS_121
  have h1 := keS_122
  have h2 := keS_123
  have h3 := eS_124
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_25 : (129991289492993 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 126 * sCG cZ 126 + kappa * (ex (57436 / 100000) 127 * sCG cZ 127) - kappa * (ex (57436 / 100000) 128 * sCG cZ 128) - ex (57436 / 100000) 129 * sCG cZ 129 ∧ ex (57436 / 100000) 126 * sCG cZ 126 + kappa * (ex (57436 / 100000) 127 * sCG cZ 127) - kappa * (ex (57436 / 100000) 128 * sCG cZ 128) - ex (57436 / 100000) 129 * sCG cZ 129 ≤ (129991344509071 / 1000000000000000 : ℝ) := by
  have h0 := eS_126
  have h1 := keS_127
  have h2 := keS_128
  have h3 := eS_129
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_26 : (66588659680051 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 131 * sCG cZ 131 + kappa * (ex (57436 / 100000) 132 * sCG cZ 132) - kappa * (ex (57436 / 100000) 133 * sCG cZ 133) - ex (57436 / 100000) 134 * sCG cZ 134 ∧ ex (57436 / 100000) 131 * sCG cZ 131 + kappa * (ex (57436 / 100000) 132 * sCG cZ 132) - kappa * (ex (57436 / 100000) 133 * sCG cZ 133) - ex (57436 / 100000) 134 * sCG cZ 134 ≤ (33294343307333 / 250000000000000 : ℝ) := by
  have h0 := eS_131
  have h1 := keS_132
  have h2 := keS_133
  have h3 := eS_134
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_27 : (16062415332007 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 136 * sCG cZ 136 + kappa * (ex (57436 / 100000) 137 * sCG cZ 137) - kappa * (ex (57436 / 100000) 138 * sCG cZ 138) - ex (57436 / 100000) 139 * sCG cZ 139 ∧ ex (57436 / 100000) 136 * sCG cZ 136 + kappa * (ex (57436 / 100000) 137 * sCG cZ 137) - kappa * (ex (57436 / 100000) 138 * sCG cZ 138) - ex (57436 / 100000) 139 * sCG cZ 139 ≤ (6424968768149 / 50000000000000 : ℝ) := by
  have h0 := eS_136
  have h1 := keS_137
  have h2 := keS_138
  have h3 := eS_139
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_28 : (53776864434643 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 141 * sCG cZ 141 + kappa * (ex (57436 / 100000) 142 * sCG cZ 142) - kappa * (ex (57436 / 100000) 143 * sCG cZ 143) - ex (57436 / 100000) 144 * sCG cZ 144 ∧ ex (57436 / 100000) 141 * sCG cZ 141 + kappa * (ex (57436 / 100000) 142 * sCG cZ 142) - kappa * (ex (57436 / 100000) 143 * sCG cZ 143) - ex (57436 / 100000) 144 * sCG cZ 144 ≤ (53776890253283 / 500000000000000 : ℝ) := by
  have h0 := eS_141
  have h1 := keS_142
  have h2 := keS_143
  have h3 := eS_144
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_29 : (2072986255207 / 40000000000000 : ℝ) ≤ ex (57436 / 100000) 146 * sCG cZ 146 + kappa * (ex (57436 / 100000) 147 * sCG cZ 147) - kappa * (ex (57436 / 100000) 148 * sCG cZ 148) - ex (57436 / 100000) 149 * sCG cZ 149 ∧ ex (57436 / 100000) 146 * sCG cZ 146 + kappa * (ex (57436 / 100000) 147 * sCG cZ 147) - kappa * (ex (57436 / 100000) 148 * sCG cZ 148) - ex (57436 / 100000) 149 * sCG cZ 149 ≤ (12956176747331 / 250000000000000 : ℝ) := by
  have h0 := eS_146
  have h1 := keS_147
  have h2 := keS_148
  have h3 := eS_149
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_30 : (-40465035023711 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 151 * sCG cZ 151 + kappa * (ex (57436 / 100000) 152 * sCG cZ 152) - kappa * (ex (57436 / 100000) 153 * sCG cZ 153) - ex (57436 / 100000) 154 * sCG cZ 154 ∧ ex (57436 / 100000) 151 * sCG cZ 151 + kappa * (ex (57436 / 100000) 152 * sCG cZ 152) - kappa * (ex (57436 / 100000) 153 * sCG cZ 153) - ex (57436 / 100000) 154 * sCG cZ 154 ≤ (-40464985467377 / 1000000000000000 : ℝ) := by
  have h0 := eS_151
  have h1 := keS_152
  have h2 := keS_153
  have h3 := eS_154
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_31 : (-118046856526091 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 156 * sCG cZ 156 + kappa * (ex (57436 / 100000) 157 * sCG cZ 157) - kappa * (ex (57436 / 100000) 158 * sCG cZ 158) - ex (57436 / 100000) 159 * sCG cZ 159 ∧ ex (57436 / 100000) 156 * sCG cZ 156 + kappa * (ex (57436 / 100000) 157 * sCG cZ 157) - kappa * (ex (57436 / 100000) 158 * sCG cZ 158) - ex (57436 / 100000) 159 * sCG cZ 159 ≤ (-59023403895587 / 500000000000000 : ℝ) := by
  have h0 := eS_156
  have h1 := keS_157
  have h2 := keS_158
  have h3 := eS_159
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_32 : (-703795271667 / 7812500000000 : ℝ) ≤ ex (57436 / 100000) 161 * sCG cZ 161 + kappa * (ex (57436 / 100000) 162 * sCG cZ 162) - kappa * (ex (57436 / 100000) 163 * sCG cZ 163) - ex (57436 / 100000) 164 * sCG cZ 164 ∧ ex (57436 / 100000) 161 * sCG cZ 161 + kappa * (ex (57436 / 100000) 162 * sCG cZ 162) - kappa * (ex (57436 / 100000) 163 * sCG cZ 163) - ex (57436 / 100000) 164 * sCG cZ 164 ≤ (-9008574690073 / 100000000000000 : ℝ) := by
  have h0 := eS_161
  have h1 := keS_162
  have h2 := keS_163
  have h3 := eS_164
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_33 : (11910800758293 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 166 * sCG cZ 166 + kappa * (ex (57436 / 100000) 167 * sCG cZ 167) - kappa * (ex (57436 / 100000) 168 * sCG cZ 168) - ex (57436 / 100000) 169 * sCG cZ 169 ∧ ex (57436 / 100000) 166 * sCG cZ 166 + kappa * (ex (57436 / 100000) 167 * sCG cZ 167) - kappa * (ex (57436 / 100000) 168 * sCG cZ 168) - ex (57436 / 100000) 169 * sCG cZ 169 ≤ (23821625016101 / 500000000000000 : ℝ) := by
  have h0 := eS_166
  have h1 := keS_167
  have h2 := keS_168
  have h3 := eS_169
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_34 : (113789949927877 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 171 * sCG cZ 171 + kappa * (ex (57436 / 100000) 172 * sCG cZ 172) - kappa * (ex (57436 / 100000) 173 * sCG cZ 173) - ex (57436 / 100000) 174 * sCG cZ 174 ∧ ex (57436 / 100000) 171 * sCG cZ 171 + kappa * (ex (57436 / 100000) 172 * sCG cZ 172) - kappa * (ex (57436 / 100000) 173 * sCG cZ 173) - ex (57436 / 100000) 174 * sCG cZ 174 ≤ (113789996228609 / 1000000000000000 : ℝ) := by
  have h0 := eS_171
  have h1 := keS_172
  have h2 := keS_173
  have h3 := eS_174
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_35 : (-20387317992603 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 176 * sCG cZ 176 + kappa * (ex (57436 / 100000) 177 * sCG cZ 177) - kappa * (ex (57436 / 100000) 178 * sCG cZ 178) - ex (57436 / 100000) 179 * sCG cZ 179 ∧ ex (57436 / 100000) 176 * sCG cZ 176 + kappa * (ex (57436 / 100000) 177 * sCG cZ 177) - kappa * (ex (57436 / 100000) 178 * sCG cZ 178) - ex (57436 / 100000) 179 * sCG cZ 179 ≤ (-2038727255139 / 100000000000000 : ℝ) := by
  have h0 := eS_176
  have h1 := keS_177
  have h2 := keS_178
  have h3 := eS_179
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_36 : (-107105771346637 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 181 * sCG cZ 181 + kappa * (ex (57436 / 100000) 182 * sCG cZ 182) - kappa * (ex (57436 / 100000) 183 * sCG cZ 183) - ex (57436 / 100000) 184 * sCG cZ 184 ∧ ex (57436 / 100000) 181 * sCG cZ 181 + kappa * (ex (57436 / 100000) 182 * sCG cZ 182) - kappa * (ex (57436 / 100000) 183 * sCG cZ 183) - ex (57436 / 100000) 184 * sCG cZ 184 ≤ (-107105726540137 / 1000000000000000 : ℝ) := by
  have h0 := eS_181
  have h1 := keS_182
  have h2 := keS_183
  have h3 := eS_184
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_37 : (49935592694269 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 186 * sCG cZ 186 + kappa * (ex (57436 / 100000) 187 * sCG cZ 187) - kappa * (ex (57436 / 100000) 188 * sCG cZ 188) - ex (57436 / 100000) 189 * sCG cZ 189 ∧ ex (57436 / 100000) 186 * sCG cZ 186 + kappa * (ex (57436 / 100000) 187 * sCG cZ 187) - kappa * (ex (57436 / 100000) 188 * sCG cZ 188) - ex (57436 / 100000) 189 * sCG cZ 189 ≤ (4993563676311 / 100000000000000 : ℝ) := by
  have h0 := eS_186
  have h1 := keS_187
  have h2 := keS_188
  have h3 := eS_189
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_38 : (9087728854257 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 191 * sCG cZ 191 + kappa * (ex (57436 / 100000) 192 * sCG cZ 192) - kappa * (ex (57436 / 100000) 193 * sCG cZ 193) - ex (57436 / 100000) 194 * sCG cZ 194 ∧ ex (57436 / 100000) 191 * sCG cZ 191 + kappa * (ex (57436 / 100000) 192 * sCG cZ 192) - kappa * (ex (57436 / 100000) 193 * sCG cZ 193) - ex (57436 / 100000) 194 * sCG cZ 194 ≤ (72701874250069 / 1000000000000000 : ℝ) := by
  have h0 := eS_191
  have h1 := keS_192
  have h2 := keS_193
  have h3 := eS_194
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_39 : (-97621333804689 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 196 * sCG cZ 196 + kappa * (ex (57436 / 100000) 197 * sCG cZ 197) - kappa * (ex (57436 / 100000) 198 * sCG cZ 198) - ex (57436 / 100000) 199 * sCG cZ 199 ∧ ex (57436 / 100000) 196 * sCG cZ 196 + kappa * (ex (57436 / 100000) 197 * sCG cZ 197) - kappa * (ex (57436 / 100000) 198 * sCG cZ 198) - ex (57436 / 100000) 199 * sCG cZ 199 ≤ (-48810645498121 / 500000000000000 : ℝ) := by
  have h0 := eS_196
  have h1 := keS_197
  have h2 := keS_198
  have h3 := eS_199
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_40 : (11530282815011 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 201 * sCG cZ 201 + kappa * (ex (57436 / 100000) 202 * sCG cZ 202) - kappa * (ex (57436 / 100000) 203 * sCG cZ 203) - ex (57436 / 100000) 204 * sCG cZ 204 ∧ ex (57436 / 100000) 201 * sCG cZ 201 + kappa * (ex (57436 / 100000) 202 * sCG cZ 202) - kappa * (ex (57436 / 100000) 203 * sCG cZ 203) - ex (57436 / 100000) 204 * sCG cZ 204 ≤ (11530303887059 / 500000000000000 : ℝ) := by
  have h0 := eS_201
  have h1 := keS_202
  have h2 := keS_203
  have h3 := eS_204
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_0 : (-2862370668781 / 20000000000000 : ℝ) ≤ Real.log 1 * (ex (57436 / 100000) 1 * cCG cZ 1) + kappa * (Real.log 2 * (ex (57436 / 100000) 2 * cCG cZ 2)) - kappa * (Real.log 3 * (ex (57436 / 100000) 3 * cCG cZ 3)) - Real.log 4 * (ex (57436 / 100000) 4 * cCG cZ 4) ∧ Real.log 1 * (ex (57436 / 100000) 1 * cCG cZ 1) + kappa * (Real.log 2 * (ex (57436 / 100000) 2 * cCG cZ 2)) - kappa * (Real.log 3 * (ex (57436 / 100000) 3 * cCG cZ 3)) - Real.log 4 * (ex (57436 / 100000) 4 * cCG cZ 4) ≤ (-71559245388103 / 500000000000000 : ℝ) := by
  have h0 : Real.log 1 * (ex (57436 / 100000) 1 * cCG cZ 1) = (0 : ℝ) := by rw [Real.log_one]; norm_num
  have h1 := kleC_2
  have h2 := kleC_3
  have h3 := leC_4
  constructor <;> linarith [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_1 : (-536421207193731 / 500000000000000 : ℝ) ≤ Real.log 6 * (ex (57436 / 100000) 6 * cCG cZ 6) + kappa * (Real.log 7 * (ex (57436 / 100000) 7 * cCG cZ 7)) - kappa * (Real.log 8 * (ex (57436 / 100000) 8 * cCG cZ 8)) - Real.log 9 * (ex (57436 / 100000) 9 * cCG cZ 9) ∧ Real.log 6 * (ex (57436 / 100000) 6 * cCG cZ 6) + kappa * (Real.log 7 * (ex (57436 / 100000) 7 * cCG cZ 7)) - kappa * (Real.log 8 * (ex (57436 / 100000) 8 * cCG cZ 8)) - Real.log 9 * (ex (57436 / 100000) 9 * cCG cZ 9) ≤ (-1072842307088477 / 1000000000000000 : ℝ) := by
  have h0 := leC_6
  have h1 := kleC_7
  have h2 := kleC_8
  have h3 := leC_9
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_2 : (-9418929594841 / 8000000000000 : ℝ) ≤ Real.log 11 * (ex (57436 / 100000) 11 * cCG cZ 11) + kappa * (Real.log 12 * (ex (57436 / 100000) 12 * cCG cZ 12)) - kappa * (Real.log 13 * (ex (57436 / 100000) 13 * cCG cZ 13)) - Real.log 14 * (ex (57436 / 100000) 14 * cCG cZ 14) ∧ Real.log 11 * (ex (57436 / 100000) 11 * cCG cZ 11) + kappa * (Real.log 12 * (ex (57436 / 100000) 12 * cCG cZ 12)) - kappa * (Real.log 13 * (ex (57436 / 100000) 13 * cCG cZ 13)) - Real.log 14 * (ex (57436 / 100000) 14 * cCG cZ 14) ≤ (-235473217283797 / 200000000000000 : ℝ) := by
  have h0 := leC_11
  have h1 := kleC_12
  have h2 := kleC_13
  have h3 := leC_14
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_3 : (-809656071784553 / 1000000000000000 : ℝ) ≤ Real.log 16 * (ex (57436 / 100000) 16 * cCG cZ 16) + kappa * (Real.log 17 * (ex (57436 / 100000) 17 * cCG cZ 17)) - kappa * (Real.log 18 * (ex (57436 / 100000) 18 * cCG cZ 18)) - Real.log 19 * (ex (57436 / 100000) 19 * cCG cZ 19) ∧ Real.log 16 * (ex (57436 / 100000) 16 * cCG cZ 16) + kappa * (Real.log 17 * (ex (57436 / 100000) 17 * cCG cZ 17)) - kappa * (Real.log 18 * (ex (57436 / 100000) 18 * cCG cZ 18)) - Real.log 19 * (ex (57436 / 100000) 19 * cCG cZ 19) ≤ (-809655936811237 / 1000000000000000 : ℝ) := by
  have h0 := leC_16
  have h1 := kleC_17
  have h2 := kleC_18
  have h3 := leC_19
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_4 : (-2059190253467 / 5000000000000 : ℝ) ≤ Real.log 21 * (ex (57436 / 100000) 21 * cCG cZ 21) + kappa * (Real.log 22 * (ex (57436 / 100000) 22 * cCG cZ 22)) - kappa * (Real.log 23 * (ex (57436 / 100000) 23 * cCG cZ 23)) - Real.log 24 * (ex (57436 / 100000) 24 * cCG cZ 24) ∧ Real.log 21 * (ex (57436 / 100000) 21 * cCG cZ 21) + kappa * (Real.log 22 * (ex (57436 / 100000) 22 * cCG cZ 22)) - kappa * (Real.log 23 * (ex (57436 / 100000) 23 * cCG cZ 23)) - Real.log 24 * (ex (57436 / 100000) 24 * cCG cZ 24) ≤ (-25739869096559 / 62500000000000 : ℝ) := by
  have h0 := leC_21
  have h1 := kleC_22
  have h2 := kleC_23
  have h3 := leC_24
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_5 : (-88484717105609 / 250000000000000 : ℝ) ≤ Real.log 26 * (ex (57436 / 100000) 26 * cCG cZ 26) + kappa * (Real.log 27 * (ex (57436 / 100000) 27 * cCG cZ 27)) - kappa * (Real.log 28 * (ex (57436 / 100000) 28 * cCG cZ 28)) - Real.log 29 * (ex (57436 / 100000) 29 * cCG cZ 29) ∧ Real.log 26 * (ex (57436 / 100000) 26 * cCG cZ 26) + kappa * (Real.log 27 * (ex (57436 / 100000) 27 * cCG cZ 27)) - kappa * (Real.log 28 * (ex (57436 / 100000) 28 * cCG cZ 28)) - Real.log 29 * (ex (57436 / 100000) 29 * cCG cZ 29) ≤ (-176969363774057 / 500000000000000 : ℝ) := by
  have h0 := leC_26
  have h1 := kleC_27
  have h2 := kleC_28
  have h3 := leC_29
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_6 : (8192893410629 / 7812500000000 : ℝ) ≤ Real.log 31 * (ex (57436 / 100000) 31 * cCG cZ 31) + kappa * (Real.log 32 * (ex (57436 / 100000) 32 * cCG cZ 32)) - kappa * (Real.log 33 * (ex (57436 / 100000) 33 * cCG cZ 33)) - Real.log 34 * (ex (57436 / 100000) 34 * cCG cZ 34) ∧ Real.log 31 * (ex (57436 / 100000) 31 * cCG cZ 31) + kappa * (Real.log 32 * (ex (57436 / 100000) 32 * cCG cZ 32)) - kappa * (Real.log 33 * (ex (57436 / 100000) 33 * cCG cZ 33)) - Real.log 34 * (ex (57436 / 100000) 34 * cCG cZ 34) ≤ (1048690492368257 / 1000000000000000 : ℝ) := by
  have h0 := leC_31
  have h1 := kleC_32
  have h2 := kleC_33
  have h3 := leC_34
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_7 : (32561595004867 / 500000000000000 : ℝ) ≤ Real.log 36 * (ex (57436 / 100000) 36 * cCG cZ 36) + kappa * (Real.log 37 * (ex (57436 / 100000) 37 * cCG cZ 37)) - kappa * (Real.log 38 * (ex (57436 / 100000) 38 * cCG cZ 38)) - Real.log 39 * (ex (57436 / 100000) 39 * cCG cZ 39) ∧ Real.log 36 * (ex (57436 / 100000) 36 * cCG cZ 36) + kappa * (Real.log 37 * (ex (57436 / 100000) 37 * cCG cZ 37)) - kappa * (Real.log 38 * (ex (57436 / 100000) 38 * cCG cZ 38)) - Real.log 39 * (ex (57436 / 100000) 39 * cCG cZ 39) ≤ (13024664099993 / 200000000000000 : ℝ) := by
  have h0 := leC_36
  have h1 := kleC_37
  have h2 := kleC_38
  have h3 := leC_39
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_8 : (-114949033039577 / 1000000000000000 : ℝ) ≤ Real.log 41 * (ex (57436 / 100000) 41 * cCG cZ 41) + kappa * (Real.log 42 * (ex (57436 / 100000) 42 * cCG cZ 42)) - kappa * (Real.log 43 * (ex (57436 / 100000) 43 * cCG cZ 43)) - Real.log 44 * (ex (57436 / 100000) 44 * cCG cZ 44) ∧ Real.log 41 * (ex (57436 / 100000) 41 * cCG cZ 41) + kappa * (Real.log 42 * (ex (57436 / 100000) 42 * cCG cZ 42)) - kappa * (Real.log 43 * (ex (57436 / 100000) 43 * cCG cZ 43)) - Real.log 44 * (ex (57436 / 100000) 44 * cCG cZ 44) ≤ (-57474453838201 / 500000000000000 : ℝ) := by
  have h0 := leC_41
  have h1 := kleC_42
  have h2 := kleC_43
  have h3 := leC_44
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_9 : (-2995314514429 / 6250000000000 : ℝ) ≤ Real.log 46 * (ex (57436 / 100000) 46 * cCG cZ 46) + kappa * (Real.log 47 * (ex (57436 / 100000) 47 * cCG cZ 47)) - kappa * (Real.log 48 * (ex (57436 / 100000) 48 * cCG cZ 48)) - Real.log 49 * (ex (57436 / 100000) 49 * cCG cZ 49) ∧ Real.log 46 * (ex (57436 / 100000) 46 * cCG cZ 46) + kappa * (Real.log 47 * (ex (57436 / 100000) 47 * cCG cZ 47)) - kappa * (Real.log 48 * (ex (57436 / 100000) 48 * cCG cZ 48)) - Real.log 49 * (ex (57436 / 100000) 49 * cCG cZ 49) ≤ (-95850040213677 / 200000000000000 : ℝ) := by
  have h0 := leC_46
  have h1 := kleC_47
  have h2 := kleC_48
  have h3 := leC_49
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_10 : (122435482269881 / 500000000000000 : ℝ) ≤ Real.log 51 * (ex (57436 / 100000) 51 * cCG cZ 51) + kappa * (Real.log 52 * (ex (57436 / 100000) 52 * cCG cZ 52)) - kappa * (Real.log 53 * (ex (57436 / 100000) 53 * cCG cZ 53)) - Real.log 54 * (ex (57436 / 100000) 54 * cCG cZ 54) ∧ Real.log 51 * (ex (57436 / 100000) 51 * cCG cZ 51) + kappa * (Real.log 52 * (ex (57436 / 100000) 52 * cCG cZ 52)) - kappa * (Real.log 53 * (ex (57436 / 100000) 53 * cCG cZ 53)) - Real.log 54 * (ex (57436 / 100000) 54 * cCG cZ 54) ≤ (122435541031569 / 500000000000000 : ℝ) := by
  have h0 := leC_51
  have h1 := kleC_52
  have h2 := kleC_53
  have h3 := leC_54
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_11 : (-427230927510333 / 1000000000000000 : ℝ) ≤ Real.log 56 * (ex (57436 / 100000) 56 * cCG cZ 56) + kappa * (Real.log 57 * (ex (57436 / 100000) 57 * cCG cZ 57)) - kappa * (Real.log 58 * (ex (57436 / 100000) 58 * cCG cZ 58)) - Real.log 59 * (ex (57436 / 100000) 59 * cCG cZ 59) ∧ Real.log 56 * (ex (57436 / 100000) 56 * cCG cZ 56) + kappa * (Real.log 57 * (ex (57436 / 100000) 57 * cCG cZ 57)) - kappa * (Real.log 58 * (ex (57436 / 100000) 58 * cCG cZ 58)) - Real.log 59 * (ex (57436 / 100000) 59 * cCG cZ 59) ≤ (-427230799118331 / 1000000000000000 : ℝ) := by
  have h0 := leC_56
  have h1 := kleC_57
  have h2 := kleC_58
  have h3 := leC_59
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_12 : (125898517043389 / 1000000000000000 : ℝ) ≤ Real.log 61 * (ex (57436 / 100000) 61 * cCG cZ 61) + kappa * (Real.log 62 * (ex (57436 / 100000) 62 * cCG cZ 62)) - kappa * (Real.log 63 * (ex (57436 / 100000) 63 * cCG cZ 63)) - Real.log 64 * (ex (57436 / 100000) 64 * cCG cZ 64) ∧ Real.log 61 * (ex (57436 / 100000) 61 * cCG cZ 61) + kappa * (Real.log 62 * (ex (57436 / 100000) 62 * cCG cZ 62)) - kappa * (Real.log 63 * (ex (57436 / 100000) 63 * cCG cZ 63)) - Real.log 64 * (ex (57436 / 100000) 64 * cCG cZ 64) ≤ (125898701978987 / 1000000000000000 : ℝ) := by
  have h0 := leC_61
  have h1 := kleC_62
  have h2 := kleC_63
  have h3 := leC_64
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_13 : (111265324779227 / 1000000000000000 : ℝ) ≤ Real.log 66 * (ex (57436 / 100000) 66 * cCG cZ 66) + kappa * (Real.log 67 * (ex (57436 / 100000) 67 * cCG cZ 67)) - kappa * (Real.log 68 * (ex (57436 / 100000) 68 * cCG cZ 68)) - Real.log 69 * (ex (57436 / 100000) 69 * cCG cZ 69) ∧ Real.log 66 * (ex (57436 / 100000) 66 * cCG cZ 66) + kappa * (Real.log 67 * (ex (57436 / 100000) 67 * cCG cZ 67)) - kappa * (Real.log 68 * (ex (57436 / 100000) 68 * cCG cZ 68)) - Real.log 69 * (ex (57436 / 100000) 69 * cCG cZ 69) ≤ (111265549174377 / 1000000000000000 : ℝ) := by
  have h0 := leC_66
  have h1 := kleC_67
  have h2 := kleC_68
  have h3 := leC_69
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_14 : (-269146409513 / 100000000000000 : ℝ) ≤ Real.log 71 * (ex (57436 / 100000) 71 * cCG cZ 71) + kappa * (Real.log 72 * (ex (57436 / 100000) 72 * cCG cZ 72)) - kappa * (Real.log 73 * (ex (57436 / 100000) 73 * cCG cZ 73)) - Real.log 74 * (ex (57436 / 100000) 74 * cCG cZ 74) ∧ Real.log 71 * (ex (57436 / 100000) 71 * cCG cZ 71) + kappa * (Real.log 72 * (ex (57436 / 100000) 72 * cCG cZ 72)) - kappa * (Real.log 73 * (ex (57436 / 100000) 73 * cCG cZ 73)) - Real.log 74 * (ex (57436 / 100000) 74 * cCG cZ 74) ≤ (-2691215264543 / 1000000000000000 : ℝ) := by
  have h0 := leC_71
  have h1 := kleC_72
  have h2 := kleC_73
  have h3 := leC_74
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_15 : (120410691225473 / 1000000000000000 : ℝ) ≤ Real.log 76 * (ex (57436 / 100000) 76 * cCG cZ 76) + kappa * (Real.log 77 * (ex (57436 / 100000) 77 * cCG cZ 77)) - kappa * (Real.log 78 * (ex (57436 / 100000) 78 * cCG cZ 78)) - Real.log 79 * (ex (57436 / 100000) 79 * cCG cZ 79) ∧ Real.log 76 * (ex (57436 / 100000) 76 * cCG cZ 76) + kappa * (Real.log 77 * (ex (57436 / 100000) 77 * cCG cZ 77)) - kappa * (Real.log 78 * (ex (57436 / 100000) 78 * cCG cZ 78)) - Real.log 79 * (ex (57436 / 100000) 79 * cCG cZ 79) ≤ (60205477043257 / 500000000000000 : ℝ) := by
  have h0 := leC_76
  have h1 := kleC_77
  have h2 := kleC_78
  have h3 := leC_79
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_16 : (-24687403756753 / 200000000000000 : ℝ) ≤ Real.log 81 * (ex (57436 / 100000) 81 * cCG cZ 81) + kappa * (Real.log 82 * (ex (57436 / 100000) 82 * cCG cZ 82)) - kappa * (Real.log 83 * (ex (57436 / 100000) 83 * cCG cZ 83)) - Real.log 84 * (ex (57436 / 100000) 84 * cCG cZ 84) ∧ Real.log 81 * (ex (57436 / 100000) 81 * cCG cZ 81) + kappa * (Real.log 82 * (ex (57436 / 100000) 82 * cCG cZ 82)) - kappa * (Real.log 83 * (ex (57436 / 100000) 83 * cCG cZ 83)) - Real.log 84 * (ex (57436 / 100000) 84 * cCG cZ 84) ≤ (-123436746659113 / 1000000000000000 : ℝ) := by
  have h0 := leC_81
  have h1 := kleC_82
  have h2 := kleC_83
  have h3 := leC_84
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_17 : (6477201959303 / 125000000000000 : ℝ) ≤ Real.log 86 * (ex (57436 / 100000) 86 * cCG cZ 86) + kappa * (Real.log 87 * (ex (57436 / 100000) 87 * cCG cZ 87)) - kappa * (Real.log 88 * (ex (57436 / 100000) 88 * cCG cZ 88)) - Real.log 89 * (ex (57436 / 100000) 89 * cCG cZ 89) ∧ Real.log 86 * (ex (57436 / 100000) 86 * cCG cZ 86) + kappa * (Real.log 87 * (ex (57436 / 100000) 87 * cCG cZ 87)) - kappa * (Real.log 88 * (ex (57436 / 100000) 88 * cCG cZ 88)) - Real.log 89 * (ex (57436 / 100000) 89 * cCG cZ 89) ≤ (25908946499291 / 500000000000000 : ℝ) := by
  have h0 := leC_86
  have h1 := kleC_87
  have h2 := kleC_88
  have h3 := leC_89
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_18 : (-27355561606683 / 200000000000000 : ℝ) ≤ Real.log 91 * (ex (57436 / 100000) 91 * cCG cZ 91) + kappa * (Real.log 92 * (ex (57436 / 100000) 92 * cCG cZ 92)) - kappa * (Real.log 93 * (ex (57436 / 100000) 93 * cCG cZ 93)) - Real.log 94 * (ex (57436 / 100000) 94 * cCG cZ 94) ∧ Real.log 91 * (ex (57436 / 100000) 91 * cCG cZ 91) + kappa * (Real.log 92 * (ex (57436 / 100000) 92 * cCG cZ 92)) - kappa * (Real.log 93 * (ex (57436 / 100000) 93 * cCG cZ 93)) - Real.log 94 * (ex (57436 / 100000) 94 * cCG cZ 94) ≤ (-136777528475339 / 1000000000000000 : ℝ) := by
  have h0 := leC_91
  have h1 := kleC_92
  have h2 := kleC_93
  have h3 := leC_94
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_19 : (83367164577617 / 200000000000000 : ℝ) ≤ Real.log 96 * (ex (57436 / 100000) 96 * cCG cZ 96) + kappa * (Real.log 97 * (ex (57436 / 100000) 97 * cCG cZ 97)) - kappa * (Real.log 98 * (ex (57436 / 100000) 98 * cCG cZ 98)) - Real.log 99 * (ex (57436 / 100000) 99 * cCG cZ 99) ∧ Real.log 96 * (ex (57436 / 100000) 96 * cCG cZ 96) + kappa * (Real.log 97 * (ex (57436 / 100000) 97 * cCG cZ 97)) - kappa * (Real.log 98 * (ex (57436 / 100000) 98 * cCG cZ 98)) - Real.log 99 * (ex (57436 / 100000) 99 * cCG cZ 99) ≤ (651306409983 / 1562500000000 : ℝ) := by
  have h0 := leC_96
  have h1 := kleC_97
  have h2 := kleC_98
  have h3 := leC_99
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_20 : (-242602876127009 / 500000000000000 : ℝ) ≤ Real.log 101 * (ex (57436 / 100000) 101 * cCG cZ 101) + kappa * (Real.log 102 * (ex (57436 / 100000) 102 * cCG cZ 102)) - kappa * (Real.log 103 * (ex (57436 / 100000) 103 * cCG cZ 103)) - Real.log 104 * (ex (57436 / 100000) 104 * cCG cZ 104) ∧ Real.log 101 * (ex (57436 / 100000) 101 * cCG cZ 101) + kappa * (Real.log 102 * (ex (57436 / 100000) 102 * cCG cZ 102)) - kappa * (Real.log 103 * (ex (57436 / 100000) 103 * cCG cZ 103)) - Real.log 104 * (ex (57436 / 100000) 104 * cCG cZ 104) ≤ (-242602736576273 / 500000000000000 : ℝ) := by
  have h0 := leC_101
  have h1 := kleC_102
  have h2 := kleC_103
  have h3 := leC_104
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_21 : (-1222749694089 / 5000000000000 : ℝ) ≤ Real.log 106 * (ex (57436 / 100000) 106 * cCG cZ 106) + kappa * (Real.log 107 * (ex (57436 / 100000) 107 * cCG cZ 107)) - kappa * (Real.log 108 * (ex (57436 / 100000) 108 * cCG cZ 108)) - Real.log 109 * (ex (57436 / 100000) 109 * cCG cZ 109) ∧ Real.log 106 * (ex (57436 / 100000) 106 * cCG cZ 106) + kappa * (Real.log 107 * (ex (57436 / 100000) 107 * cCG cZ 107)) - kappa * (Real.log 108 * (ex (57436 / 100000) 108 * cCG cZ 108)) - Real.log 109 * (ex (57436 / 100000) 109 * cCG cZ 109) ≤ (-122274830243883 / 500000000000000 : ℝ) := by
  have h0 := leC_106
  have h1 := kleC_107
  have h2 := kleC_108
  have h3 := leC_109
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_22 : (117453666803439 / 250000000000000 : ℝ) ≤ Real.log 111 * (ex (57436 / 100000) 111 * cCG cZ 111) + kappa * (Real.log 112 * (ex (57436 / 100000) 112 * cCG cZ 112)) - kappa * (Real.log 113 * (ex (57436 / 100000) 113 * cCG cZ 113)) - Real.log 114 * (ex (57436 / 100000) 114 * cCG cZ 114) ∧ Real.log 111 * (ex (57436 / 100000) 111 * cCG cZ 111) + kappa * (Real.log 112 * (ex (57436 / 100000) 112 * cCG cZ 112)) - kappa * (Real.log 113 * (ex (57436 / 100000) 113 * cCG cZ 113)) - Real.log 114 * (ex (57436 / 100000) 114 * cCG cZ 114) ≤ (58726867918461 / 125000000000000 : ℝ) := by
  have h0 := leC_111
  have h1 := kleC_112
  have h2 := kleC_113
  have h3 := leC_114
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_23 : (309531252988037 / 500000000000000 : ℝ) ≤ Real.log 116 * (ex (57436 / 100000) 116 * cCG cZ 116) + kappa * (Real.log 117 * (ex (57436 / 100000) 117 * cCG cZ 117)) - kappa * (Real.log 118 * (ex (57436 / 100000) 118 * cCG cZ 118)) - Real.log 119 * (ex (57436 / 100000) 119 * cCG cZ 119) ∧ Real.log 116 * (ex (57436 / 100000) 116 * cCG cZ 116) + kappa * (Real.log 117 * (ex (57436 / 100000) 117 * cCG cZ 117)) - kappa * (Real.log 118 * (ex (57436 / 100000) 118 * cCG cZ 118)) - Real.log 119 * (ex (57436 / 100000) 119 * cCG cZ 119) ≤ (309531389964409 / 500000000000000 : ℝ) := by
  have h0 := leC_116
  have h1 := kleC_117
  have h2 := kleC_118
  have h3 := leC_119
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_24 : (80562393783 / 200000000000 : ℝ) ≤ Real.log 121 * (ex (57436 / 100000) 121 * cCG cZ 121) + kappa * (Real.log 122 * (ex (57436 / 100000) 122 * cCG cZ 122)) - kappa * (Real.log 123 * (ex (57436 / 100000) 123 * cCG cZ 123)) - Real.log 124 * (ex (57436 / 100000) 124 * cCG cZ 124) ∧ Real.log 121 * (ex (57436 / 100000) 121 * cCG cZ 121) + kappa * (Real.log 122 * (ex (57436 / 100000) 122 * cCG cZ 122)) - kappa * (Real.log 123 * (ex (57436 / 100000) 123 * cCG cZ 123)) - Real.log 124 * (ex (57436 / 100000) 124 * cCG cZ 124) ≤ (201406119923277 / 500000000000000 : ℝ) := by
  have h0 := leC_121
  have h1 := kleC_122
  have h2 := kleC_123
  have h3 := leC_124
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_25 : (46912948478483 / 250000000000000 : ℝ) ≤ Real.log 126 * (ex (57436 / 100000) 126 * cCG cZ 126) + kappa * (Real.log 127 * (ex (57436 / 100000) 127 * cCG cZ 127)) - kappa * (Real.log 128 * (ex (57436 / 100000) 128 * cCG cZ 128)) - Real.log 129 * (ex (57436 / 100000) 129 * cCG cZ 129) ∧ Real.log 126 * (ex (57436 / 100000) 126 * cCG cZ 126) + kappa * (Real.log 127 * (ex (57436 / 100000) 127 * cCG cZ 127)) - kappa * (Real.log 128 * (ex (57436 / 100000) 128 * cCG cZ 128)) - Real.log 129 * (ex (57436 / 100000) 129 * cCG cZ 129) ≤ (93826030218681 / 500000000000000 : ℝ) := by
  have h0 := leC_126
  have h1 := kleC_127
  have h2 := kleC_128
  have h3 := leC_129
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_26 : (27546323130767 / 250000000000000 : ℝ) ≤ Real.log 131 * (ex (57436 / 100000) 131 * cCG cZ 131) + kappa * (Real.log 132 * (ex (57436 / 100000) 132 * cCG cZ 132)) - kappa * (Real.log 133 * (ex (57436 / 100000) 133 * cCG cZ 133)) - Real.log 134 * (ex (57436 / 100000) 134 * cCG cZ 134) ∧ Real.log 131 * (ex (57436 / 100000) 131 * cCG cZ 131) + kappa * (Real.log 132 * (ex (57436 / 100000) 132 * cCG cZ 132)) - kappa * (Real.log 133 * (ex (57436 / 100000) 133 * cCG cZ 133)) - Real.log 134 * (ex (57436 / 100000) 134 * cCG cZ 134) ≤ (110185555476503 / 1000000000000000 : ℝ) := by
  have h0 := leC_131
  have h1 := kleC_132
  have h2 := kleC_133
  have h3 := leC_134
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_27 : (184281935018353 / 1000000000000000 : ℝ) ≤ Real.log 136 * (ex (57436 / 100000) 136 * cCG cZ 136) + kappa * (Real.log 137 * (ex (57436 / 100000) 137 * cCG cZ 137)) - kappa * (Real.log 138 * (ex (57436 / 100000) 138 * cCG cZ 138)) - Real.log 139 * (ex (57436 / 100000) 139 * cCG cZ 139) ∧ Real.log 136 * (ex (57436 / 100000) 136 * cCG cZ 136) + kappa * (Real.log 137 * (ex (57436 / 100000) 137 * cCG cZ 137)) - kappa * (Real.log 138 * (ex (57436 / 100000) 138 * cCG cZ 138)) - Real.log 139 * (ex (57436 / 100000) 139 * cCG cZ 139) ≤ (92141097116511 / 500000000000000 : ℝ) := by
  have h0 := leC_136
  have h1 := kleC_137
  have h2 := kleC_138
  have h3 := leC_139
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_28 : (380421923470743 / 1000000000000000 : ℝ) ≤ Real.log 141 * (ex (57436 / 100000) 141 * cCG cZ 141) + kappa * (Real.log 142 * (ex (57436 / 100000) 142 * cCG cZ 142)) - kappa * (Real.log 143 * (ex (57436 / 100000) 143 * cCG cZ 143)) - Real.log 144 * (ex (57436 / 100000) 144 * cCG cZ 144) ∧ Real.log 141 * (ex (57436 / 100000) 141 * cCG cZ 141) + kappa * (Real.log 142 * (ex (57436 / 100000) 142 * cCG cZ 142)) - kappa * (Real.log 143 * (ex (57436 / 100000) 143 * cCG cZ 143)) - Real.log 144 * (ex (57436 / 100000) 144 * cCG cZ 144) ≤ (76084435928941 / 200000000000000 : ℝ) := by
  have h0 := leC_141
  have h1 := kleC_142
  have h2 := kleC_143
  have h3 := leC_144
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_29 : (595417015822513 / 1000000000000000 : ℝ) ≤ Real.log 146 * (ex (57436 / 100000) 146 * cCG cZ 146) + kappa * (Real.log 147 * (ex (57436 / 100000) 147 * cCG cZ 147)) - kappa * (Real.log 148 * (ex (57436 / 100000) 148 * cCG cZ 148)) - Real.log 149 * (ex (57436 / 100000) 149 * cCG cZ 149) ∧ Real.log 146 * (ex (57436 / 100000) 146 * cCG cZ 146) + kappa * (Real.log 147 * (ex (57436 / 100000) 147 * cCG cZ 147)) - kappa * (Real.log 148 * (ex (57436 / 100000) 148 * cCG cZ 148)) - Real.log 149 * (ex (57436 / 100000) 149 * cCG cZ 149) ≤ (297708634547261 / 500000000000000 : ℝ) := by
  have h0 := leC_146
  have h1 := kleC_147
  have h2 := kleC_148
  have h3 := leC_149
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_30 : (608512165836547 / 1000000000000000 : ℝ) ≤ Real.log 151 * (ex (57436 / 100000) 151 * cCG cZ 151) + kappa * (Real.log 152 * (ex (57436 / 100000) 152 * cCG cZ 152)) - kappa * (Real.log 153 * (ex (57436 / 100000) 153 * cCG cZ 153)) - Real.log 154 * (ex (57436 / 100000) 154 * cCG cZ 154) ∧ Real.log 151 * (ex (57436 / 100000) 151 * cCG cZ 151) + kappa * (Real.log 152 * (ex (57436 / 100000) 152 * cCG cZ 152)) - kappa * (Real.log 153 * (ex (57436 / 100000) 153 * cCG cZ 153)) - Real.log 154 * (ex (57436 / 100000) 154 * cCG cZ 154) ≤ (304256207786711 / 500000000000000 : ℝ) := by
  have h0 := leC_151
  have h1 := kleC_152
  have h2 := kleC_153
  have h3 := leC_154
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_31 : (208809964786249 / 1000000000000000 : ℝ) ≤ Real.log 156 * (ex (57436 / 100000) 156 * cCG cZ 156) + kappa * (Real.log 157 * (ex (57436 / 100000) 157 * cCG cZ 157)) - kappa * (Real.log 158 * (ex (57436 / 100000) 158 * cCG cZ 158)) - Real.log 159 * (ex (57436 / 100000) 159 * cCG cZ 159) ∧ Real.log 156 * (ex (57436 / 100000) 156 * cCG cZ 156) + kappa * (Real.log 157 * (ex (57436 / 100000) 157 * cCG cZ 157)) - kappa * (Real.log 158 * (ex (57436 / 100000) 158 * cCG cZ 158)) - Real.log 159 * (ex (57436 / 100000) 159 * cCG cZ 159) ≤ (208810211135711 / 1000000000000000 : ℝ) := by
  have h0 := leC_156
  have h1 := kleC_157
  have h2 := kleC_158
  have h3 := leC_159
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_32 : (-421547537889227 / 1000000000000000 : ℝ) ≤ Real.log 161 * (ex (57436 / 100000) 161 * cCG cZ 161) + kappa * (Real.log 162 * (ex (57436 / 100000) 162 * cCG cZ 162)) - kappa * (Real.log 163 * (ex (57436 / 100000) 163 * cCG cZ 163)) - Real.log 164 * (ex (57436 / 100000) 164 * cCG cZ 164) ∧ Real.log 161 * (ex (57436 / 100000) 161 * cCG cZ 161) + kappa * (Real.log 162 * (ex (57436 / 100000) 162 * cCG cZ 162)) - kappa * (Real.log 163 * (ex (57436 / 100000) 163 * cCG cZ 163)) - Real.log 164 * (ex (57436 / 100000) 164 * cCG cZ 164) ≤ (-52693411757401 / 125000000000000 : ℝ) := by
  have h0 := leC_161
  have h1 := kleC_162
  have h2 := kleC_163
  have h3 := leC_164
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_33 : (-561501849934529 / 1000000000000000 : ℝ) ≤ Real.log 166 * (ex (57436 / 100000) 166 * cCG cZ 166) + kappa * (Real.log 167 * (ex (57436 / 100000) 167 * cCG cZ 167)) - kappa * (Real.log 168 * (ex (57436 / 100000) 168 * cCG cZ 168)) - Real.log 169 * (ex (57436 / 100000) 169 * cCG cZ 169) ∧ Real.log 166 * (ex (57436 / 100000) 166 * cCG cZ 166) + kappa * (Real.log 167 * (ex (57436 / 100000) 167 * cCG cZ 167)) - kappa * (Real.log 168 * (ex (57436 / 100000) 168 * cCG cZ 168)) - Real.log 169 * (ex (57436 / 100000) 169 * cCG cZ 169) ≤ (-140375402190637 / 250000000000000 : ℝ) := by
  have h0 := leC_166
  have h1 := kleC_167
  have h2 := kleC_168
  have h3 := leC_169
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_34 : (33569039815567 / 250000000000000 : ℝ) ≤ Real.log 171 * (ex (57436 / 100000) 171 * cCG cZ 171) + kappa * (Real.log 172 * (ex (57436 / 100000) 172 * cCG cZ 172)) - kappa * (Real.log 173 * (ex (57436 / 100000) 173 * cCG cZ 173)) - Real.log 174 * (ex (57436 / 100000) 174 * cCG cZ 174) ∧ Real.log 171 * (ex (57436 / 100000) 171 * cCG cZ 171) + kappa * (Real.log 172 * (ex (57436 / 100000) 172 * cCG cZ 172)) - kappa * (Real.log 173 * (ex (57436 / 100000) 173 * cCG cZ 173)) - Real.log 174 * (ex (57436 / 100000) 174 * cCG cZ 174) ≤ (134276397428691 / 1000000000000000 : ℝ) := by
  have h0 := leC_171
  have h1 := kleC_172
  have h2 := kleC_173
  have h3 := leC_174
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_35 : (580228758777703 / 1000000000000000 : ℝ) ≤ Real.log 176 * (ex (57436 / 100000) 176 * cCG cZ 176) + kappa * (Real.log 177 * (ex (57436 / 100000) 177 * cCG cZ 177)) - kappa * (Real.log 178 * (ex (57436 / 100000) 178 * cCG cZ 178)) - Real.log 179 * (ex (57436 / 100000) 179 * cCG cZ 179) ∧ Real.log 176 * (ex (57436 / 100000) 176 * cCG cZ 176) + kappa * (Real.log 177 * (ex (57436 / 100000) 177 * cCG cZ 177)) - kappa * (Real.log 178 * (ex (57436 / 100000) 178 * cCG cZ 178)) - Real.log 179 * (ex (57436 / 100000) 179 * cCG cZ 179) ≤ (580228994767963 / 1000000000000000 : ℝ) := by
  have h0 := leC_176
  have h1 := kleC_177
  have h2 := kleC_178
  have h3 := leC_179
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_36 : (-152905399146537 / 1000000000000000 : ℝ) ≤ Real.log 181 * (ex (57436 / 100000) 181 * cCG cZ 181) + kappa * (Real.log 182 * (ex (57436 / 100000) 182 * cCG cZ 182)) - kappa * (Real.log 183 * (ex (57436 / 100000) 183 * cCG cZ 183)) - Real.log 184 * (ex (57436 / 100000) 184 * cCG cZ 184) ∧ Real.log 181 * (ex (57436 / 100000) 181 * cCG cZ 181) + kappa * (Real.log 182 * (ex (57436 / 100000) 182 * cCG cZ 182)) - kappa * (Real.log 183 * (ex (57436 / 100000) 183 * cCG cZ 183)) - Real.log 184 * (ex (57436 / 100000) 184 * cCG cZ 184) ≤ (-19113145761711 / 125000000000000 : ℝ) := by
  have h0 := leC_181
  have h1 := kleC_182
  have h2 := kleC_183
  have h3 := leC_184
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_37 : (-12562011211933 / 25000000000000 : ℝ) ≤ Real.log 186 * (ex (57436 / 100000) 186 * cCG cZ 186) + kappa * (Real.log 187 * (ex (57436 / 100000) 187 * cCG cZ 187)) - kappa * (Real.log 188 * (ex (57436 / 100000) 188 * cCG cZ 188)) - Real.log 189 * (ex (57436 / 100000) 189 * cCG cZ 189) ∧ Real.log 186 * (ex (57436 / 100000) 186 * cCG cZ 186) + kappa * (Real.log 187 * (ex (57436 / 100000) 187 * cCG cZ 187)) - kappa * (Real.log 188 * (ex (57436 / 100000) 188 * cCG cZ 188)) - Real.log 189 * (ex (57436 / 100000) 189 * cCG cZ 189) ≤ (-251240108717041 / 500000000000000 : ℝ) := by
  have h0 := leC_186
  have h1 := kleC_187
  have h2 := kleC_188
  have h3 := leC_189
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_38 : (8042073700171 / 20000000000000 : ℝ) ≤ Real.log 191 * (ex (57436 / 100000) 191 * cCG cZ 191) + kappa * (Real.log 192 * (ex (57436 / 100000) 192 * cCG cZ 192)) - kappa * (Real.log 193 * (ex (57436 / 100000) 193 * cCG cZ 193)) - Real.log 194 * (ex (57436 / 100000) 194 * cCG cZ 194) ∧ Real.log 191 * (ex (57436 / 100000) 191 * cCG cZ 191) + kappa * (Real.log 192 * (ex (57436 / 100000) 192 * cCG cZ 192)) - kappa * (Real.log 193 * (ex (57436 / 100000) 193 * cCG cZ 193)) - Real.log 194 * (ex (57436 / 100000) 194 * cCG cZ 194) ≤ (20105195678599 / 50000000000000 : ℝ) := by
  have h0 := leC_191
  have h1 := kleC_192
  have h2 := kleC_193
  have h3 := leC_194
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_39 : (169246517516019 / 1000000000000000 : ℝ) ≤ Real.log 196 * (ex (57436 / 100000) 196 * cCG cZ 196) + kappa * (Real.log 197 * (ex (57436 / 100000) 197 * cCG cZ 197)) - kappa * (Real.log 198 * (ex (57436 / 100000) 198 * cCG cZ 198)) - Real.log 199 * (ex (57436 / 100000) 199 * cCG cZ 199) ∧ Real.log 196 * (ex (57436 / 100000) 196 * cCG cZ 196) + kappa * (Real.log 197 * (ex (57436 / 100000) 197 * cCG cZ 197)) - kappa * (Real.log 198 * (ex (57436 / 100000) 198 * cCG cZ 198)) - Real.log 199 * (ex (57436 / 100000) 199 * cCG cZ 199) ≤ (169246743611839 / 1000000000000000 : ℝ) := by
  have h0 := leC_196
  have h1 := kleC_197
  have h2 := kleC_198
  have h3 := leC_199
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_40 : (-517220265497383 / 1000000000000000 : ℝ) ≤ Real.log 201 * (ex (57436 / 100000) 201 * cCG cZ 201) + kappa * (Real.log 202 * (ex (57436 / 100000) 202 * cCG cZ 202)) - kappa * (Real.log 203 * (ex (57436 / 100000) 203 * cCG cZ 203)) - Real.log 204 * (ex (57436 / 100000) 204 * cCG cZ 204) ∧ Real.log 201 * (ex (57436 / 100000) 201 * cCG cZ 201) + kappa * (Real.log 202 * (ex (57436 / 100000) 202 * cCG cZ 202)) - kappa * (Real.log 203 * (ex (57436 / 100000) 203 * cCG cZ 203)) - Real.log 204 * (ex (57436 / 100000) 204 * cCG cZ 204) ≤ (-517220041209009 / 1000000000000000 : ℝ) := by
  have h0 := leC_201
  have h1 := kleC_202
  have h2 := kleC_203
  have h3 := leC_204
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReT_1 : (5419023647177 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 206 * (cCG cZ 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (57436 / 100000) 206 * (cCG cZ 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (3386891691 / 156250000000 : ℝ) := by
  have hc := cCB_206
  have hs := sCB_206
  have hin : (28897071461017 / 62500000000000 : ℝ) ≤ cCG cZ 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (57794175471313 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (5419023647177 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 206 * (cCG cZ 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (57436 / 100000) 206 * (cCG cZ 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (3386891691 / 156250000000 : ℝ) :=
    mul_bounds_of exB_206 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem PReT_2 : (26543090831 / 25000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 207 * (cCG cZ 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (57436 / 100000) 207 * (cCG cZ 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (1061727062999 / 1000000000000000 : ℝ) := by
  have hc := cCB_207
  have hs := sCB_207
  have hin : (7994163291283 / 100000000000000 : ℝ) ≤ cCG cZ 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (9992736382299 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (3737423285037 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 207 * (cCG cZ 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (57436 / 100000) 207 * (cCG cZ 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (934358839573 / 250000000000000 : ℝ) :=
    mul_bounds_of exB_207 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PReT_3 : (-287239787981 / 62500000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 208 * (cCG cZ 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (57436 / 100000) 208 * (cCG cZ 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-919166641857 / 200000000000000 : ℝ) := by
  have hc := cCB_208
  have hs := sCB_208
  have hin : (-4337487663289 / 12500000000000 : ℝ) ≤ cCG cZ 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-433748446109 / 1250000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-16178020545147 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 208 * (cCG cZ 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (57436 / 100000) 208 * (cCG cZ 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-16178008582241 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_208 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PReT_4 : (-12890221168939 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 209 * (cCG cZ 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (57436 / 100000) 209 * (cCG cZ 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-161127690561 / 6250000000000 : ℝ) := by
  have hc := cCB_209
  have hs := sCB_209
  have hin : (-277242361718119 / 500000000000000 : ℝ) ≤ cCG cZ 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-554484469268869 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-12890221168939 / 500000000000000 : ℝ) ≤ ex (57436 / 100000) 209 * (cCG cZ 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (57436 / 100000) 209 * (cCG cZ 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-161127690561 / 6250000000000 : ℝ) :=
    mul_bounds_of exB_209 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem PImT_1 : (-1904488357679 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 206 * (cCG cZ 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (57436 / 100000) 206 * (cCG cZ 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-15235894635413 / 1000000000000000 : ℝ) := by
  have hc := cCB_206
  have hs := sCB_206
  have hin : (-324983330938089 / 1000000000000000 : ℝ) ≤ cCG cZ 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-6499661410873 / 20000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-1904488357679 / 125000000000000 : ℝ) ≤ ex (57436 / 100000) 206 * (cCG cZ 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (57436 / 100000) 206 * (cCG cZ 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-15235894635413 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_206 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem PImT_2 : (-7392281223007 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 207 * (cCG cZ 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (57436 / 100000) 207 * (cCG cZ 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-1478455557139 / 200000000000000 : ℝ) := by
  have hc := cCB_207
  have hs := sCB_207
  have hin : (-34787244339749 / 62500000000000 : ℝ) ≤ cCG cZ 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-278297825645211 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-6505479182019 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 207 * (cCG cZ 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (57436 / 100000) 207 * (cCG cZ 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-26021904628237 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_207 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PImT_3 : (-36339898493 / 6250000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 208 * (cCG cZ 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (57436 / 100000) 208 * (cCG cZ 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-726797544877 / 125000000000000 : ℝ) := by
  have hc := cCB_208
  have hs := sCB_208
  have hin : (-54875357800011 / 125000000000000 : ℝ) ≤ cCG cZ 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-87800521244851 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-81869942679 / 4000000000000 : ℝ) ≤ ex (57436 / 100000) 208 * (cCG cZ 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (57436 / 100000) 208 * (cCG cZ 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-5116868425433 / 250000000000000 : ℝ) :=
    mul_bounds_of exB_208 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PImT_4 : (-2438707558503 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 209 * (cCG cZ 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (57436 / 100000) 209 * (cCG cZ 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-243869573823 / 100000000000000 : ℝ) := by
  have hc := cCB_209
  have hs := sCB_209
  have hin : (-26225812350231 / 500000000000000 : ℝ) ≤ cCG cZ 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-26225685266547 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-2438707558503 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 209 * (cCG cZ 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (57436 / 100000) 209 * (cCG cZ 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-243869573823 / 100000000000000 : ℝ) :=
    mul_bounds_of exB_209 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem AReT_1 : (-23066194129399 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 206 * (cCG cZ 206 * ((170983675899732393669583331391220591411275937452226326468677071989820256226003329824031119505825507046103022521440589856288685855207497921126702554713242542946967917146646651755905739691158398103 / 23009248742640722263749099163524768417316678885546836609262664834473421199305323899043400822605176436162560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 206 * ((-6225750268062212788573036609112628114194053793677135785502547225253995225810743549801919315435735233458460509744533941521729343672886250394574883356393445238279160586844653643173767617013857487 / 15750378603593351549590157165508025999948917094273132202769086047407401416191144335654708896426162441420800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (57436 / 100000) 206 * (cCG cZ 206 * ((170983675899732393669583331391220591411275937452226326468677071989820256226003329824031119505825507046103022521440589856288685855207497921126702554713242542946967917146646651755905739691158398103 / 23009248742640722263749099163524768417316678885546836609262664834473421199305323899043400822605176436162560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 206 * ((-6225750268062212788573036609112628114194053793677135785502547225253995225810743549801919315435735233458460509744533941521729343672886250394574883356393445238279160586844653643173767617013857487 / 15750378603593351549590157165508025999948917094273132202769086047407401416191144335654708896426162441420800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-1802045399013 / 15625000000000 : ℝ) := by
  have hc := cCB_206
  have hs := sCB_206
  have hl := lgB_206
  have hv1 : (-2717601801624673 / 1000000000000000 : ℝ) ≤ (170983675899732393669583331391220591411275937452226326468677071989820256226003329824031119505825507046103022521440589856288685855207497921126702554713242542946967917146646651755905739691158398103 / 23009248742640722263749099163524768417316678885546836609262664834473421199305323899043400822605176436162560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (170983675899732393669583331391220591411275937452226326468677071989820256226003329824031119505825507046103022521440589856288685855207497921126702554713242542946967917146646651755905739691158398103 / 23009248742640722263749099163524768417316678885546836609262664834473421199305323899043400822605176436162560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1358800900281433 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-1281149881458649 / 1000000000000000 : ℝ) ≤ (-6225750268062212788573036609112628114194053793677135785502547225253995225810743549801919315435735233458460509744533941521729343672886250394574883356393445238279160586844653643173767617013857487 / 15750378603593351549590157165508025999948917094273132202769086047407401416191144335654708896426162441420800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-6225750268062212788573036609112628114194053793677135785502547225253995225810743549801919315435735233458460509744533941521729343672886250394574883356393445238279160586844653643173767617013857487 / 15750378603593351549590157165508025999948917094273132202769086047407401416191144335654708896426162441420800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-320287470239901 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (-1347435609808269 / 1000000000000000 : ℝ) ≤ cCG cZ 206 * ((170983675899732393669583331391220591411275937452226326468677071989820256226003329824031119505825507046103022521440589856288685855207497921126702554713242542946967917146646651755905739691158398103 / 23009248742640722263749099163524768417316678885546836609262664834473421199305323899043400822605176436162560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 206 * ((170983675899732393669583331391220591411275937452226326468677071989820256226003329824031119505825507046103022521440589856288685855207497921126702554713242542946967917146646651755905739691158398103 / 23009248742640722263749099163524768417316678885546836609262664834473421199305323899043400822605176436162560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-42107333377477 / 31250000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (-556292438072057 / 500000000000000 : ℝ) ≤ sCG cZ 206 * ((-6225750268062212788573036609112628114194053793677135785502547225253995225810743549801919315435735233458460509744533941521729343672886250394574883356393445238279160586844653643173767617013857487 / 15750378603593351549590157165508025999948917094273132202769086047407401416191144335654708896426162441420800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sCG cZ 206 * ((-6225750268062212788573036609112628114194053793677135785502547225253995225810743549801919315435735233458460509744533941521729343672886250394574883356393445238279160586844653643173767617013857487 / 15750378603593351549590157165508025999948917094273132202769086047407401416191144335654708896426162441420800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-278146108000451 / 250000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (-2460020485952383 / 1000000000000000 : ℝ) ≤ cCG cZ 206 * ((170983675899732393669583331391220591411275937452226326468677071989820256226003329824031119505825507046103022521440589856288685855207497921126702554713242542946967917146646651755905739691158398103 / 23009248742640722263749099163524768417316678885546836609262664834473421199305323899043400822605176436162560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 206 * ((-6225750268062212788573036609112628114194053793677135785502547225253995225810743549801919315435735233458460509744533941521729343672886250394574883356393445238279160586844653643173767617013857487 / 15750378603593351549590157165508025999948917094273132202769086047407401416191144335654708896426162441420800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 206 * ((170983675899732393669583331391220591411275937452226326468677071989820256226003329824031119505825507046103022521440589856288685855207497921126702554713242542946967917146646651755905739691158398103 / 23009248742640722263749099163524768417316678885546836609262664834473421199305323899043400822605176436162560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 206 * ((-6225750268062212788573036609112628114194053793677135785502547225253995225810743549801919315435735233458460509744533941521729343672886250394574883356393445238279160586844653643173767617013857487 / 15750378603593351549590157165508025999948917094273132202769086047407401416191144335654708896426162441420800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-615004775020267 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (-23066194129399 / 200000000000000 : ℝ) ≤ ex (57436 / 100000) 206 * (cCG cZ 206 * ((170983675899732393669583331391220591411275937452226326468677071989820256226003329824031119505825507046103022521440589856288685855207497921126702554713242542946967917146646651755905739691158398103 / 23009248742640722263749099163524768417316678885546836609262664834473421199305323899043400822605176436162560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 206 * ((-6225750268062212788573036609112628114194053793677135785502547225253995225810743549801919315435735233458460509744533941521729343672886250394574883356393445238279160586844653643173767617013857487 / 15750378603593351549590157165508025999948917094273132202769086047407401416191144335654708896426162441420800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (57436 / 100000) 206 * (cCG cZ 206 * ((170983675899732393669583331391220591411275937452226326468677071989820256226003329824031119505825507046103022521440589856288685855207497921126702554713242542946967917146646651755905739691158398103 / 23009248742640722263749099163524768417316678885546836609262664834473421199305323899043400822605176436162560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (447169210721456688383996233028487679669316318976370798592361348216013037598717336980288110326264715915825533919713981212259476545504615324594468826703279371290104248175264690057113632243 / 874287497197890665055513028010344146599939689525605210148693451258280489706422036867317760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 206 * ((-6225750268062212788573036609112628114194053793677135785502547225253995225810743549801919315435735233458460509744533941521729343672886250394574883356393445238279160586844653643173767617013857487 / 15750378603593351549590157165508025999948917094273132202769086047407401416191144335654708896426162441420800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (52962272589118157955307762035811480301866802117829084409578721375797180154502173315629616087294401971192154457511166020635595612959181754577287192448887555737916038775684025638021601526999 / 220320449293868447593989283058606724943184801760452512957470749717086683406018353290564075520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-1802045399013 / 15625000000000 : ℝ) :=
    mul_bounds_of exB_206 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem AReT_2 : (-1138861789757 / 200000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 207 * (cCG cZ 207 * ((148858774669601223576758530327724797379397660631149373900883329221154732569416043285414660374382709177505514626830784706388257818252677581985848142850236836804722713699639297341074481581207148368669 / 20310383419972665815737681881794403827728483792459662840815744529173598869153774040333536768151377022277386240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 207 * ((-82249552774837289084744260226508593286590214241160836654297943627777827201281522829979945569810224074461534592921786522191293056025643868979991129047988098822639282512613824043279979656536989 / 217202909458496588724672778196216867586029162950007516306655037057192466047620908837815657650952391884800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ∧ kappa * (ex (57436 / 100000) 207 * (cCG cZ 207 * ((148858774669601223576758530327724797379397660631149373900883329221154732569416043285414660374382709177505514626830784706388257818252677581985848142850236836804722713699639297341074481581207148368669 / 20310383419972665815737681881794403827728483792459662840815744529173598869153774040333536768151377022277386240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 207 * ((-82249552774837289084744260226508593286590214241160836654297943627777827201281522829979945569810224074461534592921786522191293056025643868979991129047988098822639282512613824043279979656536989 / 217202909458496588724672778196216867586029162950007516306655037057192466047620908837815657650952391884800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ≤ (-5694290680577 / 1000000000000000 : ℝ) := by
  have hc := cCB_207
  have hs := sCB_207
  have hl := lgB_207
  have hv1 : (-169889429632633 / 62500000000000 : ℝ) ≤ (148858774669601223576758530327724797379397660631149373900883329221154732569416043285414660374382709177505514626830784706388257818252677581985848142850236836804722713699639297341074481581207148368669 / 20310383419972665815737681881794403827728483792459662840815744529173598869153774040333536768151377022277386240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (148858774669601223576758530327724797379397660631149373900883329221154732569416043285414660374382709177505514626830784706388257818252677581985848142850236836804722713699639297341074481581207148368669 / 20310383419972665815737681881794403827728483792459662840815744529173598869153774040333536768151377022277386240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-67955771826527 / 25000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-1250612978680543 / 1000000000000000 : ℝ) ≤ (-82249552774837289084744260226508593286590214241160836654297943627777827201281522829979945569810224074461534592921786522191293056025643868979991129047988098822639282512613824043279979656536989 / 217202909458496588724672778196216867586029162950007516306655037057192466047620908837815657650952391884800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-82249552774837289084744260226508593286590214241160836654297943627777827201281522829979945569810224074461534592921786522191293056025643868979991129047988098822639282512613824043279979656536989 / 217202909458496588724672778196216867586029162950007516306655037057192466047620908837815657650952391884800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-156326622274229 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (77056245069809 / 100000000000000 : ℝ) ≤ cCG cZ 207 * ((148858774669601223576758530327724797379397660631149373900883329221154732569416043285414660374382709177505514626830784706388257818252677581985848142850236836804722713699639297341074481581207148368669 / 20310383419972665815737681881794403827728483792459662840815744529173598869153774040333536768151377022277386240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 207 * ((148858774669601223576758530327724797379397660631149373900883329221154732569416043285414660374382709177505514626830784706388257818252677581985848142850236836804722713699639297341074481581207148368669 / 20310383419972665815737681881794403827728483792459662840815744529173598869153774040333536768151377022277386240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (770563392185553 / 1000000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (-1199310894154799 / 1000000000000000 : ℝ) ≤ sCG cZ 207 * ((-82249552774837289084744260226508593286590214241160836654297943627777827201281522829979945569810224074461534592921786522191293056025643868979991129047988098822639282512613824043279979656536989 / 217202909458496588724672778196216867586029162950007516306655037057192466047620908837815657650952391884800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sCG cZ 207 * ((-82249552774837289084744260226508593286590214241160836654297943627777827201281522829979945569810224074461534592921786522191293056025643868979991129047988098822639282512613824043279979656536989 / 217202909458496588724672778196216867586029162950007516306655037057192466047620908837815657650952391884800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-1199310460663659 / 1000000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (-428748443456709 / 1000000000000000 : ℝ) ≤ cCG cZ 207 * ((148858774669601223576758530327724797379397660631149373900883329221154732569416043285414660374382709177505514626830784706388257818252677581985848142850236836804722713699639297341074481581207148368669 / 20310383419972665815737681881794403827728483792459662840815744529173598869153774040333536768151377022277386240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 207 * ((-82249552774837289084744260226508593286590214241160836654297943627777827201281522829979945569810224074461534592921786522191293056025643868979991129047988098822639282512613824043279979656536989 / 217202909458496588724672778196216867586029162950007516306655037057192466047620908837815657650952391884800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 207 * ((148858774669601223576758530327724797379397660631149373900883329221154732569416043285414660374382709177505514626830784706388257818252677581985848142850236836804722713699639297341074481581207148368669 / 20310383419972665815737681881794403827728483792459662840815744529173598869153774040333536768151377022277386240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 207 * ((-82249552774837289084744260226508593286590214241160836654297943627777827201281522829979945569810224074461534592921786522191293056025643868979991129047988098822639282512613824043279979656536989 / 217202909458496588724672778196216867586029162950007516306655037057192466047620908837815657650952391884800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-214373534239053 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (-1252800292791 / 62500000000000 : ℝ) ≤ ex (57436 / 100000) 207 * (cCG cZ 207 * ((148858774669601223576758530327724797379397660631149373900883329221154732569416043285414660374382709177505514626830784706388257818252677581985848142850236836804722713699639297341074481581207148368669 / 20310383419972665815737681881794403827728483792459662840815744529173598869153774040333536768151377022277386240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 207 * ((-82249552774837289084744260226508593286590214241160836654297943627777827201281522829979945569810224074461534592921786522191293056025643868979991129047988098822639282512613824043279979656536989 / 217202909458496588724672778196216867586029162950007516306655037057192466047620908837815657650952391884800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (57436 / 100000) 207 * (cCG cZ 207 * ((148858774669601223576758530327724797379397660631149373900883329221154732569416043285414660374382709177505514626830784706388257818252677581985848142850236836804722713699639297341074481581207148368669 / 20310383419972665815737681881794403827728483792459662840815744529173598869153774040333536768151377022277386240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (82847392529585502428614101891324027628943171540773924268307176632227704868371588219522919481771727092909880350715267810305847826360673229383218993335307725704666983080056504342973758649 / 162095802673457629632536972805946656219102283369452690194761246645247404233820253863280640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 207 * ((-82249552774837289084744260226508593286590214241160836654297943627777827201281522829979945569810224074461534592921786522191293056025643868979991129047988098822639282512613824043279979656536989 / 217202909458496588724672778196216867586029162950007516306655037057192466047620908837815657650952391884800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5947119122884369610165178182703783904063270338242538647030734872475828710520938811707135863862536920213426885157499633310868646188581487892191813933610162564791801235313900122914992957280897 / 25366696351974731376454975948348204125039754529052390393958577010008056783358999167572513914880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-501118509447 / 25000000000000 : ℝ) :=
    mul_bounds_of exB_207 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem AReT_3 : (24443308329813 / 1000000000000000 : ℝ) ≤ kappa * (ex (57436 / 100000) 208 * (cCG cZ 208 * ((21401806043902284095078780481247211407456060582541433200139750357372200907597206964764550200473834746787356755878695404020091133903676001761079172370387871390157979727858563373576485151747715004609 / 2959717766289936479105137759577332722707510190411211203414064652037957607283629886955015008723569339017461760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 208 * ((-735446503934527145287192395967173143559982529304347245255175704099447268329760062707061342143130536463453210788680927247289371956150494136242996306562938264750715162099805104511045498152427321161 / 2025997280496087470816016918758293232805736142245769573765579970145030504985818077379920988114348059446476800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ∧ kappa * (ex (57436 / 100000) 208 * (cCG cZ 208 * ((21401806043902284095078780481247211407456060582541433200139750357372200907597206964764550200473834746787356755878695404020091133903676001761079172370387871390157979727858563373576485151747715004609 / 2959717766289936479105137759577332722707510190411211203414064652037957607283629886955015008723569339017461760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 208 * ((-735446503934527145287192395967173143559982529304347245255175704099447268329760062707061342143130536463453210788680927247289371956150494136242996306562938264750715162099805104511045498152427321161 / 2025997280496087470816016918758293232805736142245769573765579970145030504985818077379920988114348059446476800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ≤ (3055415806587 / 125000000000000 : ℝ) := by
  have hc := cCB_208
  have hs := sCB_208
  have hl := lgB_208
  have hv1 : (-2718928087742259 / 1000000000000000 : ℝ) ≤ (21401806043902284095078780481247211407456060582541433200139750357372200907597206964764550200473834746787356755878695404020091133903676001761079172370387871390157979727858563373576485151747715004609 / 2959717766289936479105137759577332722707510190411211203414064652037957607283629886955015008723569339017461760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (21401806043902284095078780481247211407456060582541433200139750357372200907597206964764550200473834746787356755878695404020091133903676001761079172370387871390157979727858563373576485151747715004609 / 2959717766289936479105137759577332722707510190411211203414064652037957607283629886955015008723569339017461760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-169933005417621 / 62500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-244118606874587 / 200000000000000 : ℝ) ≤ (-735446503934527145287192395967173143559982529304347245255175704099447268329760062707061342143130536463453210788680927247289371956150494136242996306562938264750715162099805104511045498152427321161 / 2025997280496087470816016918758293232805736142245769573765579970145030504985818077379920988114348059446476800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-735446503934527145287192395967173143559982529304347245255175704099447268329760062707061342143130536463453210788680927247289371956150494136242996306562938264750715162099805104511045498152427321161 / 2025997280496087470816016918758293232805736142245769573765579970145030504985818077379920988114348059446476800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1220593033898333 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (150646084207977 / 62500000000000 : ℝ) ≤ cCG cZ 208 * ((21401806043902284095078780481247211407456060582541433200139750357372200907597206964764550200473834746787356755878695404020091133903676001761079172370387871390157979727858563373576485151747715004609 / 2959717766289936479105137759577332722707510190411211203414064652037957607283629886955015008723569339017461760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 208 * ((21401806043902284095078780481247211407456060582541433200139750357372200907597206964764550200473834746787356755878695404020091133903676001761079172370387871390157979727858563373576485151747715004609 / 2959717766289936479105137759577332722707510190411211203414064652037957607283629886955015008723569339017461760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (2410338290324701 / 1000000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (-564796567579679 / 1000000000000000 : ℝ) ≤ sCG cZ 208 * ((-735446503934527145287192395967173143559982529304347245255175704099447268329760062707061342143130536463453210788680927247289371956150494136242996306562938264750715162099805104511045498152427321161 / 2025997280496087470816016918758293232805736142245769573765579970145030504985818077379920988114348059446476800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sCG cZ 208 * ((-735446503934527145287192395967173143559982529304347245255175704099447268329760062707061342143130536463453210788680927247289371956150494136242996306562938264750715162099805104511045498152427321161 / 2025997280496087470816016918758293232805736142245769573765579970145030504985818077379920988114348059446476800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-141199036112019 / 250000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (1845540779747953 / 1000000000000000 : ℝ) ≤ cCG cZ 208 * ((21401806043902284095078780481247211407456060582541433200139750357372200907597206964764550200473834746787356755878695404020091133903676001761079172370387871390157979727858563373576485151747715004609 / 2959717766289936479105137759577332722707510190411211203414064652037957607283629886955015008723569339017461760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 208 * ((-735446503934527145287192395967173143559982529304347245255175704099447268329760062707061342143130536463453210788680927247289371956150494136242996306562938264750715162099805104511045498152427321161 / 2025997280496087470816016918758293232805736142245769573765579970145030504985818077379920988114348059446476800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 208 * ((21401806043902284095078780481247211407456060582541433200139750357372200907597206964764550200473834746787356755878695404020091133903676001761079172370387871390157979727858563373576485151747715004609 / 2959717766289936479105137759577332722707510190411211203414064652037957607283629886955015008723569339017461760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 208 * ((-735446503934527145287192395967173143559982529304347245255175704099447268329760062707061342143130536463453210788680927247289371956150494136242996306562938264750715162099805104511045498152427321161 / 2025997280496087470816016918758293232805736142245769573765579970145030504985818077379920988114348059446476800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (14764337167013 / 8000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (21511009752223 / 250000000000000 : ℝ) ≤ ex (57436 / 100000) 208 * (cCG cZ 208 * ((21401806043902284095078780481247211407456060582541433200139750357372200907597206964764550200473834746787356755878695404020091133903676001761079172370387871390157979727858563373576485151747715004609 / 2959717766289936479105137759577332722707510190411211203414064652037957607283629886955015008723569339017461760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 208 * ((-735446503934527145287192395967173143559982529304347245255175704099447268329760062707061342143130536463453210788680927247289371956150494136242996306562938264750715162099805104511045498152427321161 / 2025997280496087470816016918758293232805736142245769573765579970145030504985818077379920988114348059446476800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (57436 / 100000) 208 * (cCG cZ 208 * ((21401806043902284095078780481247211407456060582541433200139750357372200907597206964764550200473834746787356755878695404020091133903676001761079172370387871390157979727858563373576485151747715004609 / 2959717766289936479105137759577332722707510190411211203414064652037957607283629886955015008723569339017461760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (57439723699542570552029846917316485437510455775388083457949610096401626754329508387717525806028846407188564997633335711938993718073099264969671362545219768388061799414972935299306704121029 / 112461048478577213348496796527021154974052065491009797423897639613548487882588943966755880960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 208 * ((-735446503934527145287192395967173143559982529304347245255175704099447268329760062707061342143130536463453210788680927247289371956150494136242996306562938264750715162099805104511045498152427321161 / 2025997280496087470816016918758293232805736142245769573765579970145030504985818077379920988114348059446476800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (6478931541283739411744166585573366208191596274322018676792725052719825199184678748525956983518429375019294155744658063070682297177846964264526041346078682195944672147070504810354432957280897 / 28340184216601457763821192724809331053461120503734468950822205182614218946412413879622482001920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (86044102804103 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_208 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem AReT_4 : (137417499721947 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 209 * (cCG cZ 209 * ((542457698283911028455868439103756814596360942281113129938133285265224294217796359312192227163412964504852878221553618397166979786073847298384292481488837362653771404357514519147644638568082245106007 / 76012674228970167518672550423477510989446917369342585187521194756389614104878634792529263561226326361935708160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 209 * ((-787725423223119794977296699200209269497802345711274711190014180864862043767433674150850416621864060192731585800361034637583117411299874643120776861096676541621151018006472739033600908552427321161 / 2262281971100302604722397334032068779447824921706624559152416510606833753121387940253847129798402570295705600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (57436 / 100000) 209 * (cCG cZ 209 * ((542457698283911028455868439103756814596360942281113129938133285265224294217796359312192227163412964504852878221553618397166979786073847298384292481488837362653771404357514519147644638568082245106007 / 76012674228970167518672550423477510989446917369342585187521194756389614104878634792529263561226326361935708160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 209 * ((-787725423223119794977296699200209269497802345711274711190014180864862043767433674150850416621864060192731585800361034637583117411299874643120776861096676541621151018006472739033600908552427321161 / 2262281971100302604722397334032068779447824921706624559152416510606833753121387940253847129798402570295705600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (34354390740577 / 250000000000000 : ℝ) := by
  have hc := cCB_209
  have hs := sCB_209
  have hl := lgB_209
  have hv1 : (-2719688947754467 / 1000000000000000 : ℝ) ≤ (542457698283911028455868439103756814596360942281113129938133285265224294217796359312192227163412964504852878221553618397166979786073847298384292481488837362653771404357514519147644638568082245106007 / 76012674228970167518672550423477510989446917369342585187521194756389614104878634792529263561226326361935708160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (542457698283911028455868439103756814596360942281113129938133285265224294217796359312192227163412964504852878221553618397166979786073847298384292481488837362653771404357514519147644638568082245106007 / 76012674228970167518672550423477510989446917369342585187521194756389614104878634792529263561226326361935708160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-2719688946694837 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-595535545696297 / 500000000000000 : ℝ) ≤ (-787725423223119794977296699200209269497802345711274711190014180864862043767433674150850416621864060192731585800361034637583117411299874643120776861096676541621151018006472739033600908552427321161 / 2262281971100302604722397334032068779447824921706624559152416510606833753121387940253847129798402570295705600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-787725423223119794977296699200209269497802345711274711190014180864862043767433674150850416621864060192731585800361034637583117411299874643120776861096676541621151018006472739033600908552427321161 / 2262281971100302604722397334032068779447824921706624559152416510606833753121387940253847129798402570295705600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-238214218185977 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (1291920460822433 / 500000000000000 : ℝ) ≤ cCG cZ 209 * ((542457698283911028455868439103756814596360942281113129938133285265224294217796359312192227163412964504852878221553618397166979786073847298384292481488837362653771404357514519147644638568082245106007 / 76012674228970167518672550423477510989446917369342585187521194756389614104878634792529263561226326361935708160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 209 * ((542457698283911028455868439103756814596360942281113129938133285265224294217796359312192227163412964504852878221553618397166979786073847298384292481488837362653771404357514519147644638568082245106007 / 76012674228970167518672550423477510989446917369342585187521194756389614104878634792529263561226326361935708160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (322980233164123 / 125000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (37172917373593 / 100000000000000 : ℝ) ≤ sCG cZ 209 * ((-787725423223119794977296699200209269497802345711274711190014180864862043767433674150850416621864060192731585800361034637583117411299874643120776861096676541621151018006472739033600908552427321161 / 2262281971100302604722397334032068779447824921706624559152416510606833753121387940253847129798402570295705600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sCG cZ 209 * ((-787725423223119794977296699200209269497802345711274711190014180864862043767433674150850416621864060192731585800361034637583117411299874643120776861096676541621151018006472739033600908552427321161 / 2262281971100302604722397334032068779447824921706624559152416510606833753121387940253847129798402570295705600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (371729586713123 / 1000000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (738892523845199 / 250000000000000 : ℝ) ≤ cCG cZ 209 * ((542457698283911028455868439103756814596360942281113129938133285265224294217796359312192227163412964504852878221553618397166979786073847298384292481488837362653771404357514519147644638568082245106007 / 76012674228970167518672550423477510989446917369342585187521194756389614104878634792529263561226326361935708160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 209 * ((-787725423223119794977296699200209269497802345711274711190014180864862043767433674150850416621864060192731585800361034637583117411299874643120776861096676541621151018006472739033600908552427321161 / 2262281971100302604722397334032068779447824921706624559152416510606833753121387940253847129798402570295705600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 209 * ((542457698283911028455868439103756814596360942281113129938133285265224294217796359312192227163412964504852878221553618397166979786073847298384292481488837362653771404357514519147644638568082245106007 / 76012674228970167518672550423477510989446917369342585187521194756389614104878634792529263561226326361935708160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 209 * ((-787725423223119794977296699200209269497802345711274711190014180864862043767433674150850416621864060192731585800361034637583117411299874643120776861096676541621151018006472739033600908552427321161 / 2262281971100302604722397334032068779447824921706624559152416510606833753121387940253847129798402570295705600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (2955571452026107 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (137417499721947 / 1000000000000000 : ℝ) ≤ ex (57436 / 100000) 209 * (cCG cZ 209 * ((542457698283911028455868439103756814596360942281113129938133285265224294217796359312192227163412964504852878221553618397166979786073847298384292481488837362653771404357514519147644638568082245106007 / 76012674228970167518672550423477510989446917369342585187521194756389614104878634792529263561226326361935708160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 209 * ((-787725423223119794977296699200209269497802345711274711190014180864862043767433674150850416621864060192731585800361034637583117411299874643120776861096676541621151018006472739033600908552427321161 / 2262281971100302604722397334032068779447824921706624559152416510606833753121387940253847129798402570295705600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (57436 / 100000) 209 * (cCG cZ 209 * ((542457698283911028455868439103756814596360942281113129938133285265224294217796359312192227163412964504852878221553618397166979786073847298384292481488837362653771404357514519147644638568082245106007 / 76012674228970167518672550423477510989446917369342585187521194756389614104878634792529263561226326361935708160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (64096788723466245270376114449665663824776351265571236379994481689566695922465148314538810687173844539090111010644340533227068461013136816174101461257914918134443169817286601382842704121029 / 125576971338197050036531300239035022142802298158426199307640716505873719729163062321946296320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 209 * ((-787725423223119794977296699200209269497802345711274711190014180864862043767433674150850416621864060192731585800361034637583117411299874643120776861096676541621151018006472739033600908552427321161 / 2262281971100302604722397334032068779447824921706624559152416510606833753121387940253847129798402570295705600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (7053264842169680389964751648191707721767355434439634179975864686314853443245057520055710121390729122534646594016553573288392222294277139260510136917733536070625064138765115103034544957280897 / 31645396777225656609205887660236825579986179135923402225525460559480177371749091705130466672640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (34354390740577 / 250000000000000 : ℝ) :=
    mul_bounds_of exB_209 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

/-- Lower end of the enclosure of `Re fEM(c)`. -/
theorem PReG_ge : (1986776241 / 1000000000000000 : ℝ) ≤ PReG cZ 41 12 := by
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
  have b28 := PReB_28
  have b29 := PReB_29
  have b30 := PReB_30
  have b31 := PReB_31
  have b32 := PReB_32
  have b33 := PReB_33
  have b34 := PReB_34
  have b35 := PReB_35
  have b36 := PReB_36
  have b37 := PReB_37
  have b38 := PReB_38
  have b39 := PReB_39
  have b40 := PReB_40
  have t1 := PReT_1
  have t2 := PReT_2
  have t3 := PReT_3
  have t4 := PReT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b29.1, b29.2, b30.1, b30.2, b31.1, b31.2, b32.1, b32.2, b33.1, b33.2, b34.1, b34.2, b35.1, b35.2, b36.1, b36.2, b37.1, b37.2, b38.1, b38.2, b39.1, b39.2, b40.1, b40.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- Upper end of the enclosure of `Re fEM(c)`. -/
theorem PReG_le : PReG cZ 41 12 ≤ (160361159 / 40000000000000 : ℝ) := by
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
  have b28 := PReB_28
  have b29 := PReB_29
  have b30 := PReB_30
  have b31 := PReB_31
  have b32 := PReB_32
  have b33 := PReB_33
  have b34 := PReB_34
  have b35 := PReB_35
  have b36 := PReB_36
  have b37 := PReB_37
  have b38 := PReB_38
  have b39 := PReB_39
  have b40 := PReB_40
  have t1 := PReT_1
  have t2 := PReT_2
  have t3 := PReT_3
  have t4 := PReT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b29.1, b29.2, b30.1, b30.2, b31.1, b31.2, b32.1, b32.2, b33.1, b33.2, b34.1, b34.2, b35.1, b35.2, b36.1, b36.2, b37.1, b37.2, b38.1, b38.2, b39.1, b39.2, b40.1, b40.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- **The enclosure of `Re fEM(c)`**: `PReG cZ 41 12 ∈ [1.9867762410e-06, 4.0090289750e-06]` (width `2.02e-06`). -/
theorem PReG_mem : (1986776241 / 1000000000000000 : ℝ) ≤ PReG cZ 41 12 ∧ PReG cZ 41 12 ≤ (160361159 / 40000000000000 : ℝ) := ⟨PReG_ge, PReG_le⟩

/-- Open inequality `H1` of `DHLocate3Base`. -/
theorem H1 : |PReG cZ 41 12| ≤ (9 / 100000 : ℝ) := by
  have h := PReG_mem
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Lower end of the enclosure of `Im fEM(c)`. -/
theorem PImG_ge : (1450070641 / 1000000000000000 : ℝ) ≤ PImG cZ 41 12 := by
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
  have b28 := PImB_28
  have b29 := PImB_29
  have b30 := PImB_30
  have b31 := PImB_31
  have b32 := PImB_32
  have b33 := PImB_33
  have b34 := PImB_34
  have b35 := PImB_35
  have b36 := PImB_36
  have b37 := PImB_37
  have b38 := PImB_38
  have b39 := PImB_39
  have b40 := PImB_40
  have t1 := PImT_1
  have t2 := PImT_2
  have t3 := PImT_3
  have t4 := PImT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b29.1, b29.2, b30.1, b30.2, b31.1, b31.2, b32.1, b32.2, b33.1, b33.2, b34.1, b34.2, b35.1, b35.2, b36.1, b36.2, b37.1, b37.2, b38.1, b38.2, b39.1, b39.2, b40.1, b40.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- Upper end of the enclosure of `Im fEM(c)`. -/
theorem PImG_le : PImG cZ 41 12 ≤ (3472211171 / 1000000000000000 : ℝ) := by
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
  have b28 := PImB_28
  have b29 := PImB_29
  have b30 := PImB_30
  have b31 := PImB_31
  have b32 := PImB_32
  have b33 := PImB_33
  have b34 := PImB_34
  have b35 := PImB_35
  have b36 := PImB_36
  have b37 := PImB_37
  have b38 := PImB_38
  have b39 := PImB_39
  have b40 := PImB_40
  have t1 := PImT_1
  have t2 := PImT_2
  have t3 := PImT_3
  have t4 := PImT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b29.1, b29.2, b30.1, b30.2, b31.1, b31.2, b32.1, b32.2, b33.1, b33.2, b34.1, b34.2, b35.1, b35.2, b36.1, b36.2, b37.1, b37.2, b38.1, b38.2, b39.1, b39.2, b40.1, b40.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- **The enclosure of `Im fEM(c)`**: `PImG cZ 41 12 ∈ [1.4500706410e-06, 3.4722111710e-06]` (width `2.02e-06`). -/
theorem PImG_mem : (1450070641 / 1000000000000000 : ℝ) ≤ PImG cZ 41 12 ∧ PImG cZ 41 12 ≤ (3472211171 / 1000000000000000 : ℝ) := ⟨PImG_ge, PImG_le⟩

/-- Open inequality `H2` of `DHLocate3Base`. -/
theorem H2 : |PImG cZ 41 12| ≤ (9 / 100000 : ℝ) := by
  have h := PImG_mem
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

set_option maxHeartbeats 1000000 in
/-- Lower end of the enclosure of `Re fEM′(c)`. -/
theorem AReG_ge : (617876150980419 / 1000000000000000 : ℝ) ≤ AReG cZ 41 12 := by
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
  have b28 := AReB_28
  have b29 := AReB_29
  have b30 := AReB_30
  have b31 := AReB_31
  have b32 := AReB_32
  have b33 := AReB_33
  have b34 := AReB_34
  have b35 := AReB_35
  have b36 := AReB_36
  have b37 := AReB_37
  have b38 := AReB_38
  have b39 := AReB_39
  have b40 := AReB_40
  have t1 := AReT_1
  have t2 := AReT_2
  have t3 := AReT_3
  have t4 := AReT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b29.1, b29.2, b30.1, b30.2, b31.1, b31.2, b32.1, b32.2, b33.1, b33.2, b34.1, b34.2, b35.1, b35.2, b36.1, b36.2, b37.1, b37.2, b38.1, b38.2, b39.1, b39.2, b40.1, b40.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

set_option maxHeartbeats 1000000 in
/-- Upper end of the enclosure of `Re fEM′(c)`. -/
theorem AReG_le : AReG cZ 41 12 ≤ (12357701256783 / 20000000000000 : ℝ) := by
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
  have b28 := AReB_28
  have b29 := AReB_29
  have b30 := AReB_30
  have b31 := AReB_31
  have b32 := AReB_32
  have b33 := AReB_33
  have b34 := AReB_34
  have b35 := AReB_35
  have b36 := AReB_36
  have b37 := AReB_37
  have b38 := AReB_38
  have b39 := AReB_39
  have b40 := AReB_40
  have t1 := AReT_1
  have t2 := AReT_2
  have t3 := AReT_3
  have t4 := AReT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b29.1, b29.2, b30.1, b30.2, b31.1, b31.2, b32.1, b32.2, b33.1, b33.2, b34.1, b34.2, b35.1, b35.2, b36.1, b36.2, b37.1, b37.2, b38.1, b38.2, b39.1, b39.2, b40.1, b40.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- **The enclosure of `Re fEM′(c)`**: `AReG cZ 41 12 ∈ [6.1787615098e-01, 6.1788506284e-01]` (width `8.91e-06`). -/
theorem AReG_mem : (617876150980419 / 1000000000000000 : ℝ) ≤ AReG cZ 41 12 ∧ AReG cZ 41 12 ≤ (12357701256783 / 20000000000000 : ℝ) := ⟨AReG_ge, AReG_le⟩

/-- Open inequality `H3` of `DHLocate3Base`. -/
theorem H3 : (3 / 5 : ℝ) ≤ AReG cZ 41 12 := by
  have h := AReG_mem
  linarith [h.1]

/-- **The located zero**: within `1 / 500` of `cZ = 57436 / 100000 + (16647931 / 100000) i` (`dh_zero_near_of_center'` with
its three open inequalities discharged). -/
theorem dh_zero_located : ∃ ρ, dh ρ = 0 ∧ ‖ρ - cZ‖ < (1 / 500 : ℝ) :=
  dh_zero_near_of_center' H1 H2 H3

/-- The located zero in coordinates: `0.57236 < Re ρ < 0.57636` (off the critical line)
and `166.47731 < Im ρ < 166.48131`. -/
theorem dh_zero_located_box : ∃ ρ : ℂ, dh ρ = 0 ∧ 14309 / 25000 < ρ.re ∧ ρ.re < 14409 / 25000 ∧
    16647731 / 100000 < ρ.im ∧ ρ.im < 16648131 / 100000 := by
  obtain ⟨ρ, h0, hρ⟩ := dh_zero_located
  have hre := abs_lt.1 ((Complex.abs_re_le_norm (ρ - cZ)).trans_lt hρ)
  have him := abs_lt.1 ((Complex.abs_im_le_norm (ρ - cZ)).trans_lt hρ)
  rw [Complex.sub_re, cZ_re] at hre
  rw [Complex.sub_im, cZ_im] at him
  exact ⟨ρ, h0, by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩

end PsiOmega.Locate.Z3

namespace PsiOmega.Locate

/-- **Zero 3** (`ρ ≈ 0.57435605045080599 + 166.47930591316816 i`): a kernel-checked zero of `dh` within `1 / 500` of
`57436 / 100000 + (16647931 / 100000) i`. -/
theorem dh_zero_located_3 : ∃ ρ, dh ρ = 0 ∧ ‖ρ - Z3.cZ‖ < (1 / 500 : ℝ) := Z3.dh_zero_located

/-- **Zero 3** in coordinates. -/
theorem dh_zero_located_box_3 : ∃ ρ : ℂ, dh ρ = 0 ∧ 14309 / 25000 < ρ.re ∧ ρ.re < 14409 / 25000 ∧
    16647731 / 100000 < ρ.im ∧ ρ.im < 16648131 / 100000 := Z3.dh_zero_located_box

end PsiOmega.Locate

#print axioms PsiOmega.Locate.Z3.PReG_mem
#print axioms PsiOmega.Locate.Z3.PImG_mem
#print axioms PsiOmega.Locate.Z3.AReG_mem
#print axioms PsiOmega.Locate.Z3.H1
#print axioms PsiOmega.Locate.Z3.H2
#print axioms PsiOmega.Locate.Z3.H3
#print axioms PsiOmega.Locate.Z3.dh_zero_located
#print axioms PsiOmega.Locate.Z3.dh_zero_located_box
#print axioms PsiOmega.Locate.dh_zero_located_3
#print axioms PsiOmega.Locate.dh_zero_located_box_3
