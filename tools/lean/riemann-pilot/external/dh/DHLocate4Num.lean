import DHLocate4Trig2

/-! # Generated (`gen_locate_zero.py 4`): the interval evaluation of `PReG cZ 41 12`, `PImG cZ 41 12`, `AReG cZ 41 12`

The three open inequalities of `DHLocate4Base` (`H1`, `H2`, `H3`) from the atom bounds of `DHLocate4Exp` /
`DHLocate4Trig`, `DHLocate4Trig2`, `κ` (`PsiOmega.kappa_bounds`) and `log n` (`PsiOmega.Num.log_bound_n`), by interval products
(`mul_bounds_of`) and block sums; then `dh_zero_located` = `dh_zero_near_of_center' H1 H2 H3`. -/

open Real Finset

namespace PsiOmega.Locate.Z4

theorem lgB_2 : (346573590228867 / 500000000000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (138629436131547 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_2
  constructor <;> linarith [h.1, h.2]

theorem eC_2 : (-302395628521589 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 2 * cCG cZ 2 ∧ ex (72426 / 100000) 2 * cCG cZ 2 ≤ (-604791235096273 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_2 cCB_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_2 : (-42952130505967 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 2 * cCG cZ 2) ∧ kappa * (ex (72426 / 100000) 2 * cCG cZ 2) ≤ (-171808515789211 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_2 : (24993013519601 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 2 * sCG cZ 2 ∧ ex (72426 / 100000) 2 * sCG cZ 2 ≤ (624825884563 / 25000000000000 : ℝ) := by
  exact mul_bounds_of exB_2 sCB_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_2 : (3549995691669 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 2 * sCG cZ 2) ∧ kappa * (ex (72426 / 100000) 2 * sCG cZ 2) ≤ (887499699267 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_2 : (-419209354705927 / 1000000000000000 : ℝ) ≤ Real.log 2 * (ex (72426 / 100000) 2 * cCG cZ 2) ∧ Real.log 2 * (ex (72426 / 100000) 2 * cCG cZ 2) ≤ (-104802334843133 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_2 eC_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_2 : (-119088592653817 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 2 * (ex (72426 / 100000) 2 * cCG cZ 2)) ∧ kappa * (Real.log 2 * (ex (72426 / 100000) 2 * cCG cZ 2)) ≤ (-119088588297919 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_3 : (1098612288561369 / 1000000000000000 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (1098612288829637 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_3
  constructor <;> linarith [h.1, h.2]

theorem eC_3 : (358909978269419 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 3 * cCG cZ 3 ∧ ex (72426 / 100000) 3 * cCG cZ 3 ≤ (179454999939753 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_3 cCB_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_3 : (101958803451559 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 3 * cCG cZ 3) ∧ kappa * (ex (72426 / 100000) 3 * cCG cZ 3) ≤ (101958809590533 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_3 : (-136776922156069 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 3 * sCG cZ 3 ∧ ex (72426 / 100000) 3 * sCG cZ 3 ≤ (-54710764544769 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_3 sCB_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_3 : (-38855457265531 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 3 * sCG cZ 3) ∧ kappa * (ex (72426 / 100000) 3 * sCG cZ 3) ≤ (-77710908398279 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_3 : (394302912614077 / 1000000000000000 : ℝ) ≤ Real.log 3 * (ex (72426 / 100000) 3 * cCG cZ 3) ∧ Real.log 3 * (ex (72426 / 100000) 3 * cCG cZ 3) ≤ (394302936451469 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_3 eC_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_3 : (7000824649931 / 62500000000000 : ℝ) ≤ kappa * (Real.log 3 * (ex (72426 / 100000) 3 * cCG cZ 3)) ∧ kappa * (Real.log 3 * (ex (72426 / 100000) 3 * cCG cZ 3)) ≤ (112013201170601 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_4 : (693147180505767 / 500000000000000 : ℝ) ≤ Real.log 4 ∧ Real.log 4 ≤ (693147180650437 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_4
  constructor <;> linarith [h.1, h.2]

theorem eC_4 : (365147790661347 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 4 * cCG cZ 4 ∧ ex (72426 / 100000) 4 * cCG cZ 4 ≤ (365147809782601 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_4 cCB_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_4 : (-7557783033843 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 4 * sCG cZ 4 ∧ ex (72426 / 100000) 4 * sCG cZ 4 ≤ (-30231113084303 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_4 sCB_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_4 : (101240464625929 / 200000000000000 : ℝ) ≤ Real.log 4 * (ex (72426 / 100000) 4 * cCG cZ 4) ∧ Real.log 4 * (ex (72426 / 100000) 4 * cCG cZ 4) ≤ (63275293717873 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_4 eC_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_6 : (1791759469113201 / 1000000000000000 : ℝ) ≤ Real.log 6 ∧ Real.log 6 ≤ (1791759469474139 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_6
  constructor <;> linarith [h.1, h.2]

theorem eC_6 : (-210228691846849 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 6 * cCG cZ 6 ∧ ex (72426 / 100000) 6 * cCG cZ 6 ≤ (-4204573486357 / 20000000000000 : ℝ) := by
  exact mul_bounds_of exB_6 cCB_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_6 : (174413199739891 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 6 * sCG cZ 6 ∧ ex (72426 / 100000) 6 * sCG cZ 6 ≤ (34882643450591 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_6 sCB_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_6 : (-376679249371753 / 1000000000000000 : ℝ) ≤ Real.log 6 * (ex (72426 / 100000) 6 * cCG cZ 6) ∧ Real.log 6 * (ex (72426 / 100000) 6 * cCG cZ 6) ≤ (-188339608944061 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_6 eC_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_7 : (972955074470179 / 500000000000000 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ (972955074651209 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_7
  constructor <;> linarith [h.1, h.2]

theorem eC_7 : (-38267081168059 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 7 * cCG cZ 7 ∧ ex (72426 / 100000) 7 * cCG cZ 7 ≤ (-38267065349307 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_7 cCB_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_7 : (-5435437914393 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 7 * cCG cZ 7) ∧ kappa * (ex (72426 / 100000) 7 * cCG cZ 7) ≤ (-10870871335009 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_7 : (-241287642389343 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 7 * sCG cZ 7 ∧ ex (72426 / 100000) 7 * sCG cZ 7 ≤ (-30160953314669 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_7 sCB_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_7 : (-68544762740473 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 7 * sCG cZ 7) ∧ kappa * (ex (72426 / 100000) 7 * sCG cZ 7) ≤ (-68544758231571 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_7 : (-37232150814553 / 500000000000000 : ℝ) ≤ Real.log 7 * (ex (72426 / 100000) 7 * cCG cZ 7) ∧ Real.log 7 * (ex (72426 / 100000) 7 * cCG cZ 7) ≤ (-3723213541669 / 50000000000000 : ℝ) := by
  exact mul_bounds_of lgB_7 eC_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_7 : (-21153747607041 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 7 * (ex (72426 / 100000) 7 * cCG cZ 7)) ∧ kappa * (Real.log 7 * (ex (72426 / 100000) 7 * cCG cZ 7)) ≤ (-1057686942931 / 50000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_8 : (2079441541559079 / 1000000000000000 : ℝ) ≤ Real.log 8 ∧ Real.log 8 ≤ (519860385493349 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_8
  constructor <;> linarith [h.1, h.2]

theorem eC_8 : (-27510329295179 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 8 * cCG cZ 8 ∧ ex (72426 / 100000) 8 * cCG cZ 8 ≤ (-220082617933861 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_8 cCB_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_8 : (-2500834573411 / 40000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 8 * cCG cZ 8) ∧ kappa * (ex (72426 / 100000) 8 * cCG cZ 8) ≤ (-12504171933709 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_8 : (2740965604583 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 8 * sCG cZ 8 ∧ ex (72426 / 100000) 8 * sCG cZ 8 ≤ (856552262987 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_8 sCB_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_8 : (7786508881493 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 8 * sCG cZ 8) ∧ kappa * (ex (72426 / 100000) 8 * sCG cZ 8) ≤ (7786513531799 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_8 : (-57206121569763 / 125000000000000 : ℝ) ≤ Real.log 8 * (ex (72426 / 100000) 8 * cCG cZ 8) ∧ Real.log 8 * (ex (72426 / 100000) 8 * cCG cZ 8) ≤ (-91529787661349 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_8 eC_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_8 : (-65004241269427 / 500000000000000 : ℝ) ≤ kappa * (Real.log 8 * (ex (72426 / 100000) 8 * cCG cZ 8)) ∧ kappa * (Real.log 8 * (ex (72426 / 100000) 8 * cCG cZ 8)) ≤ (-130008472808759 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_9 : (2197224577213583 / 1000000000000000 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ (274653072205603 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_9
  constructor <;> linarith [h.1, h.2]

theorem eC_9 : (53984674044443 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 9 * cCG cZ 9 ∧ ex (72426 / 100000) 9 * cCG cZ 9 ≤ (10796937927209 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_9 cCB_9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_9 : (-196362414223669 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 9 * sCG cZ 9 ∧ ex (72426 / 100000) 9 * sCG cZ 9 ≤ (-98181199293799 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_9 sCB_9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_9 : (59308226301657 / 500000000000000 : ℝ) ≤ Real.log 9 * (ex (72426 / 100000) 9 * cCG cZ 9) ∧ Real.log 9 * (ex (72426 / 100000) 9 * cCG cZ 9) ≤ (59308243442423 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_9 eC_9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_11 : (2397895272674763 / 1000000000000000 : ℝ) ≤ Real.log 11 ∧ Real.log 11 ≤ (2397895273114743 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_11
  constructor <;> linarith [h.1, h.2]

theorem eC_11 : (-32425953882509 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 11 * cCG cZ 11 ∧ ex (72426 / 100000) 11 * cCG cZ 11 ≤ (-81064877790537 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_11 cCB_11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_11 : (68741359460753 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 11 * sCG cZ 11 ∧ ex (72426 / 100000) 11 * sCG cZ 11 ≤ (34370686631229 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_11 sCB_11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_11 : (-15550808308221 / 40000000000000 : ℝ) ≤ Real.log 11 * (ex (72426 / 100000) 11 * cCG cZ 11) ∧ Real.log 11 * (ex (72426 / 100000) 11 * cCG cZ 11) ≤ (-97192543616943 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_11 eC_11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_12 : (248490664966427 / 100000000000000 : ℝ) ≤ Real.log 12 ∧ Real.log 12 ≤ (1242453325052681 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_12
  constructor <;> linarith [h.1, h.2]

theorem eC_12 : (122785347625699 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 12 * cCG cZ 12 ∧ ex (72426 / 100000) 12 * cCG cZ 12 ≤ (61392680352199 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_12 cCB_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_12 : (34880744151121 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 12 * cCG cZ 12) ∧ kappa * (ex (72426 / 100000) 12 * cCG cZ 12) ≤ (17440373933253 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_12 : (-110737838230969 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 12 * sCG cZ 12 ∧ ex (72426 / 100000) 12 * sCG cZ 12 ≤ (-3460557036377 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_12 sCB_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_12 : (-31458299201609 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 12 * sCG cZ 12) ∧ kappa * (ex (72426 / 100000) 12 * sCG cZ 12) ≤ (-15729147744787 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_12 : (152555063398219 / 500000000000000 : ℝ) ≤ Real.log 12 * (ex (72426 / 100000) 12 * cCG cZ 12) ∧ Real.log 12 * (ex (72426 / 100000) 12 * cCG cZ 12) ≤ (61022031869989 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_12 eC_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_12 : (43337696543179 / 500000000000000 : ℝ) ≤ kappa * (Real.log 12 * (ex (72426 / 100000) 12 * cCG cZ 12)) ∧ kappa * (Real.log 12 * (ex (72426 / 100000) 12 * cCG cZ 12)) ≤ (86675402334129 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_13 : (641237339334437 / 250000000000000 : ℝ) ≤ Real.log 13 ∧ Real.log 13 ≤ (512989871555873 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_13
  constructor <;> linarith [h.1, h.2]

theorem eC_13 : (103736436221413 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 13 * cCG cZ 13 ∧ ex (72426 / 100000) 13 * cCG cZ 13 ≤ (51868224260939 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_13 cCB_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_13 : (2946934761319 / 100000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 13 * cCG cZ 13) ∧ kappa * (ex (72426 / 100000) 13 * cCG cZ 13) ≤ (3683668888437 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_13 : (5827719557973 / 50000000000000 : ℝ) ≤ ex (72426 / 100000) 13 * sCG cZ 13 ∧ ex (72426 / 100000) 13 * sCG cZ 13 ≤ (58277201735379 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_13 sCB_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_13 : (1655532999799 / 50000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 13 * sCG cZ 13) ∧ kappa * (ex (72426 / 100000) 13 * sCG cZ 13) ≤ (33110663493363 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_13 : (266078705418621 / 1000000000000000 : ℝ) ≤ Real.log 13 * (ex (72426 / 100000) 13 * cCG cZ 13) ∧ Real.log 13 * (ex (72426 / 100000) 13 * cCG cZ 13) ≤ (33259842126813 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_13 eC_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_13 : (4724211513851 / 62500000000000 : ℝ) ≤ kappa * (Real.log 13 * (ex (72426 / 100000) 13 * cCG cZ 13)) ∧ kappa * (Real.log 13 * (ex (72426 / 100000) 13 * cCG cZ 13)) ≤ (37793696598673 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_14 : (32988216618643 / 12500000000000 : ℝ) ≤ Real.log 14 ∧ Real.log 14 ≤ (65976433248333 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_14
  constructor <;> linarith [h.1, h.2]

theorem eC_14 : (291740921453 / 10000000000000 : ℝ) ≤ ex (72426 / 100000) 14 * cCG cZ 14 ∧ ex (72426 / 100000) 14 * cCG cZ 14 ≤ (14587051868977 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_14 cCB_14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_14 : (18121529191519 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 14 * sCG cZ 14 ∧ ex (72426 / 100000) 14 * sCG cZ 14 ≤ (144972245161867 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_14 sCB_14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_14 : (4812006356707 / 62500000000000 : ℝ) ≤ Real.log 14 * (ex (72426 / 100000) 14 * cCG cZ 14) ∧ Real.log 14 * (ex (72426 / 100000) 14 * cCG cZ 14) ≤ (76992132313883 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_14 eC_14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_16 : (1386294361052777 / 500000000000000 : ℝ) ≤ Real.log 16 ∧ Real.log 16 ≤ (1386294361310171 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_16
  constructor <;> linarith [h.1, h.2]

theorem eC_16 : (33104747322221 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 16 * cCG cZ 16 ∧ ex (72426 / 100000) 16 * cCG cZ 16 ≤ (26483800321673 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_16 cCB_16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_16 : (-11038830326309 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 16 * sCG cZ 16 ∧ ex (72426 / 100000) 16 * sCG cZ 16 ≤ (-11038824187139 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_16 sCB_16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_16 : (14685735851799 / 40000000000000 : ℝ) ≤ Real.log 16 * (ex (72426 / 100000) 16 * cCG cZ 16) ∧ Real.log 16 * (ex (72426 / 100000) 16 * cCG cZ 16) ≤ (183571715259999 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_16 eC_16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_17 : (2833213343915281 / 1000000000000000 : ℝ) ≤ Real.log 17 ∧ Real.log 17 ≤ (2833213344477039 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_17
  constructor <;> linarith [h.1, h.2]

theorem eC_17 : (-27841503395437 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 17 * cCG cZ 17 ∧ ex (72426 / 100000) 17 * cCG cZ 17 ≤ (-27841496970929 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_17 cCB_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_17 : (-15818375327311 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 17 * cCG cZ 17) ∧ kappa * (ex (72426 / 100000) 17 * cCG cZ 17) ≤ (-7909185838587 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_17 : (-115786355437317 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 17 * sCG cZ 17 ∧ ex (72426 / 100000) 17 * sCG cZ 17 ≤ (-115786342563829 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_17 sCB_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_17 : (-10278899107 / 312500000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 17 * sCG cZ 17) ∧ kappa * (ex (72426 / 100000) 17 * sCG cZ 17) ≤ (-3289247348531 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_17 : (-15776183790051 / 100000000000000 : ℝ) ≤ Real.log 17 * (ex (72426 / 100000) 17 * cCG cZ 17) ∧ Real.log 17 * (ex (72426 / 100000) 17 * cCG cZ 17) ≤ (-6310472058609 / 40000000000000 : ℝ) := by
  exact mul_bounds_of lgB_17 eC_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_17 : (-11204208016321 / 250000000000000 : ℝ) ≤ kappa * (Real.log 17 * (ex (72426 / 100000) 17 * cCG cZ 17)) ∧ kappa * (Real.log 17 * (ex (72426 / 100000) 17 * cCG cZ 17)) ≤ (-22408410857391 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_18 : (1445185878875393 / 500000000000000 : ℝ) ≤ Real.log 18 ∧ Real.log 18 ≤ (578074351668731 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_18
  constructor <;> linarith [h.1, h.2]

theorem eC_18 : (-13870890126361 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 18 * cCG cZ 18 ∧ ex (72426 / 100000) 18 * cCG cZ 18 ≤ (-27741767295553 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_18 cCB_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_18 : (-63046867269 / 8000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 18 * cCG cZ 18) ∧ kappa * (ex (72426 / 100000) 18 * cCG cZ 18) ≤ (-7880854727763 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_18 : (120107498143451 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 18 * sCG cZ 18 ∧ ex (72426 / 100000) 18 * sCG cZ 18 ≤ (60053755570141 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_18 sCB_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_18 : (6824004646131 / 200000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 18 * sCG cZ 18) ∧ kappa * (ex (72426 / 100000) 18 * sCG cZ 18) ≤ (1066250841337 / 31250000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_18 : (-20046014542161 / 250000000000000 : ℝ) ≤ Real.log 18 * (ex (72426 / 100000) 18 * cCG cZ 18) ∧ Real.log 18 * (ex (72426 / 100000) 18 * cCG cZ 18) ≤ (-2004600517529 / 25000000000000 : ℝ) := by
  exact mul_bounds_of lgB_18 eC_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_18 : (-22778610575793 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 18 * (ex (72426 / 100000) 18 * cCG cZ 18)) ∧ kappa * (Real.log 18 * (ex (72426 / 100000) 18 * cCG cZ 18)) ≤ (-4555719986413 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_19 : (58888779580361 / 20000000000000 : ℝ) ≤ Real.log 19 ∧ Real.log 19 ≤ (1472219489816001 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_19
  constructor <;> linarith [h.1, h.2]

theorem eC_19 : (10329008308449 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 19 * cCG cZ 19 ∧ ex (72426 / 100000) 19 * cCG cZ 19 ≤ (41316046227793 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_19 cCB_19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_19 : (-111102416245067 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 19 * sCG cZ 19 ∧ ex (72426 / 100000) 19 * sCG cZ 19 ≤ (-55551201610019 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_19 sCB_19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_19 : (60826269355997 / 500000000000000 : ℝ) ≤ Real.log 19 * (ex (72426 / 100000) 19 * cCG cZ 19) ∧ Real.log 19 * (ex (72426 / 100000) 19 * cCG cZ 19) ≤ (7603286062337 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_19 eC_19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_21 : (1522261218785741 / 500000000000000 : ℝ) ≤ Real.log 21 ∧ Real.log 21 ≤ (3044522438210293 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_21
  constructor <;> linarith [h.1, h.2]

theorem eC_21 : (-19934899374739 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 21 * cCG cZ 21 ∧ ex (72426 / 100000) 21 * cCG cZ 21 ≤ (-7973958493407 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_21 cCB_21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_21 : (-76132444984751 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 21 * sCG cZ 21 ∧ ex (72426 / 100000) 21 * sCG cZ 21 ≤ (-4758277026867 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_21 sCB_21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_21 : (-242768993799429 / 1000000000000000 : ℝ) ≤ Real.log 21 * (ex (72426 / 100000) 21 * cCG cZ 21) ∧ Real.log 21 * (ex (72426 / 100000) 21 * cCG cZ 21) ≤ (-242768955494413 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_21 eC_21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_22 : (3091042453205323 / 1000000000000000 : ℝ) ≤ Real.log 22 ∧ Real.log 22 ≤ (386380306731437 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_22
  constructor <;> linarith [h.1, h.2]

theorem eC_22 : (12042075110613 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 22 * cCG cZ 22 ∧ ex (72426 / 100000) 22 * cCG cZ 22 ≤ (96336613161093 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_22 cCB_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_22 : (13683604733109 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 22 * cCG cZ 22) ∧ kappa * (ex (72426 / 100000) 22 * cCG cZ 22) ≤ (6841803238407 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_22 : (-9125258921607 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 22 * sCG cZ 22 ∧ ex (72426 / 100000) 22 * sCG cZ 22 ≤ (-45626282355591 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_22 sCB_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_22 : (-1620184268279 / 125000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 22 * sCG cZ 22) ∧ kappa * (ex (72426 / 100000) 22 * sCG cZ 22) ≤ (-405045958299 / 31250000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_22 : (59556104626547 / 200000000000000 : ℝ) ≤ Real.log 22 * (ex (72426 / 100000) 22 * cCG cZ 22) ∧ Real.log 22 * (ex (72426 / 100000) 22 * cCG cZ 22) ≤ (37222570142651 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_22 eC_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_22 : (16918641257169 / 200000000000000 : ℝ) ≤ kappa * (Real.log 22 * (ex (72426 / 100000) 22 * cCG cZ 22)) ∧ kappa * (Real.log 22 * (ex (72426 / 100000) 22 * cCG cZ 22)) ≤ (84593217083257 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_23 : (97984194242981 / 31250000000000 : ℝ) ≤ Real.log 23 ∧ Real.log 23 ≤ (78387355410673 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_23
  constructor <;> linarith [h.1, h.2]

theorem eC_23 : (8822078096647 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 23 * cCG cZ 23 ∧ ex (72426 / 100000) 23 * cCG cZ 23 ≤ (44110402438231 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_23 cCB_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_23 : (391588673497 / 31250000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 23 * cCG cZ 23) ∧ kappa * (ex (72426 / 100000) 23 * cCG cZ 23) ≤ (12530840948069 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_23 : (18663553391609 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 23 * sCG cZ 23 ∧ ex (72426 / 100000) 23 * sCG cZ 23 ≤ (3732711157451 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_23 sCB_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_23 : (26509622010763 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 23 * sCG cZ 23) ∧ kappa * (ex (72426 / 100000) 23 * sCG cZ 23) ≤ (26509625413529 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_23 : (138307874215777 / 1000000000000000 : ℝ) ≤ Real.log 23 * (ex (72426 / 100000) 23 * cCG cZ 23) ∧ Real.log 23 * (ex (72426 / 100000) 23 * cCG cZ 23) ≤ (69153955864669 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_23 eC_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_23 : (39290368662817 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 23 * (ex (72426 / 100000) 23 * cCG cZ 23)) ∧ kappa * (Real.log 23 * (ex (72426 / 100000) 23 * cCG cZ 23)) ≤ (7858075863927 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_24 : (397256728774203 / 125000000000000 : ℝ) ≤ Real.log 24 ∧ Real.log 24 ≤ (3178053830849101 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_24
  constructor <;> linarith [h.1, h.2]

theorem eC_24 : (-71491840804001 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 24 * cCG cZ 24 ∧ ex (72426 / 100000) 24 * cCG cZ 24 ≤ (-35745914581467 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_24 cCB_24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_24 : (35021020878893 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 24 * sCG cZ 24 ∧ ex (72426 / 100000) 24 * sCG cZ 24 ≤ (35021026694459 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_24 sCB_24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_24 : (-22720491854161 / 100000000000000 : ℝ) ≤ Real.log 24 * (ex (72426 / 100000) 24 * cCG cZ 24) ∧ Real.log 24 * (ex (72426 / 100000) 24 * cCG cZ 24) ≤ (-22720488149881 / 100000000000000 : ℝ) := by
  exact mul_bounds_of lgB_24 eC_24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_26 : (162904826893321 / 50000000000000 : ℝ) ≤ Real.log 26 ∧ Real.log 26 ≤ (1629048269263539 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_26
  constructor <;> linarith [h.1, h.2]

theorem eC_26 : (-128226452603 / 1953125000000 : ℝ) ≤ ex (72426 / 100000) 26 * cCG cZ 26 ∧ ex (72426 / 100000) 26 * cCG cZ 26 ≤ (-16412983162977 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_26 cCB_26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_26 : (-67898398204491 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 26 * sCG cZ 26 ∧ ex (72426 / 100000) 26 * sCG cZ 26 ≤ (-33949193557353 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_26 sCB_26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_26 : (-106950185311601 / 500000000000000 : ℝ) ≤ Real.log 26 * (ex (72426 / 100000) 26 * cCG cZ 26) ∧ Real.log 26 * (ex (72426 / 100000) 26 * cCG cZ 26) ≤ (-10695016723871 / 50000000000000 : ℝ) := by
  exact mul_bounds_of lgB_26 eC_26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_27 : (51497451028891 / 15625000000000 : ℝ) ≤ Real.log 27 ∧ Real.log 27 ≤ (411979608313923 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_27
  constructor <;> linarith [h.1, h.2]

theorem eC_27 : (-34340052009947 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 27 * cCG cZ 27 ∧ ex (72426 / 100000) 27 * cCG cZ 27 ≤ (-6868008241077 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_27 cCB_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_27 : (-152426392819 / 15625000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 27 * cCG cZ 27) ∧ kappa * (ex (72426 / 100000) 27 * cCG cZ 27) ≤ (-4877643035533 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_27 : (-85244151561337 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 27 * sCG cZ 27 ∧ ex (72426 / 100000) 27 * sCG cZ 27 ≤ (-1331939698943 / 15625000000000 : ℝ) := by
  exact mul_bounds_of exB_27 sCB_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_27 : (-6054019267133 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 27 * sCG cZ 27) ∧ kappa * (ex (72426 / 100000) 27 * sCG cZ 27) ≤ (-6054018498061 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_27 : (-56589604706151 / 500000000000000 : ℝ) ≤ Real.log 27 * (ex (72426 / 100000) 27 * cCG cZ 27) ∧ Real.log 27 * (ex (72426 / 100000) 27 * cCG cZ 27) ≤ (-56589586889741 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_27 eC_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_27 : (-32151841592461 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 27 * (ex (72426 / 100000) 27 * cCG cZ 27)) ∧ kappa * (Real.log 27 * (ex (72426 / 100000) 27 * cCG cZ 27)) ≤ (-32151831469923 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_28 : (3332204510019711 / 1000000000000000 : ℝ) ≤ Real.log 28 ∧ Real.log 28 ≤ (1666102255341693 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_28
  constructor <;> linarith [h.1, h.2]

theorem eC_28 : (-132922111353 / 6250000000000 : ℝ) ≤ ex (72426 / 100000) 28 * cCG cZ 28 ∧ ex (72426 / 100000) 28 * cCG cZ 28 ≤ (-664610227689 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_28 cCB_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_28 : (-3020830903873 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 28 * cCG cZ 28) ∧ kappa * (ex (72426 / 100000) 28 * cCG cZ 28) ≤ (-604165881627 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_28 : (-86948797910623 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 28 * sCG cZ 28 ∧ ex (72426 / 100000) 28 * sCG cZ 28 ≤ (-86948787348617 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_28 sCB_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_28 : (-6175082843381 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 28 * sCG cZ 28) ∧ kappa * (ex (72426 / 100000) 28 * sCG cZ 28) ≤ (-12350164186539 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_28 : (-14173557088641 / 200000000000000 : ℝ) ≤ Real.log 28 * (ex (72426 / 100000) 28 * cCG cZ 28) ∧ Real.log 28 * (ex (72426 / 100000) 28 * cCG cZ 28) ≤ (-4429234396221 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_28 eC_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_28 : (-10066026363897 / 500000000000000 : ℝ) ≤ kappa * (Real.log 28 * (ex (72426 / 100000) 28 * cCG cZ 28)) ∧ kappa * (Real.log 28 * (ex (72426 / 100000) 28 * cCG cZ 28)) ≤ (-2516505344447 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_29 : (673459165966167 / 200000000000000 : ℝ) ≤ Real.log 29 ∧ Real.log 29 ≤ (3367295830495533 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_29
  constructor <;> linarith [h.1, h.2]

theorem eC_29 : (-2764555984263 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 29 * cCG cZ 29 ∧ ex (72426 / 100000) 29 * cCG cZ 29 ≤ (-3455693690671 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_29 cCB_29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_29 : (-82770938659829 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 29 * sCG cZ 29 ∧ ex (72426 / 100000) 29 * sCG cZ 29 ≤ (-41385464158013 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_29 sCB_29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_29 : (-93090778389803 / 1000000000000000 : ℝ) ≤ Real.log 29 * (ex (72426 / 100000) 29 * cCG cZ 29) ∧ Real.log 29 * (ex (72426 / 100000) 29 * cCG cZ 29) ≤ (-93090743630153 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_29 eC_29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_31 : (3433987204329301 / 1000000000000000 : ℝ) ≤ Real.log 31 ∧ Real.log 31 ≤ (42924840062443 / 12500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_31
  constructor <;> linarith [h.1, h.2]

theorem eC_31 : (-74262050931739 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 31 * cCG cZ 31 ∧ ex (72426 / 100000) 31 * cCG cZ 31 ≤ (-37131020515457 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_31 cCB_31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_31 : (-37405918902787 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 31 * sCG cZ 31 ∧ ex (72426 / 100000) 31 * sCG cZ 31 ≤ (-37405909019763 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_31 sCB_31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_31 : (-31876866589539 / 125000000000000 : ℝ) ≤ Real.log 31 * (ex (72426 / 100000) 31 * cCG cZ 31) ∧ Real.log 31 * (ex (72426 / 100000) 31 * cCG cZ 31) ≤ (-15938431166721 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_31 eC_31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_32 : (3465735902643809 / 1000000000000000 : ℝ) ≤ Real.log 32 ∧ Real.log 32 ≤ (433216987913807 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_32
  constructor <;> linarith [h.1, h.2]

theorem eC_32 : (-79534066883811 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 32 * cCG cZ 32 ∧ ex (72426 / 100000) 32 * cCG cZ 32 ≤ (-79534057212793 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_32 cCB_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_32 : (-22593961673093 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 32 * cCG cZ 32) ∧ kappa * (ex (72426 / 100000) 32 * cCG cZ 32) ≤ (-11296979462879 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_32 : (166619178377 / 10000000000000 : ℝ) ≤ ex (72426 / 100000) 32 * sCG cZ 32 ∧ ex (72426 / 100000) 32 * sCG cZ 32 ≤ (8330963739179 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_32 sCB_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_32 : (4733301687881 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 32 * sCG cZ 32) ∧ kappa * (ex (72426 / 100000) 32 * sCG cZ 32) ≤ (4733304426591 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_32 : (-275644071135519 / 1000000000000000 : ℝ) ≤ Real.log 32 * (ex (72426 / 100000) 32 * cCG cZ 32) ∧ Real.log 32 * (ex (72426 / 100000) 32 * cCG cZ 32) ≤ (-275644037565303 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_32 eC_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_32 : (-39152352084229 / 500000000000000 : ℝ) ≤ kappa * (Real.log 32 * (ex (72426 / 100000) 32 * cCG cZ 32)) ∧ kappa * (Real.log 32 * (ex (72426 / 100000) 32 * cCG cZ 32)) ≤ (-78304694631861 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_33 : (699301512262101 / 200000000000000 : ℝ) ≤ Real.log 33 ∧ Real.log 33 ≤ (3496507561977559 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_33
  constructor <;> linarith [h.1, h.2]

theorem eC_33 : (-39385532416467 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 33 * cCG cZ 33 ∧ ex (72426 / 100000) 33 * cCG cZ 33 ≤ (-39385522983893 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_33 cCB_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_33 : (-87410971797 / 7812500000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 33 * cCG cZ 33) ∧ kappa * (ex (72426 / 100000) 33 * cCG cZ 33) ≤ (-5594300855209 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_33 : (69023175980251 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 33 * sCG cZ 33 ∧ ex (72426 / 100000) 33 * sCG cZ 33 ≤ (17255796356801 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_33 sCB_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_33 : (9804018917649 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 33 * sCG cZ 33) ∧ kappa * (ex (72426 / 100000) 33 * sCG cZ 33) ≤ (980402025949 / 50000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_33 : (-13771181192669 / 100000000000000 : ℝ) ≤ Real.log 33 * (ex (72426 / 100000) 33 * cCG cZ 33) ∧ Real.log 33 * (ex (72426 / 100000) 33 * cCG cZ 33) ≤ (-2754235578387 / 20000000000000 : ℝ) := by
  exact mul_bounds_of lgB_33 eC_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_33 : (-7824207971533 / 200000000000000 : ℝ) ≤ kappa * (Real.log 33 * (ex (72426 / 100000) 33 * cCG cZ 33)) ∧ kappa * (Real.log 33 * (ex (72426 / 100000) 33 * cCG cZ 33)) ≤ (-39121030480971 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_34 : (3526360524460139 / 1000000000000000 : ℝ) ≤ Real.log 34 ∧ Real.log 34 ≤ (3526360525127523 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_34
  constructor <;> linarith [h.1, h.2]

theorem eC_34 : (36570437190713 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 34 * cCG cZ 34 ∧ ex (72426 / 100000) 34 * cCG cZ 34 ≤ (18285223219921 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_34 cCB_34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_34 : (68634879285351 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 34 * sCG cZ 34 ∧ ex (72426 / 100000) 34 * sCG cZ 34 ≤ (68634888550011 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_34 sCB_34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_34 : (128960546071579 / 1000000000000000 : ℝ) ≤ Real.log 34 * (ex (72426 / 100000) 34 * cCG cZ 34) ∧ Real.log 34 * (ex (72426 / 100000) 34 * cCG cZ 34) ≤ (515842314847 / 4000000000000 : ℝ) := by
  exact mul_bounds_of lgB_34 eC_34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_36 : (3583518938300017 / 1000000000000000 : ℝ) ≤ Real.log 36 ∧ Real.log 36 ≤ (3583518938967891 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_36
  constructor <;> linarith [h.1, h.2]

theorem eC_36 : (86100800493 / 6250000000000 : ℝ) ≤ ex (72426 / 100000) 36 * cCG cZ 36 ∧ ex (72426 / 100000) 36 * cCG cZ 36 ≤ (215252139241 / 15625000000000 : ℝ) := by
  exact mul_bounds_of exB_36 cCB_36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_36 : (-73333322585189 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 36 * sCG cZ 36 ∧ ex (72426 / 100000) 36 * sCG cZ 36 ≤ (-73333313723831 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_36 sCB_36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_36 : (49367015867113 / 1000000000000000 : ℝ) ≤ Real.log 36 * (ex (72426 / 100000) 36 * cCG cZ 36) ∧ Real.log 36 * (ex (72426 / 100000) 36 * cCG cZ 36) ≤ (49367047527903 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_36 eC_36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_37 : (1805458956244053 / 500000000000000 : ℝ) ≤ Real.log 37 ∧ Real.log 37 ≤ (11284118478613 / 3125000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_37
  constructor <;> linarith [h.1, h.2]

theorem eC_37 : (-69555966466493 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 37 * cCG cZ 37 ∧ ex (72426 / 100000) 37 * cCG cZ 37 ≤ (-69555957796489 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_37 cCB_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_37 : (-9879696223599 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 37 * cCG cZ 37) ∧ kappa * (ex (72426 / 100000) 37 * cCG cZ 37) ≤ (-1975938998423 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_37 : (-22647032650297 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 37 * sCG cZ 37 ∧ ex (72426 / 100000) 37 * sCG cZ 37 ≤ (-22647024002993 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_37 sCB_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_37 : (-6433547381119 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 37 * sCG cZ 37) ∧ kappa * (ex (72426 / 100000) 37 * sCG cZ 37) ≤ (-6433544924601 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_37 : (-251160885280749 / 1000000000000000 : ℝ) ≤ Real.log 37 * (ex (72426 / 100000) 37 * cCG cZ 37) ∧ Real.log 37 * (ex (72426 / 100000) 37 * cCG cZ 37) ≤ (-31395106740951 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_37 eC_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_37 : (-71349544140667 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 37 * (ex (72426 / 100000) 37 * cCG cZ 37)) ∧ kappa * (Real.log 37 * (ex (72426 / 100000) 37 * cCG cZ 37)) ≤ (-8918691904237 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_38 : (1818793079785123 / 500000000000000 : ℝ) ≤ Real.log 38 ∧ Real.log 38 ≤ (72751723204769 / 20000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_38
  constructor <;> linarith [h.1, h.2]

theorem eC_38 : (-22210798358437 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 38 * cCG cZ 38 ∧ ex (72426 / 100000) 38 * cCG cZ 38 ≤ (-22210789867097 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_38 cCB_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_38 : (-6309622360597 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 38 * cCG cZ 38) ∧ kappa * (ex (72426 / 100000) 38 * cCG cZ 38) ≤ (-1261923989677 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_38 : (17056593322551 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 38 * sCG cZ 38 ∧ ex (72426 / 100000) 38 * sCG cZ 38 ≤ (68226381803819 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_38 sCB_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_38 : (969084144449 / 50000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 38 * sCG cZ 38) ∧ kappa * (ex (72426 / 100000) 38 * sCG cZ 38) ≤ (30283883293 / 1562500000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_38 : (-40396846358249 / 500000000000000 : ℝ) ≤ Real.log 38 * (ex (72426 / 100000) 38 * cCG cZ 38) ∧ Real.log 38 * (ex (72426 / 100000) 38 * cCG cZ 38) ≤ (-3231746472547 / 40000000000000 : ℝ) := by
  exact mul_bounds_of lgB_38 eC_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_38 : (-22951794975239 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 38 * (ex (72426 / 100000) 38 * cCG cZ 38)) ∧ kappa * (Real.log 38 * (ex (72426 / 100000) 38 * cCG cZ 38)) ≤ (-11475893098197 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_39 : (3663561645973489 / 1000000000000000 : ℝ) ≤ Real.log 39 ∧ Real.log 39 ≤ (3663561646641817 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_39
  constructor <;> linarith [h.1, h.2]

theorem eC_39 : (17278985815987 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 39 * cCG cZ 39 ∧ ex (72426 / 100000) 39 * cCG cZ 39 ≤ (34557975826529 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_39 cCB_39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_39 : (13455032505919 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 39 * sCG cZ 39 ∧ ex (72426 / 100000) 39 * sCG cZ 39 ≤ (168188010851 / 12500000000000 : ℝ) := by
  exact mul_bounds_of exB_39 sCB_39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_39 : (253210518867079 / 1000000000000000 : ℝ) ≤ Real.log 39 * (ex (72426 / 100000) 39 * cCG cZ 39) ∧ Real.log 39 * (ex (72426 / 100000) 39 * cCG cZ 39) ≤ (126605274823647 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_39 eC_39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_41 : (3713572066548123 / 1000000000000000 : ℝ) ≤ Real.log 41 ∧ Real.log 41 ≤ (3713572067216643 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_41
  constructor <;> linarith [h.1, h.2]

theorem eC_41 : (-62665213324769 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 41 * cCG cZ 41 ∧ ex (72426 / 100000) 41 * cCG cZ 41 ≤ (-62665205254127 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_41 cCB_41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_41 : (6541490180621 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 41 * sCG cZ 41 ∧ ex (72426 / 100000) 41 * sCG cZ 41 ≤ (3270746096931 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_41 sCB_41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_41 : (-46542357157807 / 200000000000000 : ℝ) ≤ Real.log 41 * (ex (72426 / 100000) 41 * cCG cZ 41) ∧ Real.log 41 * (ex (72426 / 100000) 41 * cCG cZ 41) ≤ (-23271175577623 / 100000000000000 : ℝ) := by
  exact mul_bounds_of lgB_41 eC_41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_42 : (3737669618127173 / 1000000000000000 : ℝ) ≤ Real.log 42 ∧ Real.log 42 ≤ (3737669618795767 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_42
  constructor <;> linarith [h.1, h.2]

theorem eC_42 : (50128582561981 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 42 * cCG cZ 42 ∧ ex (72426 / 100000) 42 * cCG cZ 42 ≤ (6266073816699 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_42 cCB_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_42 : (7120239901641 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 42 * cCG cZ 42) ∧ kappa * (ex (72426 / 100000) 42 * cCG cZ 42) ≤ (14240482067851 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_42 : (4405129503591 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 42 * sCG cZ 42 ∧ ex (72426 / 100000) 42 * sCG cZ 42 ≤ (44051303001981 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_42 sCB_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_42 : (12514049773733 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 42 * sCG cZ 42) ∧ kappa * (ex (72426 / 100000) 42 * sCG cZ 42) ≤ (1564256504591 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_42 : (37472816008339 / 200000000000000 : ℝ) ≤ Real.log 42 * (ex (72426 / 100000) 42 * cCG cZ 42) ∧ Real.log 42 * (ex (72426 / 100000) 42 * cCG cZ 42) ≤ (9368205493523 / 50000000000000 : ℝ) := by
  exact mul_bounds_of lgB_42 eC_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_42 : (53226208708283 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 42 * (ex (72426 / 100000) 42 * cCG cZ 42)) ∧ kappa * (Real.log 42 * (ex (72426 / 100000) 42 * cCG cZ 42)) ≤ (53226217182011 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_43 : (1880600057768679 / 500000000000000 : ℝ) ≤ Real.log 43 ∧ Real.log 43 ≤ (1880600058103007 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_43
  constructor <;> linarith [h.1, h.2]

theorem eC_43 : (543543039179 / 50000000000000 : ℝ) ≤ ex (72426 / 100000) 43 * cCG cZ 43 ∧ ex (72426 / 100000) 43 * cCG cZ 43 ≤ (10870868596733 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_43 cCB_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_43 : (3088183737121 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 43 * cCG cZ 43) ∧ kappa * (ex (72426 / 100000) 43 * cCG cZ 43) ≤ (123527438267 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_43 : (-64699176771161 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 43 * sCG cZ 43 ∧ ex (72426 / 100000) 43 * sCG cZ 43 ≤ (-16174792232983 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_43 sCB_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_43 : (-9189840137207 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 43 * sCG cZ 43) ∧ kappa * (ex (72426 / 100000) 43 * sCG cZ 43) ≤ (-4594919511863 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_43 : (40887482835191 / 1000000000000000 : ℝ) ≤ Real.log 43 * (ex (72426 / 100000) 43 * cCG cZ 43) ∧ Real.log 43 * (ex (72426 / 100000) 43 * cCG cZ 43) ≤ (40887512229293 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_43 eC_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_43 : (5807638514431 / 500000000000000 : ℝ) ≤ kappa * (Real.log 43 * (ex (72426 / 100000) 43 * cCG cZ 43)) ∧ kappa * (Real.log 43 * (ex (72426 / 100000) 43 * cCG cZ 43)) ≤ (11615285379111 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_44 : (3784189633762049 / 1000000000000000 : ℝ) ≤ Real.log 44 ∧ Real.log 44 ≤ (3784189634430759 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_44
  constructor <;> linarith [h.1, h.2]

theorem eC_44 : (-57123201564243 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 44 * cCG cZ 44 ∧ ex (72426 / 100000) 44 * cCG cZ 44 ≤ (-1428079846869 / 25000000000000 : ℝ) := by
  exact mul_bounds_of exB_44 cCB_44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_44 : (15001059543339 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 44 * sCG cZ 44 ∧ ex (72426 / 100000) 44 * sCG cZ 44 ≤ (30002126763001 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_44 sCB_44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_44 : (-54041256811227 / 250000000000000 : ℝ) ≤ Real.log 44 * (ex (72426 / 100000) 44 * cCG cZ 44) ∧ Real.log 44 * (ex (72426 / 100000) 44 * cCG cZ 44) ≤ (-108082499054123 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_44 eC_44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_46 : (3828641396332871 / 1000000000000000 : ℝ) ≤ Real.log 46 ∧ Real.log 46 ≤ (59822521828151 / 15625000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_46
  constructor <;> linarith [h.1, h.2]

theorem eC_46 : (-29009878685731 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 46 * cCG cZ 46 ∧ ex (72426 / 100000) 46 * cCG cZ 46 ≤ (-29009871245449 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_46 cCB_46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_46 : (-13833830929767 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 46 * sCG cZ 46 ∧ ex (72426 / 100000) 46 * sCG cZ 46 ≤ (-5533531626601 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_46 sCB_46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_46 : (-55534211229093 / 500000000000000 : ℝ) ≤ Real.log 46 * (ex (72426 / 100000) 46 * cCG cZ 46) ∧ Real.log 46 * (ex (72426 / 100000) 46 * cCG cZ 46) ≤ (-27767098488153 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_46 eC_46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_47 : (385014760155383 / 100000000000000 : ℝ) ≤ Real.log 47 ∧ Real.log 47 ≤ (60158556284729 / 15625000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_47
  constructor <;> linarith [h.1, h.2]

theorem eC_47 : (-2688728795919 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 47 * cCG cZ 47 ∧ ex (72426 / 100000) 47 * cCG cZ 47 ≤ (-10754907854907 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_47 cCB_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_47 : (-763811505491 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 47 * cCG cZ 47) ∧ kappa * (ex (72426 / 100000) 47 * cCG cZ 47) ≤ (-3055243940013 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_47 : (15141358592423 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 47 * sCG cZ 47 ∧ ex (72426 / 100000) 47 * sCG cZ 47 ≤ (30282720861299 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_47 sCB_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_47 : (17205370685521 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 47 * sCG cZ 47) ∧ kappa * (ex (72426 / 100000) 47 * sCG cZ 47) ≤ (2150671596791 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_47 : (-41408010906539 / 1000000000000000 : ℝ) ≤ Real.log 47 * (ex (72426 / 100000) 47 * cCG cZ 47) ∧ Real.log 47 * (ex (72426 / 100000) 47 * cCG cZ 47) ≤ (-20703991341251 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_47 eC_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_47 : (-11763148145663 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 47 * (ex (72426 / 100000) 47 * cCG cZ 47)) ∧ kappa * (Real.log 47 * (ex (72426 / 100000) 47 * cCG cZ 47)) ≤ (-2352628025561 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_48 : (1935600505375829 / 500000000000000 : ℝ) ≤ Real.log 48 ∧ Real.log 48 ≤ (3871201011420513 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_48
  constructor <;> linarith [h.1, h.2]

theorem eC_48 : (41487069798343 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 48 * cCG cZ 48 ∧ ex (72426 / 100000) 48 * cCG cZ 48 ≤ (41487077024999 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_48 cCB_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_48 : (11785607120053 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 48 * cCG cZ 48) ∧ kappa * (ex (72426 / 100000) 48 * cCG cZ 48) ≤ (2946402293249 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_48 : (-11036904493223 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 48 * sCG cZ 48 ∧ ex (72426 / 100000) 48 * sCG cZ 48 ≤ (-22073805370451 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_48 sCB_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_48 : (-12541413101571 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 48 * sCG cZ 48) ∧ kappa * (ex (72426 / 100000) 48 * sCG cZ 48) ≤ (-6270705523557 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_48 : (16060478653647 / 100000000000000 : ℝ) ≤ Real.log 48 * (ex (72426 / 100000) 48 * cCG cZ 48) ∧ Real.log 48 * (ex (72426 / 100000) 48 * cCG cZ 48) ≤ (160604814540057 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_48 eC_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_48 : (45624454195473 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 48 * (ex (72426 / 100000) 48 * cCG cZ 48)) ∧ kappa * (Real.log 48 * (ex (72426 / 100000) 48 * cCG cZ 48)) ≤ (45624462150707 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_49 : (389182029795439 / 100000000000000 : ℝ) ≤ Real.log 49 ∧ Real.log 49 ≤ (389182029862327 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_49
  constructor <;> linarith [h.1, h.2]

theorem eC_49 : (-56755357336731 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 49 * cCG cZ 49 ∧ ex (72426 / 100000) 49 * cCG cZ 49 ≤ (-56755350206621 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_49 cCB_49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_49 : (18466739214399 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 49 * sCG cZ 49 ∧ ex (72426 / 100000) 49 * sCG cZ 49 ≤ (18466746325953 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_49 sCB_49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_49 : (-220881651738707 / 1000000000000000 : ℝ) ≤ Real.log 49 * (ex (72426 / 100000) 49 * cCG cZ 49) ∧ Real.log 49 * (ex (72426 / 100000) 49 * cCG cZ 49) ≤ (-220881623951637 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_49 eC_49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_51 : (982956408142021 / 250000000000000 : ℝ) ≤ Real.log 51 ∧ Real.log 51 ≤ (982956408309251 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_51
  constructor <;> linarith [h.1, h.2]

theorem eC_51 : (-51658988095749 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 51 * cCG cZ 51 ∧ ex (72426 / 100000) 51 * cCG cZ 51 ≤ (-25829490585113 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_51 cCB_51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_51 : (-13162291306697 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 51 * sCG cZ 51 ∧ ex (72426 / 100000) 51 * sCG cZ 51 ≤ (-5264915140033 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_51 sCB_51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_51 : (-1586829168609 / 7812500000000 : ℝ) ≤ Real.log 51 * (ex (72426 / 100000) 51 * cCG cZ 51) ∧ Real.log 51 * (ex (72426 / 100000) 51 * cCG cZ 51) ≤ (-101557053158723 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_51 eC_51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_52 : (3951243718425183 / 1000000000000000 : ℝ) ≤ Real.log 52 ∧ Real.log 52 ≤ (3951243719094119 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_52
  constructor <;> linarith [h.1, h.2]

theorem eC_52 : (10350675066857 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 52 * cCG cZ 52 ∧ ex (72426 / 100000) 52 * cCG cZ 52 ≤ (2587669193777 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_52 cCB_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_52 : (5880819752191 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 52 * cCG cZ 52) ∧ kappa * (ex (72426 / 100000) 52 * cCG cZ 52) ≤ (1470205180687 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_52 : (9855877400761 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 52 * sCG cZ 52 ∧ ex (72426 / 100000) 52 * sCG cZ 52 ≤ (4927939553857 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_52 sCB_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_52 : (5599696456433 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 52 * sCG cZ 52) ∧ kappa * (ex (72426 / 100000) 52 * sCG cZ 52) ≤ (2239878970501 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_52 : (32718431871503 / 200000000000000 : ℝ) ≤ Real.log 52 * (ex (72426 / 100000) 52 * cCG cZ 52) ∧ Real.log 52 * (ex (72426 / 100000) 52 * cCG cZ 52) ≤ (40898046596019 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_52 eC_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_52 : (46473104210071 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 52 * (ex (72426 / 100000) 52 * cCG cZ 52)) ∧ kappa * (Real.log 52 * (ex (72426 / 100000) 52 * cCG cZ 52)) ≤ (46473111887751 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_53 : (31762335307167 / 8000000000000 : ℝ) ≤ Real.log 53 ∧ Real.log 53 ≤ (1985145957032413 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_53
  constructor <;> linarith [h.1, h.2]

theorem eC_53 : (-31165323209891 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 53 * cCG cZ 53 ∧ ex (72426 / 100000) 53 * cCG cZ 53 ≤ (-31165316523047 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_53 cCB_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_53 : (-2213353804611 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 53 * cCG cZ 53) ∧ kappa * (ex (72426 / 100000) 53 * cCG cZ 53) ≤ (-177068266377 / 20000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_53 : (-46991196504153 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 53 * sCG cZ 53 ∧ ex (72426 / 100000) 53 * sCG cZ 53 ≤ (-23495594904727 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_53 sCB_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_53 : (-13349214171817 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 53 * sCG cZ 53) ∧ kappa * (ex (72426 / 100000) 53 * sCG cZ 53) ≤ (-13349212269993 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_53 : (-15466928842431 / 125000000000000 : ℝ) ≤ Real.log 53 * (ex (72426 / 100000) 53 * cCG cZ 53) ∧ Real.log 53 * (ex (72426 / 100000) 53 * cCG cZ 53) ≤ (-30933851042469 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_53 eC_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_53 : (-7030128570729 / 200000000000000 : ℝ) ≤ kappa * (Real.log 53 * (ex (72426 / 100000) 53 * cCG cZ 53)) ∧ kappa * (Real.log 53 * (ex (72426 / 100000) 53 * cCG cZ 53)) ≤ (-7030127061157 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_54 : (1994492023204013 / 500000000000000 : ℝ) ≤ Real.log 54 ∧ Real.log 54 ≤ (3988984047076989 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_54
  constructor <;> linarith [h.1, h.2]

theorem eC_54 : (1431191581229 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 54 * cCG cZ 54 ∧ ex (72426 / 100000) 54 * cCG cZ 54 ≤ (1144953595699 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_54 cCB_54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_54 : (3168540526857 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 54 * sCG cZ 54 ∧ ex (72426 / 100000) 54 * sCG cZ 54 ≤ (50696655057507 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_54 sCB_54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_54 : (18268801231603 / 200000000000000 : ℝ) ≤ Real.log 54 * (ex (72426 / 100000) 54 * cCG cZ 54) ∧ Real.log 54 * (ex (72426 / 100000) 54 * cCG cZ 54) ≤ (18268806511547 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_54 eC_54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_56 : (2012675845289449 / 500000000000000 : ℝ) ≤ Real.log 56 ∧ Real.log 56 ≤ (2012675845623941 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_56
  constructor <;> linarith [h.1, h.2]

theorem eC_56 : (7517763790601 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 56 * cCG cZ 56 ∧ ex (72426 / 100000) 56 * cCG cZ 56 ≤ (3758883511021 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_56 cCB_56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_56 : (52054325437083 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 56 * sCG cZ 56 ∧ ex (72426 / 100000) 56 * sCG cZ 56 ≤ (6506791489739 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_56 sCB_56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_56 : (60523286367737 / 1000000000000000 : ℝ) ≤ Real.log 56 * (ex (72426 / 100000) 56 * cCG cZ 56) ∧ Real.log 56 * (ex (72426 / 100000) 56 * cCG cZ 56) ≤ (60523312393169 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_56 eC_56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_57 : (2021525633839149 / 500000000000000 : ℝ) ≤ Real.log 57 ∧ Real.log 57 ≤ (404305126834729 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_57
  constructor <;> linarith [h.1, h.2]

theorem eC_57 : (-3890938502759 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 57 * cCG cZ 57 ∧ ex (72426 / 100000) 57 * cCG cZ 57 ≤ (-3112749529549 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_57 cCB_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_57 : (-4421336358023 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 57 * cCG cZ 57) ∧ kappa * (ex (72426 / 100000) 57 * cCG cZ 57) ≤ (-552666818793 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_57 : (-25588964438569 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 57 * sCG cZ 57 ∧ ex (72426 / 100000) 57 * sCG cZ 57 ≤ (-51177922496579 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_57 sCB_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_57 : (-14538577101151 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 57 * sCG cZ 57) ∧ kappa * (ex (72426 / 100000) 57 * sCG cZ 57) ≤ (-7269287644283 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_57 : (-12585011078913 / 200000000000000 : ℝ) ≤ Real.log 57 * (ex (72426 / 100000) 57 * cCG cZ 57) ∧ Real.log 57 * (ex (72426 / 100000) 57 * cCG cZ 57) ≤ (-786562870713 / 12500000000000 : ℝ) := by
  exact mul_bounds_of lgB_57 eC_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_57 : (-8937844785047 / 500000000000000 : ℝ) ≤ kappa * (Real.log 57 * (ex (72426 / 100000) 57 * cCG cZ 57)) ∧ kappa * (Real.log 57 * (ex (72426 / 100000) 57 * cCG cZ 57)) ≤ (-17875682258601 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_58 : (4060443010370279 / 1000000000000000 : ℝ) ≤ Real.log 58 ∧ Real.log 58 ≤ (2030221505569357 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_58
  constructor <;> linarith [h.1, h.2]

theorem eC_58 : (18788481534499 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 58 * cCG cZ 58 ∧ ex (72426 / 100000) 58 * cCG cZ 58 ≤ (3757697746483 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_58 cCB_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_58 : (5337413869533 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 58 * cCG cZ 58) ∧ kappa * (ex (72426 / 100000) 58 * cCG cZ 58) ≤ (5337415914311 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_58 : (49368186482389 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 58 * sCG cZ 58 ∧ ex (72426 / 100000) 58 * sCG cZ 58 ≤ (9873638739467 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_58 sCB_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_58 : (3506116803013 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 58 * sCG cZ 58) ∧ kappa * (ex (72426 / 100000) 58 * sCG cZ 58) ≤ (3506117315417 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_58 : (76289558522227 / 1000000000000000 : ℝ) ≤ Real.log 58 * (ex (72426 / 100000) 58 * cCG cZ 58) ∧ Real.log 58 * (ex (72426 / 100000) 58 * cCG cZ 58) ≤ (76289587763393 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_58 eC_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_58 : (21672264840001 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 58 * (ex (72426 / 100000) 58 * cCG cZ 58)) ∧ kappa * (Real.log 58 * (ex (72426 / 100000) 58 * cCG cZ 58)) ≤ (5418068286701 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_59 : (2038768721855667 / 500000000000000 : ℝ) ≤ Real.log 59 ∧ Real.log 59 ≤ (4077537444570997 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_59
  constructor <;> linarith [h.1, h.2]

theorem eC_59 : (-2430563462811 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 59 * cCG cZ 59 ∧ ex (72426 / 100000) 59 * cCG cZ 59 ≤ (-60764066719 / 2500000000000 : ℝ) := by
  exact mul_bounds_of exB_59 cCB_59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_59 : (-5770642170207 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 59 * sCG cZ 59 ∧ ex (72426 / 100000) 59 * sCG cZ 59 ≤ (-46165129407511 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_59 sCB_59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_59 : (-4955356765509 / 50000000000000 : ℝ) ≤ Real.log 59 * (ex (72426 / 100000) 59 * cCG cZ 59) ∧ Real.log 59 * (ex (72426 / 100000) 59 * cCG cZ 59) ≤ (-49553551455779 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_59 eC_59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_61 : (205543693197337 / 50000000000000 : ℝ) ≤ Real.log 61 ∧ Real.log 61 ≤ (2055436932483667 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_61
  constructor <;> linarith [h.1, h.2]

theorem eC_61 : (-19580197800541 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 61 * cCG cZ 61 ∧ ex (72426 / 100000) 61 * cCG cZ 61 ≤ (-39160386384061 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_61 cCB_61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_61 : (-1017488649371 / 31250000000000 : ℝ) ≤ ex (72426 / 100000) 61 * sCG cZ 61 ∧ ex (72426 / 100000) 61 * sCG cZ 61 ≤ (-1627981378449 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_61 sCB_61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_61 : (-16098344681827 / 100000000000000 : ℝ) ≤ Real.log 61 * (ex (72426 / 100000) 61 * cCG cZ 61) ∧ Real.log 61 * (ex (72426 / 100000) 61 * cCG cZ 61) ≤ (-40245852222073 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_61 eC_61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_62 : (515891798100539 / 125000000000000 : ℝ) ≤ Real.log 62 ∧ Real.log 62 ≤ (82542687717919 / 20000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_62
  constructor <;> linarith [h.1, h.2]

theorem eC_62 : (11461979226759 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 62 * cCG cZ 62 ∧ ex (72426 / 100000) 62 * cCG cZ 62 ≤ (45847926664549 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_62 cCB_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_62 : (520977295881 / 40000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 62 * cCG cZ 62) ∧ kappa * (ex (72426 / 100000) 62 * cCG cZ 62) ≤ (13024435168931 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_62 : (20766732321881 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 62 * sCG cZ 62 ∧ ex (72426 / 100000) 62 * sCG cZ 62 ≤ (20766742059549 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_62 sCB_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_62 : (5899393461689 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 62 * sCG cZ 62) ∧ kappa * (ex (72426 / 100000) 62 * sCG cZ 62) ≤ (2949698113979 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_62 : (189220514338679 / 1000000000000000 : ℝ) ≤ Real.log 62 * (ex (72426 / 100000) 62 * cCG cZ 62) ∧ Real.log 62 * (ex (72426 / 100000) 62 * cCG cZ 62) ≤ (5913142333103 / 31250000000000 : ℝ) := by
  exact mul_bounds_of lgB_62 eC_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_62 : (26876791394161 / 500000000000000 : ℝ) ≤ kappa * (Real.log 62 * (ex (72426 / 100000) 62 * cCG cZ 62)) ∧ kappa * (Real.log 62 * (ex (72426 / 100000) 62 * cCG cZ 62)) ≤ (26876797121283 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_63 : (828626945227529 / 200000000000000 : ℝ) ≤ Real.log 63 ∧ Real.log 63 ≤ (517891840911853 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_63
  constructor <;> linarith [h.1, h.2]

theorem eC_63 : (-49445661265217 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 63 * cCG cZ 63 ∧ ex (72426 / 100000) 63 * cCG cZ 63 ≤ (-9889130205449 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_63 cCB_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_63 : (-351161904357 / 25000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 63 * cCG cZ 63) ∧ kappa * (ex (72426 / 100000) 63 * cCG cZ 63) ≤ (-7023236632943 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_63 : (-5511628120601 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 63 * sCG cZ 63 ∧ ex (72426 / 100000) 63 * sCG cZ 63 ≤ (-5511617919469 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_63 sCB_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_63 : (-313147609301 / 200000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 63 * sCG cZ 63) ∧ kappa * (ex (72426 / 100000) 63 * sCG cZ 63) ≤ (-48929223393 / 31250000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_63 : (-102430018150989 / 500000000000000 : ℝ) ≤ Real.log 63 * (ex (72426 / 100000) 63 * cCG cZ 63) ∧ Real.log 63 * (ex (72426 / 100000) 63 * cCG cZ 63) ≤ (-102429996913731 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_63 eC_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_63 : (-58196443233779 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 63 * (ex (72426 / 100000) 63 * cCG cZ 63)) ∧ kappa * (Real.log 63 * (ex (72426 / 100000) 63 * cCG cZ 63)) ≤ (-29098215583829 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_64 : (1039720770773419 / 250000000000000 : ℝ) ≤ Real.log 64 ∧ Real.log 64 ≤ (831776616862279 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_64
  constructor <;> linarith [h.1, h.2]

theorem eC_64 : (37253959121 / 781250000000 : ℝ) ≤ ex (72426 / 100000) 64 * cCG cZ 64 ∧ ex (72426 / 100000) 64 * cCG cZ 64 ≤ (23842539169491 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_64 cCB_64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_64 : (-754049100503 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 64 * sCG cZ 64 ∧ ex (72426 / 100000) 64 * sCG cZ 64 ≤ (-6032387487689 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_64 sCB_64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_64 : (39663324253847 / 200000000000000 : ℝ) ≤ Real.log 64 * (ex (72426 / 100000) 64 * cCG cZ 64) ∧ Real.log 64 * (ex (72426 / 100000) 64 * cCG cZ 64) ≤ (24789583209757 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_64 eC_64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_66 : (261853421358679 / 62500000000000 : ℝ) ≤ Real.log 66 ∧ Real.log 66 ≤ (837930948612883 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_66
  constructor <;> linarith [h.1, h.2]

theorem eC_66 : (4418984032531 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 66 * cCG cZ 66 ∧ ex (72426 / 100000) 66 * cCG cZ 66 ≤ (11047465742871 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_66 cCB_66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_66 : (-2670561488393 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 66 * sCG cZ 66 ∧ ex (72426 / 100000) 66 * sCG cZ 66 ≤ (-42728972471367 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_66 sCB_66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_66 : (92570087027809 / 1000000000000000 : ℝ) ≤ Real.log 66 * (ex (72426 / 100000) 66 * cCG cZ 66) ∧ Real.log 66 * (ex (72426 / 100000) 66 * cCG cZ 66) ≤ (92570134496923 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_66 eC_66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_67 : (131396644346681 / 31250000000000 : ℝ) ≤ Real.log 67 ∧ Real.log 67 ≤ (840938524093481 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_67
  constructor <;> linarith [h.1, h.2]

theorem eC_67 : (84850659071 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 67 * cCG cZ 67 ∧ ex (72426 / 100000) 67 * cCG cZ 67 ≤ (339414194471 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_67 cCB_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_67 : (12052147049 / 125000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 67 * cCG cZ 67) ∧ kappa * (ex (72426 / 100000) 67 * cCG cZ 67) ≤ (12052557479 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_67 : (23790631263483 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 67 * sCG cZ 67 ∧ ex (72426 / 100000) 67 * sCG cZ 67 ≤ (2973829633261 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_67 sCB_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_67 : (675841978169 / 50000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 67 * sCG cZ 67) ∧ kappa * (ex (72426 / 100000) 67 * sCG cZ 67) ≤ (6758421430089 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_67 : (356770939921 / 250000000000000 : ℝ) ≤ Real.log 67 * (ex (72426 / 100000) 67 * cCG cZ 67) ∧ Real.log 67 * (ex (72426 / 100000) 67 * cCG cZ 67) ≤ (57085294351 / 40000000000000 : ℝ) := by
  exact mul_bounds_of lgB_67 eC_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_67 : (405404589931 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 67 * (ex (72426 / 100000) 67 * cCG cZ 67)) ∧ kappa * (Real.log 67 * (ex (72426 / 100000) 67 * cCG cZ 67)) ≤ (81083679183 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_68 : (1054876926217503 / 250000000000000 : ℝ) ≤ Real.log 68 ∧ Real.log 68 ≤ (421950770628823 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_68
  constructor <;> linarith [h.1, h.2]

theorem eC_68 : (-23832880699639 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 68 * cCG cZ 68 ∧ ex (72426 / 100000) 68 * cCG cZ 68 ≤ (-23832868858299 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_68 cCB_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_68 : (-6770421961117 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 68 * cCG cZ 68) ∧ kappa * (ex (72426 / 100000) 68 * cCG cZ 68) ≤ (-6770418597239 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_68 : (-20297888948929 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 68 * sCG cZ 68 ∧ ex (72426 / 100000) 68 * sCG cZ 68 ≤ (-10148941509811 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_68 sCB_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_68 : (-5766204884591 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 68 * sCG cZ 68) ∧ kappa * (ex (72426 / 100000) 68 * sCG cZ 68) ≤ (-11532406400397 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_68 : (-4022520951007 / 40000000000000 : ℝ) ≤ Real.log 68 * (ex (72426 / 100000) 68 * cCG cZ 68) ∧ Real.log 68 * (ex (72426 / 100000) 68 * cCG cZ 68) ≤ (-100562973776749 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_68 eC_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_68 : (-28567847639753 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 68 * (ex (72426 / 100000) 68 * cCG cZ 68)) ∧ kappa * (Real.log 68 * (ex (72426 / 100000) 68 * cCG cZ 68)) ≤ (-28567833436247 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_69 : (1058526626070719 / 250000000000000 : ℝ) ≤ Real.log 69 ∧ Real.log 69 ≤ (4234106505742537 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_69
  constructor <;> linarith [h.1, h.2]

theorem eC_69 : (827181791309 / 20000000000000 : ℝ) ≤ ex (72426 / 100000) 69 * cCG cZ 69 ∧ ex (72426 / 100000) 69 * cCG cZ 69 ≤ (161558990853 / 3906250000000 : ℝ) := by
  exact mul_bounds_of exB_69 cCB_69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_69 : (21426108360197 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 69 * sCG cZ 69 ∧ ex (72426 / 100000) 69 * sCG cZ 69 ≤ (10713060216009 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_69 sCB_69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_69 : (175118790140289 / 1000000000000000 : ℝ) ≤ Real.log 69 * (ex (72426 / 100000) 69 * cCG cZ 69) ∧ Real.log 69 * (ex (72426 / 100000) 69 * cCG cZ 69) ≤ (175118841403363 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_69 eC_69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_71 : (852535975342409 / 200000000000000 : ℝ) ≤ Real.log 71 ∧ Real.log 71 ≤ (4262679878246141 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_71
  constructor <;> linarith [h.1, h.2]

theorem eC_71 : (16594845831249 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 71 * cCG cZ 71 ∧ ex (72426 / 100000) 71 * cCG cZ 71 ≤ (3318970411607 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_71 cCB_71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_71 : (-31307036131229 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 71 * sCG cZ 71 ∧ ex (72426 / 100000) 71 * sCG cZ 71 ≤ (-3913377960361 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_71 sCB_71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_71 : (141477030764007 / 1000000000000000 : ℝ) ≤ Real.log 71 * (ex (72426 / 100000) 71 * cCG cZ 71) ∧ Real.log 71 * (ex (72426 / 100000) 71 * cCG cZ 71) ≤ (28295416780103 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_71 eC_71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_72 : (133645816208753 / 31250000000000 : ℝ) ≤ Real.log 72 ∧ Real.log 72 ≤ (106916653006191 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_72
  constructor <;> linarith [h.1, h.2]

theorem eC_72 : (-6498871346279 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 72 * cCG cZ 72 ∧ ex (72426 / 100000) 72 * cCG cZ 72 ≤ (-3249429395021 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_72 cCB_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_72 : (-1846193158093 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 72 * cCG cZ 72) ∧ kappa * (ex (72426 / 100000) 72 * cCG cZ 72) ≤ (-230773698891 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_72 : (8939129892161 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 72 * sCG cZ 72 ∧ ex (72426 / 100000) 72 * sCG cZ 72 ≤ (2793478878777 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_72 sCB_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_72 : (12697097362651 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 72 * sCG cZ 72) ∧ kappa * (ex (72426 / 100000) 72 * sCG cZ 72) ≤ (6348550470971 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_72 : (-347418786331 / 12500000000000 : ℝ) ≤ Real.log 72 * (ex (72426 / 100000) 72 * cCG cZ 72) ∧ Real.log 72 * (ex (72426 / 100000) 72 * cCG cZ 72) ≤ (-13896724598729 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_72 eC_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_72 : (-7895551730649 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 72 * (ex (72426 / 100000) 72 * cCG cZ 72)) ∧ kappa * (Real.log 72 * (ex (72426 / 100000) 72 * cCG cZ 72)) ≤ (-98694205913 / 12500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_73 : (4290459440806191 / 1000000000000000 : ℝ) ≤ Real.log 73 ∧ Real.log 73 ≤ (4290459442404939 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_73
  constructor <;> linarith [h.1, h.2]

theorem eC_73 : (-23748658138761 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 73 * cCG cZ 73 ∧ ex (72426 / 100000) 73 * cCG cZ 73 ≤ (-11874322739089 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_73 cCB_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_73 : (-6746496096553 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 73 * cCG cZ 73) ∧ kappa * (ex (72426 / 100000) 73 * cCG cZ 73) ≤ (-1349298499989 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_73 : (-592017545921 / 15625000000000 : ℝ) ≤ ex (72426 / 100000) 73 * sCG cZ 73 ∧ ex (72426 / 100000) 73 * sCG cZ 73 ≤ (-37889110261893 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_73 sCB_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_73 : (-84089889191 / 7812500000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 73 * sCG cZ 73) ∧ kappa * (ex (72426 / 100000) 73 * sCG cZ 73) ≤ (-5381751107581 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_73 : (-20378530911179 / 200000000000000 : ℝ) ≤ Real.log 73 * (ex (72426 / 100000) 73 * cCG cZ 73) ∧ Real.log 73 * (ex (72426 / 100000) 73 * cCG cZ 73) ≤ (-1592071878097 / 15625000000000 : ℝ) := by
  exact mul_bounds_of lgB_73 eC_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_73 : (-28945567880601 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 73 * (ex (72426 / 100000) 73 * cCG cZ 73)) ∧ kappa * (Real.log 73 * (ex (72426 / 100000) 73 * cCG cZ 73)) ≤ (-90454851371 / 3125000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_74 : (2152032546428071 / 500000000000000 : ℝ) ≤ Real.log 74 ∧ Real.log 74 ≤ (1076016273621007 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_74
  constructor <;> linarith [h.1, h.2]

theorem eC_74 : (42632847725227 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 74 * cCG cZ 74 ∧ ex (72426 / 100000) 74 * cCG cZ 74 ≤ (4263286052067 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_74 cCB_74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_74 : (11958306411309 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 74 * sCG cZ 74 ∧ ex (72426 / 100000) 74 * sCG cZ 74 ≤ (5979159585283 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_74 sCB_74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_74 : (229368189629 / 1250000000000 : ℝ) ≤ Real.log 74 * (ex (72426 / 100000) 74 * cCG cZ 74) ∧ Real.log 74 * (ex (72426 / 100000) 74 * cCG cZ 74) ≤ (91747303422511 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_74 eC_74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_76 : (4330733339927761 / 1000000000000000 : ℝ) ≤ Real.log 76 ∧ Real.log 76 ≤ (4330733341608359 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_76
  constructor <;> linarith [h.1, h.2]

theorem eC_76 : (5863853054269 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 76 * cCG cZ 76 ∧ ex (72426 / 100000) 76 * cCG cZ 76 ≤ (11727719053421 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_76 cCB_76 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_76 : (-5227229582501 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 76 * sCG cZ 76 ∧ ex (72426 / 100000) 76 * sCG cZ 76 ≤ (-20908911839239 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_76 sCB_76 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_76 : (50789567845119 / 1000000000000000 : ℝ) ≤ Real.log 76 * (ex (72426 / 100000) 76 * cCG cZ 76) ∧ Real.log 76 * (ex (72426 / 100000) 76 * cCG cZ 76) ≤ (25394811962833 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_76 eC_76 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_77 : (4343805421490343 / 1000000000000000 : ℝ) ≤ Real.log 77 ∧ Real.log 77 ≤ (4343805423194797 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_77
  constructor <;> linarith [h.1, h.2]

theorem eC_77 : (4558132908831 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 77 * cCG cZ 77 ∧ ex (72426 / 100000) 77 * cCG cZ 77 ≤ (5697669391751 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_77 cCB_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_77 : (6474350192191 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 77 * cCG cZ 77) ∧ kappa * (ex (72426 / 100000) 77 * cCG cZ 77) ≤ (647435389171 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_77 : (9122342689533 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 77 * sCG cZ 77 ∧ ex (72426 / 100000) 77 * sCG cZ 77 ≤ (36489383797981 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_77 sCB_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_77 : (2591466388827 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 77 * sCG cZ 77) ∧ kappa * (ex (72426 / 100000) 77 * sCG cZ 77) ≤ (10365869259657 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_77 : (24749553051567 / 250000000000000 : ℝ) ≤ Real.log 77 * (ex (72426 / 100000) 77 * cCG cZ 77) ∧ Real.log 77 * (ex (72426 / 100000) 77 * cCG cZ 77) ≤ (24749567203459 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_77 eC_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_77 : (14061658732733 / 500000000000000 : ℝ) ≤ kappa * (Real.log 77 * (ex (72426 / 100000) 77 * cCG cZ 77)) ∧ kappa * (Real.log 77 * (ex (72426 / 100000) 77 * cCG cZ 77)) ≤ (28123333546491 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_78 : (4356708826321779 / 1000000000000000 : ℝ) ≤ Real.log 78 ∧ Real.log 78 ≤ (4356708828048589 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_78
  constructor <;> linarith [h.1, h.2]

theorem eC_78 : (-21068504107399 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 78 * cCG cZ 78 ∧ ex (72426 / 100000) 78 * cCG cZ 78 ≤ (-2106849757149 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_78 cCB_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_78 : (-2992560250989 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 78 * cCG cZ 78) ∧ kappa * (ex (72426 / 100000) 78 * cCG cZ 78) ≤ (-478809491621 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_78 : (-1282016142159 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 78 * sCG cZ 78 ∧ ex (72426 / 100000) 78 * sCG cZ 78 ≤ (-801258460461 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_78 sCB_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_78 : (-1820969599263 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 78 * sCG cZ 78) ∧ kappa * (ex (72426 / 100000) 78 * sCG cZ 78) ≤ (-910482949267 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_78 : (-183578675676967 / 1000000000000000 : ℝ) ≤ Real.log 78 * (ex (72426 / 100000) 78 * cCG cZ 78) ∧ Real.log 78 * (ex (72426 / 100000) 78 * cCG cZ 78) ≤ (-91789309327049 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_78 eC_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_78 : (-52150854655803 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 78 * (ex (72426 / 100000) 78 * cCG cZ 78)) ∧ kappa * (Real.log 78 * (ex (72426 / 100000) 78 * cCG cZ 78)) ≤ (-52150838456799 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_79 : (546180981511877 / 125000000000000 : ℝ) ≤ Real.log 79 ∧ Real.log 79 ≤ (4369447853842793 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_79
  constructor <;> linarith [h.1, h.2]

theorem eC_79 : (31196924335651 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 79 * cCG cZ 79 ∧ ex (72426 / 100000) 79 * cCG cZ 79 ≤ (31196937439611 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_79 cCB_79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_79 : (-7115799742047 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 79 * sCG cZ 79 ∧ ex (72426 / 100000) 79 * sCG cZ 79 ≤ (-28463185869919 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_79 sCB_79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_79 : (6815666701519 / 50000000000000 : ℝ) ≤ Real.log 79 * (ex (72426 / 100000) 79 * cCG cZ 79) ∧ Real.log 79 * (ex (72426 / 100000) 79 * cCG cZ 79) ≤ (136313391341977 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_79 eC_79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_81 : (4394449154292799 / 1000000000000000 : ℝ) ≤ Real.log 81 ∧ Real.log 81 ≤ (4394449156078747 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_81
  constructor <;> linarith [h.1, h.2]

theorem eC_81 : (-17821927061407 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 81 * cCG cZ 81 ∧ ex (72426 / 100000) 81 * cCG cZ 81 ≤ (-17821920476457 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_81 cCB_81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_81 : (-1325070794267 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 81 * sCG cZ 81 ∧ ex (72426 / 100000) 81 * sCG cZ 81 ≤ (-10600559778557 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_81 sCB_81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_81 : (-78317552334697 / 500000000000000 : ℝ) ≤ Real.log 81 * (ex (72426 / 100000) 81 * cCG cZ 81) ∧ Real.log 81 * (ex (72426 / 100000) 81 * cCG cZ 81) ≤ (-156635046731279 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_81 eC_81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_82 : (4406719246881137 / 1000000000000000 : ℝ) ≤ Real.log 82 ∧ Real.log 82 ≤ (4406719248684467 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_82
  constructor <;> linarith [h.1, h.2]

theorem eC_82 : (297963182903 / 8000000000000 : ℝ) ≤ ex (72426 / 100000) 82 * cCG cZ 82 ∧ ex (72426 / 100000) 82 * cCG cZ 82 ≤ (9311352758701 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_82 cCB_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_82 : (10580637012341 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 82 * cCG cZ 82) ∧ kappa * (ex (72426 / 100000) 82 * cCG cZ 82) ≤ (10580640754211 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_82 : (-17391143867087 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 82 * sCG cZ 82 ∧ ex (72426 / 100000) 82 * sCG cZ 82 ≤ (-17391130721111 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_82 sCB_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_82 : (-2470229760527 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 82 * sCG cZ 82) ∧ kappa * (ex (72426 / 100000) 82 * sCG cZ 82) ≤ (-1235113946639 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_82 : (41032502905019 / 250000000000000 : ℝ) ≤ Real.log 82 * (ex (72426 / 100000) 82 * cCG cZ 82) ∧ Real.log 82 * (ex (72426 / 100000) 82 * cCG cZ 82) ≤ (41032517433059 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_82 eC_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_82 : (23312948383273 / 500000000000000 : ℝ) ≤ kappa * (Real.log 82 * (ex (72426 / 100000) 82 * cCG cZ 82)) ∧ kappa * (Real.log 82 * (ex (72426 / 100000) 82 * cCG cZ 82)) ≤ (23312956637497 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_83 : (4418840607410211 / 1000000000000000 : ℝ) ≤ Real.log 83 ∧ Real.log 83 ≤ (552355076153737 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_83
  constructor <;> linarith [h.1, h.2]

theorem eC_83 : (-5453034363973 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 83 * cCG cZ 83 ∧ ex (72426 / 100000) 83 * cCG cZ 83 ≤ (-272651062699 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_83 cCB_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_83 : (-1549092788147 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 83 * cCG cZ 83) ∧ kappa * (ex (72426 / 100000) 83 * cCG cZ 83) ≤ (-24204516623 / 15625000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_83 : (40379789300253 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 83 * sCG cZ 83 ∧ ex (72426 / 100000) 83 * sCG cZ 83 ≤ (4037980245631 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_83 sCB_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_83 : (11471051934893 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 83 * sCG cZ 83) ∧ kappa * (ex (72426 / 100000) 83 * sCG cZ 83) ≤ (5735527836127 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_83 : (-24096089691051 / 1000000000000000 : ℝ) ≤ Real.log 83 * (ex (72426 / 100000) 83 * cCG cZ 83) ∧ Real.log 83 * (ex (72426 / 100000) 83 * cCG cZ 83) ≤ (-24096031750157 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_83 eC_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_83 : (-6845194119727 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 83 * (ex (72426 / 100000) 83 * cCG cZ 83)) ∧ kappa * (Real.log 83 * (ex (72426 / 100000) 83 * cCG cZ 83)) ≤ (-1711294414983 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_84 : (4430816798453847 / 1000000000000000 : ℝ) ≤ Real.log 84 ∧ Real.log 84 ≤ (443081680028893 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_84
  constructor <;> linarith [h.1, h.2]

theorem eC_84 : (-15709155272733 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 84 * cCG cZ 84 ∧ ex (72426 / 100000) 84 * cCG cZ 84 ≤ (-31418297372731 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_84 cCB_84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_84 : (-6347245881841 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 84 * sCG cZ 84 ∧ ex (72426 / 100000) 84 * sCG cZ 84 ≤ (-793405323857 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_84 sCB_84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_84 : (-69604389100773 / 500000000000000 : ℝ) ≤ Real.log 84 * (ex (72426 / 100000) 84 * cCG cZ 84) ∧ Real.log 84 * (ex (72426 / 100000) 84 * cCG cZ 84) ≤ (-69604359888957 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_84 eC_84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_86 : (1113586823964601 / 250000000000000 : ℝ) ≤ Real.log 86 ∧ Real.log 86 ≤ (2227173648860837 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_86
  constructor <;> linarith [h.1, h.2]

theorem eC_86 : (-1239396204563 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 86 * cCG cZ 86 ∧ ex (72426 / 100000) 86 * cCG cZ 86 ≤ (-19830286917 / 4000000000000 : ℝ) := by
  exact mul_bounds_of exB_86 cCB_86 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_86 : (1970059113259 / 50000000000000 : ℝ) ≤ ex (72426 / 100000) 86 * sCG cZ 86 ∧ ex (72426 / 100000) 86 * sCG cZ 86 ≤ (19700597700349 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_86 sCB_86 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_86 : (-22082804538407 / 1000000000000000 : ℝ) ≤ Real.log 86 * (ex (72426 / 100000) 86 * cCG cZ 86) ∧ Real.log 86 * (ex (72426 / 100000) 86 * cCG cZ 86) ≤ (-690085819569 / 31250000000000 : ℝ) := by
  exact mul_bounds_of lgB_86 eC_86 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_87 : (2232954059128449 / 500000000000000 : ℝ) ≤ Real.log 87 ∧ Real.log 87 ≤ (178636324805323 / 40000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_87
  constructor <;> linarith [h.1, h.2]

theorem eC_87 : (-6512915422043 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 87 * cCG cZ 87 ∧ ex (72426 / 100000) 87 * cCG cZ 87 ≤ (-6512912797119 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_87 cCB_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_87 : (-4625456964269 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 87 * cCG cZ 87) ∧ kappa * (ex (72426 / 100000) 87 * cCG cZ 87) ≤ (-9250910200107 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_87 : (-2768096985101 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 87 * sCG cZ 87 ∧ ex (72426 / 100000) 87 * sCG cZ 87 ≤ (-22144762770519 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_87 sCB_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_87 : (-6290866758281 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 87 * sCG cZ 87) ∧ kappa * (ex (72426 / 100000) 87 * sCG cZ 87) ≤ (-6290863033921 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_87 : (-145430409345209 / 1000000000000000 : ℝ) ≤ Real.log 87 * (ex (72426 / 100000) 87 * cCG cZ 87) ∧ Real.log 87 * (ex (72426 / 100000) 87 * cCG cZ 87) ≤ (-36357587667691 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_87 eC_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_87 : (-41313731632107 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 87 * (ex (72426 / 100000) 87 * cCG cZ 87)) ∧ kappa * (Real.log 87 * (ex (72426 / 100000) 87 * cCG cZ 87)) ≤ (-20656857481963 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_88 : (1119334203519521 / 250000000000000 : ℝ) ≤ Real.log 88 ∧ Real.log 88 ≤ (4477336815966447 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_88
  constructor <;> linarith [h.1, h.2]

theorem eC_88 : (337977608263 / 10000000000000 : ℝ) ≤ ex (72426 / 100000) 88 * cCG cZ 88 ∧ ex (72426 / 100000) 88 * cCG cZ 88 ≤ (33797773933773 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_88 cCB_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_88 : (4800617789741 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 88 * cCG cZ 88) ∧ kappa * (ex (72426 / 100000) 88 * cCG cZ 88) ≤ (9601239303041 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_88 : (-19572707161477 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 88 * sCG cZ 88 ∧ ex (72426 / 100000) 88 * sCG cZ 88 ≤ (-19572694073509 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_88 sCB_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_88 : (-5560195935801 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 88 * sCG cZ 88) ∧ kappa * (ex (72426 / 100000) 88 * sCG cZ 88) ≤ (-5560192217783 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_88 : (151323958780999 / 1000000000000000 : ℝ) ≤ Real.log 88 * (ex (72426 / 100000) 88 * cCG cZ 88) ∧ Real.log 88 * (ex (72426 / 100000) 88 * cCG cZ 88) ≤ (151324017531393 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_88 eC_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_88 : (10746991380163 / 250000000000000 : ℝ) ≤ kappa * (Real.log 88 * (ex (72426 / 100000) 88 * cCG cZ 88)) ∧ kappa * (Real.log 88 * (ex (72426 / 100000) 88 * cCG cZ 88)) ≤ (42987982210409 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_89 : (897727273865943 / 200000000000000 : ℝ) ≤ Real.log 89 ∧ Real.log 89 ≤ (448863637122959 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_89
  constructor <;> linarith [h.1, h.2]

theorem eC_89 : (3830945291321 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 89 * cCG cZ 89 ∧ ex (72426 / 100000) 89 * cCG cZ 89 ≤ (3830958337203 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_89 cCB_89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_89 : (19273941952979 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 89 * sCG cZ 89 ∧ ex (72426 / 100000) 89 * sCG cZ 89 ≤ (38547896999649 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_89 sCB_89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_89 : (3439144072707 / 200000000000000 : ℝ) ≤ Real.log 89 * (ex (72426 / 100000) 89 * cCG cZ 89) ∧ Real.log 89 * (ex (72426 / 100000) 89 * cCG cZ 89) ≤ (3439155785807 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_89 eC_89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_91 : (4510859506110189 / 1000000000000000 : ℝ) ≤ Real.log 91 ∧ Real.log 91 ≤ (1127714877007811 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_91
  constructor <;> linarith [h.1, h.2]

theorem eC_91 : (12076720156429 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 91 * cCG cZ 91 ∧ ex (72426 / 100000) 91 * cCG cZ 91 ≤ (24153453303819 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_91 cCB_91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_91 : (-5898104253319 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 91 * sCG cZ 91 ∧ ex (72426 / 100000) 91 * sCG cZ 91 ≤ (-1474525413369 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_91 sCB_91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_91 : (2723819396013 / 25000000000000 : ℝ) ≤ Real.log 91 * (ex (72426 / 100000) 91 * cCG cZ 91) ∧ Real.log 91 * (ex (72426 / 100000) 91 * cCG cZ 91) ≤ (108952834487321 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_91 eC_91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_92 : (452178857664043 / 100000000000000 : ℝ) ≤ Real.log 92 ∧ Real.log 92 ≤ (452178857857123 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_92
  constructor <;> linarith [h.1, h.2]

theorem eC_92 : (18927906761357 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 92 * cCG cZ 92 ∧ ex (72426 / 100000) 92 * cCG cZ 92 ≤ (9463959854773 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_92 cCB_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_92 : (2688510827333 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 92 * cCG cZ 92) ∧ kappa * (ex (72426 / 100000) 92 * cCG cZ 92) ≤ (336064083311 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_92 : (16370633695477 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 92 * sCG cZ 92 ∧ ex (72426 / 100000) 92 * sCG cZ 92 ≤ (32741280358509 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_92 sCB_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_92 : (1860221586909 / 200000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 92 * sCG cZ 92) ∧ kappa * (ex (72426 / 100000) 92 * sCG cZ 92) ≤ (9301111618357 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_92 : (85587992573219 / 1000000000000000 : ℝ) ≤ Real.log 92 * (ex (72426 / 100000) 92 * cCG cZ 92) ∧ Real.log 92 * (ex (72426 / 100000) 92 * cCG cZ 92) ≤ (85588051158739 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_92 eC_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_92 : (1215687754721 / 50000000000000 : ℝ) ≤ kappa * (Real.log 92 * (ex (72426 / 100000) 92 * cCG cZ 92)) ∧ kappa * (Real.log 92 * (ex (72426 / 100000) 92 * cCG cZ 92)) ≤ (24313771737339 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_93 : (11331498731857 / 2500000000000 : ℝ) ≤ Real.log 93 ∧ Real.log 93 ≤ (453259949468283 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_93
  constructor <;> linarith [h.1, h.2]

theorem eC_93 : (-9221482040777 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 93 * cCG cZ 93 ∧ ex (72426 / 100000) 93 * cCG cZ 93 ≤ (-36885915216897 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_93 cCB_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_93 : (-5239259601871 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 93 * cCG cZ 93) ∧ kappa * (ex (72426 / 100000) 93 * cCG cZ 93) ≤ (-5239257762997 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_93 : (1377860490223 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 93 * sCG cZ 93 ∧ ex (72426 / 100000) 93 * sCG cZ 93 ≤ (6889315355141 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_93 sCB_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_93 : (24463830663 / 12500000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 93 * sCG cZ 93) ∧ kappa * (ex (72426 / 100000) 93 * sCG cZ 93) ≤ (489277529701 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_93 : (-167189139353011 / 1000000000000000 : ℝ) ≤ Real.log 93 * (ex (72426 / 100000) 93 * cCG cZ 93) ∧ Real.log 93 * (ex (72426 / 100000) 93 * cCG cZ 93) ≤ (-167189080601461 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_93 eC_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_93 : (-9498986169581 / 200000000000000 : ℝ) ≤ kappa * (Real.log 93 * (ex (72426 / 100000) 93 * cCG cZ 93)) ∧ kappa * (Real.log 93 * (ex (72426 / 100000) 93 * cCG cZ 93)) ≤ (-2374745707891 / 50000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_94 : (4543294781857799 / 1000000000000000 : ℝ) ≤ Real.log 94 ∧ Real.log 94 ≤ (181731791352263 / 40000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_94
  constructor <;> linarith [h.1, h.2]

theorem eC_94 : (2495379452931 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 94 * cCG cZ 94 ∧ ex (72426 / 100000) 94 * cCG cZ 94 ≤ (4990771765997 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_94 cCB_94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_94 : (-36898250619143 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 94 * sCG cZ 94 ∧ ex (72426 / 100000) 94 * sCG cZ 94 ≤ (-36898237713931 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_94 sCB_94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_94 : (22674488894513 / 1000000000000000 : ℝ) ≤ Real.log 94 * (ex (72426 / 100000) 94 * cCG cZ 94) ∧ Real.log 94 * (ex (72426 / 100000) 94 * cCG cZ 94) ≤ (2834318416453 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_94 eC_94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_96 : (4564348191052399 / 1000000000000000 : ℝ) ≤ Real.log 96 ∧ Real.log 96 ≤ (570543524127167 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_96
  constructor <;> linarith [h.1, h.2]

theorem eC_96 : (-23987644694143 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 96 * cCG cZ 96 ∧ ex (72426 / 100000) 96 * cCG cZ 96 ≤ (-23987631903151 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_96 cCB_96 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_96 : (27736970100909 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 96 * sCG cZ 96 ∧ ex (72426 / 100000) 96 * sCG cZ 96 ≤ (6934245724623 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_96 sCB_96 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_96 : (-54743981357227 / 500000000000000 : ℝ) ≤ Real.log 96 * (ex (72426 / 100000) 96 * cCG cZ 96) ∧ Real.log 96 * (ex (72426 / 100000) 96 * cCG cZ 96) ≤ (-54743952142389 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_96 eC_96 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_97 : (1143677744521613 / 250000000000000 : ℝ) ≤ Real.log 97 ∧ Real.log 97 ≤ (2287355490029429 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_97
  constructor <;> linarith [h.1, h.2]

theorem eC_97 : (-20473632987639 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 97 * cCG cZ 97 ∧ ex (72426 / 100000) 97 * cCG cZ 97 ≤ (-319900316511 / 15625000000000 : ℝ) := by
  exact mul_bounds_of exB_97 cCB_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_97 : (-5816130083069 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 97 * cCG cZ 97) ∧ kappa * (ex (72426 / 100000) 97 * cCG cZ 97) ≤ (-1454031616619 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_97 : (-30092238258039 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 97 * sCG cZ 97 ∧ ex (72426 / 100000) 97 * sCG cZ 97 ≤ (-75230563783 / 2500000000000 : ℝ) := by
  exact mul_bounds_of exB_97 sCB_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_97 : (-4274287135681 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 97 * sCG cZ 97) ∧ kappa * (ex (72426 / 100000) 97 * sCG cZ 97) ≤ (-8548570650819 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_97 : (-11707619203781 / 125000000000000 : ℝ) ≤ Real.log 97 * (ex (72426 / 100000) 97 * cCG cZ 97) ∧ Real.log 97 * (ex (72426 / 100000) 97 * cCG cZ 97) ≤ (-23415223837379 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_97 eC_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_97 : (-26607114152463 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 97 * (ex (72426 / 100000) 97 * cCG cZ 97)) ∧ kappa * (Real.log 97 * (ex (72426 / 100000) 97 * cCG cZ 97)) ≤ (-26607097596127 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_98 : (2292483739126111 / 500000000000000 : ℝ) ≤ Real.log 98 ∧ Real.log 98 ≤ (2292483740115861 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_98
  constructor <;> linarith [h.1, h.2]

theorem eC_98 : (8465898974959 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 98 * cCG cZ 98 ∧ ex (72426 / 100000) 98 * cCG cZ 98 ≤ (33863608593139 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_98 cCB_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_98 : (9619937944223 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 98 * cCG cZ 98) ∧ kappa * (ex (72426 / 100000) 98 * cCG cZ 98) ≤ (76959532401 / 8000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_98 : (-786688517043 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 98 * sCG cZ 98 ∧ ex (72426 / 100000) 98 * sCG cZ 98 ≤ (-39334386281 / 3125000000000 : ℝ) := by
  exact mul_bounds_of exB_98 sCB_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_98 : (-3575707547549 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 98 * sCG cZ 98) ∧ kappa * (ex (72426 / 100000) 98 * sCG cZ 98) ≤ (-3575703950321 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_98 : (155263485897423 / 1000000000000000 : ℝ) ≤ Real.log 98 * (ex (72426 / 100000) 98 * cCG cZ 98) ∧ Real.log 98 * (ex (72426 / 100000) 98 * cCG cZ 98) ≤ (77631772081419 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_98 eC_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_98 : (44107102617069 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 98 * (ex (72426 / 100000) 98 * cCG cZ 98)) ∧ kappa * (Real.log 98 * (ex (72426 / 100000) 98 * cCG cZ 98)) ≤ (44107119169053 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_99 : (1148779962428723 / 250000000000000 : ℝ) ≤ Real.log 99 ∧ Real.log 99 ≤ (4595119851701133 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_99
  constructor <;> linarith [h.1, h.2]

theorem eC_99 : (2372843878487 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 99 * cCG cZ 99 ∧ ex (72426 / 100000) 99 * cCG cZ 99 ≤ (4745700352267 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_99 cCB_99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_99 : (7109433019823 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 99 * sCG cZ 99 ∧ ex (72426 / 100000) 99 * sCG cZ 99 ≤ (35547177738763 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_99 sCB_99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_99 : (1090350200631 / 50000000000000 : ℝ) ≤ Real.log 99 * (ex (72426 / 100000) 99 * cCG cZ 99) ∧ Real.log 99 * (ex (72426 / 100000) 99 * cCG cZ 99) ≤ (1362941368683 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_99 eC_99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_101 : (4615120516419061 / 1000000000000000 : ℝ) ≤ Real.log 101 ∧ Real.log 101 ≤ (2307560259208903 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_101
  constructor <;> linarith [h.1, h.2]

theorem eC_101 : (4541009080391 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 101 * cCG cZ 101 ∧ ex (72426 / 100000) 101 * cCG cZ 101 ≤ (90820306749 / 10000000000000 : ℝ) := by
  exact mul_bounds_of exB_101 cCB_101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_101 : (-34160124436043 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 101 * sCG cZ 101 ∧ ex (72426 / 100000) 101 * sCG cZ 101 ≤ (-34160111885583 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_101 sCB_101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_101 : (8382921668863 / 200000000000000 : ℝ) ≤ Real.log 101 * (ex (72426 / 100000) 101 * cCG cZ 101) ∧ Real.log 101 * (ex (72426 / 100000) 101 * cCG cZ 101) ≤ (41914666116631 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_101 eC_101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_102 : (289060800803807 / 62500000000000 : ℝ) ≤ Real.log 102 ∧ Real.log 102 ≤ (4624972814865459 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_102
  constructor <;> linarith [h.1, h.2]

theorem eC_102 : (6380165050239 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 102 * cCG cZ 102 ∧ ex (72426 / 100000) 102 * cCG cZ 102 ≤ (31900837756807 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_102 cCB_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_102 : (9062355935079 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 102 * cCG cZ 102) ∧ kappa * (ex (72426 / 100000) 102 * cCG cZ 102) ≤ (4531179743831 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_102 : (14629756752967 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 102 * sCG cZ 102 ∧ ex (72426 / 100000) 102 * sCG cZ 102 ≤ (14629769233473 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_102 sCB_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_102 : (415600731 / 100000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 102 * sCG cZ 102) ∧ kappa * (ex (72426 / 100000) 102 * sCG cZ 102) ≤ (4156010855451 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_102 : (147540449494603 / 1000000000000000 : ℝ) ≤ Real.log 102 * (ex (72426 / 100000) 102 * cCG cZ 102) ∧ Real.log 102 * (ex (72426 / 100000) 102 * cCG cZ 102) ≤ (73770253698333 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_102 eC_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_102 : (41913149820211 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 102 * (ex (72426 / 100000) 102 * cCG cZ 102)) ∧ kappa * (Real.log 102 * (ex (72426 / 100000) 102 * cCG cZ 102)) ≤ (1676526650759 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_103 : (1158682246951293 / 250000000000000 : ℝ) ≤ Real.log 103 ∧ Real.log 103 ≤ (4634728989815243 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_103
  constructor <;> linarith [h.1, h.2]

theorem eC_103 : (-4797204987207 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 103 * cCG cZ 103 ∧ ex (72426 / 100000) 103 * cCG cZ 103 ≤ (-4797201884681 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_103 cCB_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_103 : (-5451141623489 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 103 * cCG cZ 103) ∧ kappa * (ex (72426 / 100000) 103 * cCG cZ 103) ≤ (-2725569049019 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_103 : (29089485964659 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 103 * sCG cZ 103 ∧ ex (72426 / 100000) 103 * sCG cZ 103 ≤ (29089498389301 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_103 sCB_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_103 : (8263713358649 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 103 * sCG cZ 103) ∧ kappa * (ex (72426 / 100000) 103 * sCG cZ 103) ≤ (826371688823 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_103 : (-88934980097179 / 1000000000000000 : ℝ) ≤ Real.log 103 * (ex (72426 / 100000) 103 * cCG cZ 103) ∧ Real.log 103 * (ex (72426 / 100000) 103 * cCG cZ 103) ≤ (-44467461270569 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_103 eC_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_103 : (-25264564109973 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 103 * (ex (72426 / 100000) 103 * cCG cZ 103)) ∧ kappa * (Real.log 103 * (ex (72426 / 100000) 103 * cCG cZ 103)) ≤ (-25264547759507 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_104 : (290274431169741 / 62500000000000 : ℝ) ≤ Real.log 104 ∧ Real.log 104 ≤ (464439090073119 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_104
  constructor <;> linarith [h.1, h.2]

theorem eC_104 : (-1301265505739 / 50000000000000 : ℝ) ≤ ex (72426 / 100000) 104 * cCG cZ 104 ∧ ex (72426 / 100000) 104 * cCG cZ 104 ≤ (-13012648869847 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_104 cCB_104 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_104 : (-2851028103509 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 104 * sCG cZ 104 ∧ ex (72426 / 100000) 104 * sCG cZ 104 ≤ (-5702053114751 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_104 sCB_104 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_104 : (-3777241046431 / 31250000000000 : ℝ) ≤ Real.log 104 * (ex (72426 / 100000) 104 * cCG cZ 104) ∧ Real.log 104 * (ex (72426 / 100000) 104 * cCG cZ 104) ≤ (-24174331191721 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_104 eC_104 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_106 : (4663439093684591 / 1000000000000000 : ℝ) ≤ Real.log 106 ∧ Real.log 106 ≤ (4663439095709723 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_106
  constructor <;> linarith [h.1, h.2]

theorem eC_106 : (2002295655263 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 106 * cCG cZ 106 ∧ ex (72426 / 100000) 106 * cCG cZ 106 ≤ (2002296880669 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_106 cCB_106 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_106 : (13820470981391 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 106 * sCG cZ 106 ∧ ex (72426 / 100000) 106 * sCG cZ 106 ≤ (27640954228279 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_106 sCB_106 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_106 : (46687919179341 / 500000000000000 : ℝ) ≤ Real.log 106 * (ex (72426 / 100000) 106 * cCG cZ 106) ∧ Real.log 106 * (ex (72426 / 100000) 106 * cCG cZ 106) ≤ (18675179109059 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_106 eC_106 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_107 : (2336414417016759 / 500000000000000 : ℝ) ≤ Real.log 107 ∧ Real.log 107 ≤ (4672828836063211 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_107
  constructor <;> linarith [h.1, h.2]

theorem eC_107 : (-29102055862859 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 107 * cCG cZ 107 ∧ ex (72426 / 100000) 107 * cCG cZ 107 ≤ (-29102043652543 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_107 cCB_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_107 : (-516705262707 / 62500000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 107 * cCG cZ 107) ∧ kappa * (ex (72426 / 100000) 107 * cCG cZ 107) ≤ (-1033410091827 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_107 : (4346508462773 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 107 * sCG cZ 107 ∧ ex (72426 / 100000) 107 * sCG cZ 107 ≤ (4346511511031 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_107 sCB_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_107 : (987801574519 / 200000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 107 * sCG cZ 107) ∧ kappa * (ex (72426 / 100000) 107 * sCG cZ 107) ≤ (4939011336381 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_107 : (-13598892582469 / 100000000000000 : ℝ) ≤ Real.log 107 * (ex (72426 / 100000) 107 * cCG cZ 107) ∧ Real.log 107 * (ex (72426 / 100000) 107 * cCG cZ 107) ≤ (-27197773741781 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_107 eC_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_107 : (-38631604021163 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 107 * (ex (72426 / 100000) 107 * cCG cZ 107)) ∧ kappa * (Real.log 107 * (ex (72426 / 100000) 107 * cCG cZ 107)) ≤ (-7726317559153 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_108 : (58526640333687 / 12500000000000 : ℝ) ≤ Real.log 108 ∧ Real.log 108 ≤ (292633201795563 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_108
  constructor <;> linarith [h.1, h.2]

theorem eC_108 : (-7558111383743 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 108 * cCG cZ 108 ∧ ex (72426 / 100000) 108 * cCG cZ 108 ≤ (-15116210616887 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_108 cCB_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_108 : (-4294202110267 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 108 * cCG cZ 108) ∧ kappa * (ex (72426 / 100000) 108 * cCG cZ 108) ≤ (-858839731707 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_108 : (-117533521011 / 3906250000000 : ℝ) ≤ ex (72426 / 100000) 108 * sCG cZ 108 ∧ ex (72426 / 100000) 108 * sCG cZ 108 ≤ (-240708553649 / 8000000000000 : ℝ) := by
  exact mul_bounds_of exB_108 sCB_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_108 : (-8547535428609 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 108 * sCG cZ 108) ∧ kappa * (ex (72426 / 100000) 108 * sCG cZ 108) ≤ (-4273765985301 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_108 : (-70776138680071 / 1000000000000000 : ℝ) ≤ Real.log 108 * (ex (72426 / 100000) 108 * cCG cZ 108) ∧ Real.log 108 * (ex (72426 / 100000) 108 * cCG cZ 108) ≤ (-2211752554957 / 31250000000000 : ℝ) := by
  exact mul_bounds_of lgB_108 eC_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_108 : (-2513252225369 / 125000000000000 : ℝ) ≤ kappa * (Real.log 108 * (ex (72426 / 100000) 108 * cCG cZ 108)) ∧ kappa * (Real.log 108 * (ex (72426 / 100000) 108 * cCG cZ 108)) ≤ (-502650040819 / 25000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_108 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_109 : (4691347881799053 / 1000000000000000 : ℝ) ≤ Real.log 109 ∧ Real.log 109 ≤ (4691347883837257 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_109
  constructor <;> linarith [h.1, h.2]

theorem eC_109 : (15353010809471 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 109 * cCG cZ 109 ∧ ex (72426 / 100000) 109 * cCG cZ 109 ≤ (15353016857269 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_109 cCB_109 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_109 : (-2652741111079 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 109 * sCG cZ 109 ∧ ex (72426 / 100000) 109 * sCG cZ 109 ≤ (-6631846742791 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_109 sCB_109 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_109 : (144052629480499 / 1000000000000000 : ℝ) ≤ Real.log 109 * (ex (72426 / 100000) 109 * cCG cZ 109) ∧ Real.log 109 * (ex (72426 / 100000) 109 * cCG cZ 109) ≤ (72026343143867 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_109 eC_109 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_111 : (4709530200880691 / 1000000000000000 : ℝ) ≤ Real.log 111 ∧ Real.log 111 ≤ (4709530202926659 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_111
  constructor <;> linarith [h.1, h.2]

theorem eC_111 : (-3894939720079 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 111 * cCG cZ 111 ∧ ex (72426 / 100000) 111 * cCG cZ 111 ≤ (-31159505754991 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_111 cCB_111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_111 : (1362380910759 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 111 * sCG cZ 111 ∧ ex (72426 / 100000) 111 * sCG cZ 111 ≤ (217981185233 / 20000000000000 : ℝ) := by
  exact mul_bounds_of exB_111 sCB_111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_111 : (-146746690002327 / 1000000000000000 : ℝ) ≤ Real.log 111 * (ex (72426 / 100000) 111 * cCG cZ 111) ∧ Real.log 111 * (ex (72426 / 100000) 111 * cCG cZ 111) ≤ (-29349326679529 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_111 eC_111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_112 : (2359249435431363 / 500000000000000 : ℝ) ≤ Real.log 112 ∧ Real.log 112 ≤ (4718498872912321 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_112
  constructor <;> linarith [h.1, h.2]

theorem eC_112 : (-2078871235559 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 112 * cCG cZ 112 ∧ ex (72426 / 100000) 112 * cCG cZ 112 ≤ (-2598586065509 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_112 cCB_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_112 : (-118112750573 / 40000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 112 * cCG cZ 112) ∧ kappa * (ex (72426 / 100000) 112 * cCG cZ 112) ≤ (-2952815379307 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_112 : (-15553112824001 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 112 * sCG cZ 112 ∧ ex (72426 / 100000) 112 * sCG cZ 112 ≤ (-15553106850727 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_112 sCB_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_112 : (-8836626839569 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 112 * sCG cZ 112) ∧ kappa * (ex (72426 / 100000) 112 * sCG cZ 112) ≤ (-2209155861451 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_112 : (-1961830316383 / 40000000000000 : ℝ) ≤ Real.log 112 * (ex (72426 / 100000) 112 * cCG cZ 112) ∧ Real.log 112 * (ex (72426 / 100000) 112 * cCG cZ 112) ≤ (-1961828066551 / 40000000000000 : ℝ) := by
  exact mul_bounds_of lgB_112 eC_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_112 : (-13932872011381 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 112 * (ex (72426 / 100000) 112 * cCG cZ 112)) ∧ kappa * (Real.log 112 * (ex (72426 / 100000) 112 * cCG cZ 112)) ≤ (-13932856033127 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_113 : (2363693909139639 / 500000000000000 : ℝ) ≤ Real.log 113 ∧ Real.log 113 ≤ (4727387820332341 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_113
  constructor <;> linarith [h.1, h.2]

theorem eC_113 : (30905591358483 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 113 * cCG cZ 113 ∧ ex (72426 / 100000) 113 * cCG cZ 113 ≤ (3863200407251 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_113 cCB_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_113 : (219490771061 / 25000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 113 * cCG cZ 113) ∧ kappa * (ex (72426 / 100000) 113 * cCG cZ 113) ≤ (8779634222847 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_113 : (-258266626959 / 25000000000000 : ℝ) ≤ ex (72426 / 100000) 113 * sCG cZ 113 ∧ ex (72426 / 100000) 113 * sCG cZ 113 ≤ (-10330653209473 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_113 sCB_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_113 : (-2934725457697 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 113 * sCG cZ 113) ∧ kappa * (ex (72426 / 100000) 113 * sCG cZ 113) ≤ (-2934722085993 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_113 : (146102716104809 / 1000000000000000 : ℝ) ≤ Real.log 113 * (ex (72426 / 100000) 113 * cCG cZ 113) ∧ Real.log 113 * (ex (72426 / 100000) 113 * cCG cZ 113) ≤ (146102772421931 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_113 eC_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_113 : (41504719893541 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 113 * (ex (72426 / 100000) 113 * cCG cZ 113)) ∧ kappa * (Real.log 113 * (ex (72426 / 100000) 113 * cCG cZ 113)) ≤ (5188091986507 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_114 : (4736198447960769 / 1000000000000000 : ℝ) ≤ Real.log 114 ∧ Real.log 114 ≤ (4736198450017151 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_114
  constructor <;> linarith [h.1, h.2]

theorem eC_114 : (10691903245283 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 114 * cCG cZ 114 ∧ ex (72426 / 100000) 114 * cCG cZ 114 ≤ (5345957518121 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_114 cCB_114 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_114 : (6112594222801 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 114 * sCG cZ 114 ∧ ex (72426 / 100000) 114 * sCG cZ 114 ≤ (30562982934603 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_114 sCB_114 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_114 : (6329871944507 / 125000000000000 : ℝ) ≤ Real.log 114 * (ex (72426 / 100000) 114 * cCG cZ 114) ∧ Real.log 114 * (ex (72426 / 100000) 114 * cCG cZ 114) ≤ (10127806284473 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_114 eC_114 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_116 : (950718038134279 / 200000000000000 : ℝ) ≤ Real.log 116 ∧ Real.log 116 ≤ (4753590192733993 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_116
  constructor <;> linarith [h.1, h.2]

theorem eC_116 : (-2519395113357 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 116 * cCG cZ 116 ∧ ex (72426 / 100000) 116 * cCG cZ 116 ≤ (-3149240966153 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_116 cCB_116 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_116 : (-29387874844221 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 116 * sCG cZ 116 ∧ ex (72426 / 100000) 116 * sCG cZ 116 ≤ (-14693931558463 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_116 sCB_116 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_116 : (-59880859512379 / 1000000000000000 : ℝ) ≤ Real.log 116 * (ex (72426 / 100000) 116 * cCG cZ 116) ∧ Real.log 116 * (ex (72426 / 100000) 116 * cCG cZ 116) ≤ (-59880803859061 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_116 eC_116 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_117 : (1190543483590551 / 250000000000000 : ℝ) ≤ Real.log 117 ∧ Real.log 117 ≤ (952434787285543 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_117
  constructor <;> linarith [h.1, h.2]

theorem eC_117 : (28487075953027 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 117 * cCG cZ 117 ∧ ex (72426 / 100000) 117 * cCG cZ 117 ≤ (28487087599971 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_117 cCB_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_117 : (1618516259709 / 200000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 117 * cCG cZ 117) ∧ kappa * (ex (72426 / 100000) 117 * cCG cZ 117) ≤ (4046292303599 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_117 : (-3519447289301 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 117 * sCG cZ 117 ∧ ex (72426 / 100000) 117 * sCG cZ 117 ≤ (-2815555506371 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_117 sCB_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_117 : (-1999602441583 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 117 * sCG cZ 117) ∧ kappa * (ex (72426 / 100000) 117 * sCG cZ 117) ≤ (-3999201580647 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_117 : (135660410569701 / 1000000000000000 : ℝ) ≤ Real.log 117 * (ex (72426 / 100000) 117 * cCG cZ 117) ∧ Real.log 117 * (ex (72426 / 100000) 117 * cCG cZ 117) ≤ (33915116523329 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_117 eC_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_117 : (19269139860819 / 500000000000000 : ℝ) ≤ kappa * (Real.log 117 * (ex (72426 / 100000) 117 * cCG cZ 117)) ∧ kappa * (Real.log 117 * (ex (72426 / 100000) 117 * cCG cZ 117)) ≤ (19269147747367 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_117 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_118 : (954136924805911 / 200000000000000 : ℝ) ≤ Real.log 118 ∧ Real.log 118 ≤ (74541947282779 / 15625000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_118
  constructor <;> linarith [h.1, h.2]

theorem eC_118 : (15853631422143 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 118 * cCG cZ 118 ∧ ex (72426 / 100000) 118 * cCG cZ 118 ≤ (7926821496249 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_118 cCB_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_118 : (22518422279 / 5000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 118 * cCG cZ 118) ∧ kappa * (ex (72426 / 100000) 118 * cCG cZ 118) ≤ (4503687742697 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_118 : (13656396268451 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 118 * sCG cZ 118 ∧ ex (72426 / 100000) 118 * sCG cZ 118 ≤ (13656402062239 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_118 sCB_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_118 : (3879495994247 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 118 * sCG cZ 118) ∧ kappa * (ex (72426 / 100000) 118 * sCG cZ 118) ≤ (7758995280283 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_118 : (75632675660649 / 1000000000000000 : ℝ) ≤ Real.log 118 * (ex (72426 / 100000) 118 * cCG cZ 118) ∧ Real.log 118 * (ex (72426 / 100000) 118 * cCG cZ 118) ≤ (15126546178391 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_118 eC_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_118 : (21485658184769 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 118 * (ex (72426 / 100000) 118 * cCG cZ 118)) ∧ kappa * (Real.log 118 * (ex (72426 / 100000) 118 * cCG cZ 118)) ≤ (10742836937413 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_118 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_119 : (955824698534977 / 200000000000000 : ℝ) ≤ Real.log 119 ∧ Real.log 119 ≤ (238956174737293 / 50000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_119
  constructor <;> linarith [h.1, h.2]

theorem eC_119 : (-25806995793469 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 119 * cCG cZ 119 ∧ ex (72426 / 100000) 119 * cCG cZ 119 ≤ (-25806984253313 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_119 cCB_119 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_119 : (17866416587401 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 119 * sCG cZ 119 ∧ ex (72426 / 100000) 119 * sCG cZ 119 ≤ (714657124619 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_119 sCB_119 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_119 : (-963553280667 / 7812500000000 : ℝ) ≤ Real.log 119 * (ex (72426 / 100000) 119 * cCG cZ 119) ∧ Real.log 119 * (ex (72426 / 100000) 119 * cCG cZ 119) ≤ (-61667382360049 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_119 eC_119 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_121 : (4795790545159091 / 1000000000000000 : ℝ) ≤ Real.log 121 ∧ Real.log 121 ≤ (1198947636808773 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_121
  constructor <;> linarith [h.1, h.2]

theorem eC_121 : (21560680326713 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 121 * cCG cZ 121 ∧ ex (72426 / 100000) 121 * cCG cZ 121 ≤ (21560691755281 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_121 cCB_121 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_121 : (-22290046955191 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 121 * sCG cZ 121 ∧ ex (72426 / 100000) 121 * sCG cZ 121 ≤ (-22290035522929 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_121 sCB_121 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_121 : (103400506858047 / 1000000000000000 : ℝ) ≤ Real.log 121 * (ex (72426 / 100000) 121 * cCG cZ 121) ∧ Real.log 121 * (ex (72426 / 100000) 121 * cCG cZ 121) ≤ (103400561711827 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_121 eC_121 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_122 : (4804021044295607 / 1000000000000000 : ℝ) ≤ Real.log 122 ∧ Real.log 122 ≤ (4804021046371607 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_122
  constructor <;> linarith [h.1, h.2]

theorem eC_122 : (24497618621013 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 122 * cCG cZ 122 ∧ ex (72426 / 100000) 122 * cCG cZ 122 ≤ (4899525993647 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_122 cCB_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_122 : (434953754639 / 62500000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 122 * cCG cZ 122) ∧ kappa * (ex (72426 / 100000) 122 * cCG cZ 122) ≤ (6959263297733 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_122 : (9356519801601 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 122 * sCG cZ 122 ∧ ex (72426 / 100000) 122 * sCG cZ 122 ≤ (18713050941349 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_122 sCB_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_122 : (212639295913 / 40000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 122 * sCG cZ 122) ∧ kappa * (ex (72426 / 100000) 122 * sCG cZ 122) ≤ (1328996404689 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_122 : (58843537695237 / 500000000000000 : ℝ) ≤ Real.log 122 * (ex (72426 / 100000) 122 * cCG cZ 122) ∧ Real.log 122 * (ex (72426 / 100000) 122 * cCG cZ 122) ≤ (941497039629 / 8000000000000 : ℝ) := by
  exact mul_bounds_of lgB_122 eC_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_122 : (334324318493 / 10000000000000 : ℝ) ≤ kappa * (Real.log 122 * (ex (72426 / 100000) 122 * cCG cZ 122)) ∧ kappa * (Real.log 122 * (ex (72426 / 100000) 122 * cCG cZ 122)) ≤ (33432447349549 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_123 : (300761522183423 / 62500000000000 : ℝ) ≤ Real.log 123 ∧ Real.log 123 ≤ (300761522313173 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_123
  constructor <;> linarith [h.1, h.2]

theorem eC_123 : (-3833344277947 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 123 * cCG cZ 123 ∧ ex (72426 / 100000) 123 * cCG cZ 123 ≤ (-15333365838617 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_123 cCB_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_123 : (-2177945554381 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 123 * cCG cZ 123) ∧ kappa * (ex (72426 / 100000) 123 * cCG cZ 123) ≤ (-4355887906289 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_123 : (6633381905611 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 123 * sCG cZ 123 ∧ ex (72426 / 100000) 123 * sCG cZ 123 ≤ (26533538912511 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_123 sCB_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_123 : (7537619156697 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 123 * sCG cZ 123) ∧ kappa * (ex (72426 / 100000) 123 * sCG cZ 123) ≤ (7537622363969 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_123 : (-36893518738747 / 500000000000000 : ℝ) ≤ Real.log 123 * (ex (72426 / 100000) 123 * cCG cZ 123) ∧ Real.log 123 * (ex (72426 / 100000) 123 * cCG cZ 123) ≤ (-73786983197083 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_123 eC_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_123 : (-2620168881803 / 125000000000000 : ℝ) ≤ kappa * (Real.log 123 * (ex (72426 / 100000) 123 * cCG cZ 123)) ∧ kappa * (Real.log 123 * (ex (72426 / 100000) 123 * cCG cZ 123)) ≤ (-4192267126899 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_123 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_124 : (4820281565167387 / 1000000000000000 : ℝ) ≤ Real.log 124 ∧ Real.log 124 ≤ (1205070391810847 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_124
  constructor <;> linarith [h.1, h.2]

theorem eC_124 : (-28247450336057 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 124 * cCG cZ 124 ∧ ex (72426 / 100000) 124 * cCG cZ 124 ≤ (-14123719549259 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_124 cCB_124 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_124 : (-11413669704639 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 124 * sCG cZ 124 ∧ ex (72426 / 100000) 124 * sCG cZ 124 ≤ (-11413658492457 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_124 sCB_124 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_124 : (-136160664176519 / 1000000000000000 : ℝ) ≤ Real.log 124 * (ex (72426 / 100000) 124 * cCG cZ 124) ∧ Real.log 124 * (ex (72426 / 100000) 124 * cCG cZ 124) ≤ (-68080304974887 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_124 eC_124 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_126 : (1209070476628457 / 250000000000000 : ℝ) ≤ Real.log 126 ∧ Real.log 126 ≤ (4836281908589829 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_126
  constructor <;> linarith [h.1, h.2]

theorem eC_126 : (15021023227463 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 126 * cCG cZ 126 ∧ ex (72426 / 100000) 126 * cCG cZ 126 ≤ (3004205757619 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_126 cCB_126 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_126 : (1048790381551 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 126 * sCG cZ 126 ∧ ex (72426 / 100000) 126 * sCG cZ 126 ≤ (2097591842271 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_126 sCB_126 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_126 : (72645902852303 / 500000000000000 : ℝ) ≤ Real.log 126 * (ex (72426 / 100000) 126 * cCG cZ 126) ∧ Real.log 126 * (ex (72426 / 100000) 126 * cCG cZ 126) ≤ (72645929776271 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_126 eC_126 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_127 : (4844187086020941 / 1000000000000000 : ℝ) ≤ Real.log 127 ∧ Real.log 127 ≤ (2422093544048471 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_127
  constructor <;> linarith [h.1, h.2]

theorem eC_127 : (124605116313 / 40000000000000 : ℝ) ≤ ex (72426 / 100000) 127 * cCG cZ 127 ∧ ex (72426 / 100000) 127 * cCG cZ 127 ≤ (3115138916527 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_127 cCB_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_127 : (176988511499 / 200000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 127 * cCG cZ 127) ∧ kappa * (ex (72426 / 100000) 127 * cCG cZ 127) ≤ (442472842419 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_127 : (14890387678851 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 127 * sCG cZ 127 ∧ ex (72426 / 100000) 127 * sCG cZ 127 ≤ (14890393203287 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_127 sCB_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_127 : (4230047094221 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 127 * sCG cZ 127) ∧ kappa * (ex (72426 / 100000) 127 * sCG cZ 127) ≤ (2115024331799 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_127 : (15090262382389 / 1000000000000000 : ℝ) ≤ Real.log 127 * (ex (72426 / 100000) 127 * cCG cZ 127) ∧ Real.log 127 * (ex (72426 / 100000) 127 * cCG cZ 127) ≤ (15090315717069 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_127 eC_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_127 : (428682730889 / 100000000000000 : ℝ) ≤ kappa * (Real.log 127 * (ex (72426 / 100000) 127 * cCG cZ 127)) ∧ kappa * (Real.log 127 * (ex (72426 / 100000) 127 * cCG cZ 127)) ≤ (857368492031 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_128 : (4852030263481967 / 1000000000000000 : ℝ) ≤ Real.log 128 ∧ Real.log 128 ≤ (303251891597373 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_128
  constructor <;> linarith [h.1, h.2]

theorem eC_128 : (-14268992618237 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 128 * cCG cZ 128 ∧ ex (72426 / 100000) 128 * cCG cZ 128 ≤ (-2853797426461 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_128 cCB_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_128 : (-810704355911 / 100000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 128 * cCG cZ 128) ∧ kappa * (ex (72426 / 100000) 128 * cCG cZ 128) ≤ (-1013380055279 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_128 : (8488460945151 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 128 * sCG cZ 128 ∧ ex (72426 / 100000) 128 * sCG cZ 128 ≤ (848847188681 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_128 sCB_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_128 : (96455754759 / 40000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 128 * sCG cZ 128) ∧ kappa * (ex (72426 / 100000) 128 * sCG cZ 128) ≤ (301424622159 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_128 : (-138467168085419 / 1000000000000000 : ℝ) ≤ Real.log 128 * (ex (72426 / 100000) 128 * cCG cZ 128) ∧ Real.log 128 * (ex (72426 / 100000) 128 * cCG cZ 128) ≤ (-138467114790357 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_128 eC_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_128 : (-9833905178249 / 250000000000000 : ℝ) ≤ kappa * (Real.log 128 * (ex (72426 / 100000) 128 * cCG cZ 128)) ∧ kappa * (Real.log 128 * (ex (72426 / 100000) 128 * cCG cZ 128)) ≤ (-7867121114597 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_128 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_129 : (2429906201962011 / 500000000000000 : ℝ) ≤ Real.log 129 ∧ Real.log 129 ≤ (4859812406000023 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_129
  constructor <;> linarith [h.1, h.2]

theorem eC_129 : (-862315529737 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 129 * cCG cZ 129 ∧ ex (72426 / 100000) 129 * cCG cZ 129 ≤ (-6898518782479 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_129 cCB_129 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_129 : (-26194952540329 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 129 * sCG cZ 129 ∧ ex (72426 / 100000) 129 * sCG cZ 129 ≤ (-26194941610807 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_129 sCB_129 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_129 : (-33525533674419 / 500000000000000 : ℝ) ≤ Real.log 129 * (ex (72426 / 100000) 129 * cCG cZ 129) ∧ Real.log 129 * (ex (72426 / 100000) 129 * cCG cZ 129) ≤ (-16762753573897 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_129 eC_129 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_131 : (2437598661381751 / 500000000000000 : ℝ) ≤ Real.log 131 ∧ Real.log 131 ≤ (2437598662419751 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_131
  constructor <;> linarith [h.1, h.2]

theorem eC_131 : (23076112644793 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 131 * cCG cZ 131 ∧ ex (72426 / 100000) 131 * cCG cZ 131 ≤ (5769030861821 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_131 cCB_131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_131 : (9009833674461 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 131 * sCG cZ 131 ∧ ex (72426 / 100000) 131 * sCG cZ 131 ≤ (18019678143377 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_131 sCB_131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_131 : (112500602585683 / 1000000000000000 : ℝ) ≤ Real.log 131 * (ex (72426 / 100000) 131 * cCG cZ 131) ∧ Real.log 131 * (ex (72426 / 100000) 131 * cCG cZ 131) ≤ (56250327648933 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_131 eC_131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_132 : (4882801922148721 / 1000000000000000 : ℝ) ≤ Real.log 132 ∧ Real.log 132 ≤ (2441400962112361 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_132
  constructor <;> linarith [h.1, h.2]

theorem eC_132 : (-240134721 / 19531250000 : ℝ) ≤ ex (72426 / 100000) 132 * cCG cZ 132 ∧ ex (72426 / 100000) 132 * cCG cZ 132 ≤ (-6147443495283 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_132 cCB_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_132 : (-69854455741 / 20000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 132 * cCG cZ 132) ∧ kappa * (ex (72426 / 100000) 132 * cCG cZ 132) ≤ (-698543948081 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_132 : (26394325098839 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 132 * sCG cZ 132 ∧ ex (72426 / 100000) 132 * sCG cZ 132 ≤ (26394335844721 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_132 sCB_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_132 : (7498074636891 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 132 * sCG cZ 132) ∧ kappa * (ex (72426 / 100000) 132 * sCG cZ 132) ≤ (1874519422393 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_132 : (-2401342008877 / 40000000000000 : ℝ) ≤ Real.log 132 * (ex (72426 / 100000) 132 * cCG cZ 132) ∧ Real.log 132 * (ex (72426 / 100000) 132 * cCG cZ 132) ≤ (-7504187228767 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_132 eC_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_132 : (-1705427354539 / 100000000000000 : ℝ) ≤ kappa * (Real.log 132 * (ex (72426 / 100000) 132 * cCG cZ 132)) ∧ kappa * (Real.log 132 * (ex (72426 / 100000) 132 * cCG cZ 132)) ≤ (-852712933099 / 50000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_132 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_133 : (611293640973013 / 125000000000000 : ℝ) ≤ Real.log 133 ∧ Real.log 133 ≤ (978069825972021 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_133
  constructor <;> linarith [h.1, h.2]

theorem eC_133 : (-14194343253493 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 133 * cCG cZ 133 ∧ ex (72426 / 100000) 133 * cCG cZ 133 ≤ (-28388675813917 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_133 cCB_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_133 : (-806463091879 / 100000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 133 * cCG cZ 133) ∧ kappa * (ex (72426 / 100000) 133 * cCG cZ 133) ≤ (-1008078485139 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_133 : (-1143498528143 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 133 * sCG cZ 133 ∧ ex (72426 / 100000) 133 * sCG cZ 133 ≤ (-5717481981807 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_133 sCB_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_133 : (-1624219842539 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 133 * sCG cZ 133) ∧ kappa * (ex (72426 / 100000) 133 * sCG cZ 133) ≤ (-812108407283 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_133 : (-138830588357311 / 1000000000000000 : ℝ) ≤ Real.log 133 * (ex (72426 / 100000) 133 * cCG cZ 133) ∧ Real.log 133 * (ex (72426 / 100000) 133 * cCG cZ 133) ≤ (-69415268002767 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_133 eC_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_133 : (-39438860796347 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 133 * (ex (72426 / 100000) 133 * cCG cZ 133)) ∧ kappa * (Real.log 133 * (ex (72426 / 100000) 133 * cCG cZ 133)) ≤ (-39438845924303 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_133 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_134 : (2448919899756631 / 500000000000000 : ℝ) ≤ Real.log 134 ∧ Real.log 134 ≤ (2448919900794631 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_134
  constructor <;> linarith [h.1, h.2]

theorem eC_134 : (-278895053983 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 134 * cCG cZ 134 ∧ ex (72426 / 100000) 134 * cCG cZ 134 ≤ (-1394464683273 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_134 cCB_134 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_134 : (-28768257080863 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 134 * sCG cZ 134 ∧ ex (72426 / 100000) 134 * sCG cZ 134 ≤ (-28768246452973 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_134 sCB_134 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_134 : (-3414958239661 / 500000000000000 : ℝ) ≤ Real.log 134 * (ex (72426 / 100000) 134 * cCG cZ 134) ∧ Real.log 134 * (ex (72426 / 100000) 134 * cCG cZ 134) ≤ (-27319458499 / 4000000000000 : ℝ) := by
  exact mul_bounds_of lgB_134 eC_134 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_136 : (2456327442649201 / 500000000000000 : ℝ) ≤ Real.log 136 ∧ Real.log 136 ≤ (4912654887374403 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_136
  constructor <;> linarith [h.1, h.2]

theorem eC_136 : (3085703815049 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 136 * cCG cZ 136 ∧ ex (72426 / 100000) 136 * cCG cZ 136 ≤ (3085705911229 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_136 cCB_136 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_136 : (4791261436301 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 136 * sCG cZ 136 ∧ ex (72426 / 100000) 136 * sCG cZ 136 ≤ (23956317675327 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_136 sCB_136 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_136 : (75794989607921 / 1000000000000000 : ℝ) ≤ Real.log 136 * (ex (72426 / 100000) 136 * cCG cZ 136) ∧ Real.log 136 * (ex (72426 / 100000) 136 * cCG cZ 136) ≤ (75795041128997 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_136 eC_136 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_137 : (196799237015619 / 40000000000000 : ℝ) ≤ Real.log 137 ∧ Real.log 137 ≤ (1229995231866619 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_137
  constructor <;> linarith [h.1, h.2]

theorem eC_137 : (-9369913641963 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 137 * cCG cZ 137 ∧ ex (72426 / 100000) 137 * cCG cZ 137 ≤ (-4684954208681 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_137 cCB_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_137 : (-5323592216553 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 137 * cCG cZ 137) ∧ kappa * (ex (72426 / 100000) 137 * cCG cZ 137) ≤ (-665448656019 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_137 : (10632407851667 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 137 * sCG cZ 137 ∧ ex (72426 / 100000) 137 * sCG cZ 137 ≤ (21264826157469 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_137 sCB_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_137 : (1208177702489 / 200000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 137 * sCG cZ 137) ∧ kappa * (ex (72426 / 100000) 137 * sCG cZ 137) ≤ (6040891482247 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_137 : (-23049898205233 / 250000000000000 : ℝ) ≤ Real.log 137 * (ex (72426 / 100000) 137 * cCG cZ 137) ∧ Real.log 137 * (ex (72426 / 100000) 137 * cCG cZ 137) ≤ (-92199541372153 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_137 eC_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_137 : (-13095986085523 / 500000000000000 : ℝ) ≤ kappa * (Real.log 137 * (ex (72426 / 100000) 137 * cCG cZ 137)) ∧ kappa * (Real.log 137 * (ex (72426 / 100000) 137 * cCG cZ 137)) ≤ (-1047678302221 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_138 : (985450736943911 / 200000000000000 : ℝ) ≤ Real.log 138 ∧ Real.log 138 ≤ (1231813421698889 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_138
  constructor <;> linarith [h.1, h.2]

theorem eC_138 : (-25549127167649 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 138 * cCG cZ 138 ∧ ex (72426 / 100000) 138 * cCG cZ 138 ≤ (-25549116783211 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_138 cCB_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_138 : (-7257971616743 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 138 * cCG cZ 138) ∧ kappa * (ex (72426 / 100000) 138 * cCG cZ 138) ≤ (-7257968666741 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_138 : (-1490580444949 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 138 * sCG cZ 138 ∧ ex (72426 / 100000) 138 * sCG cZ 138 ≤ (-11924633195691 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_138 sCB_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_138 : (-3387541340547 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 138 * sCG cZ 138) ∧ kappa * (ex (72426 / 100000) 138 * sCG cZ 138) ≤ (-3387538396379 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_138 : (-15735878878901 / 125000000000000 : ℝ) ≤ Real.log 138 * (ex (72426 / 100000) 138 * cCG cZ 138) ∧ Real.log 138 * (ex (72426 / 100000) 138 * cCG cZ 138) ≤ (-62943489905703 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_138 eC_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_138 : (-17880933703627 / 500000000000000 : ℝ) ≤ kappa * (Real.log 138 * (ex (72426 / 100000) 138 * cCG cZ 138)) ∧ kappa * (Real.log 138 * (ex (72426 / 100000) 138 * cCG cZ 138)) ≤ (-35761852856781 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_139 : (2467236966346521 / 500000000000000 : ℝ) ≤ Real.log 139 ∧ Real.log 139 ≤ (4934473934769043 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_139
  constructor <;> linarith [h.1, h.2]

theorem eC_139 : (1980845407217 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 139 * cCG cZ 139 ∧ ex (72426 / 100000) 139 * cCG cZ 139 ≤ (1980850555099 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_139 cCB_139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_139 : (-1735418088937 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 139 * sCG cZ 139 ∧ ex (72426 / 100000) 139 * sCG cZ 139 ≤ (-27766679091349 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_139 sCB_139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_139 : (9774430026607 / 500000000000000 : ℝ) ≤ Real.log 139 * (ex (72426 / 100000) 139 * cCG cZ 139) ∧ Real.log 139 * (ex (72426 / 100000) 139 * cCG cZ 139) ≤ (9774455432809 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_139 eC_139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_141 : (2474379944970259 / 500000000000000 : ℝ) ≤ Real.log 141 ∧ Real.log 141 ≤ (4948759892016519 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_141
  constructor <;> linarith [h.1, h.2]

theorem eC_141 : (6353927879697 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 141 * cCG cZ 141 ∧ ex (72426 / 100000) 141 * cCG cZ 141 ≤ (12707865988141 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_141 cCB_141 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_141 : (24679583729191 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 141 * sCG cZ 141 ∧ ex (72426 / 100000) 141 * sCG cZ 141 ≤ (24679593975991 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_141 sCB_141 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_141 : (31444063434619 / 500000000000000 : ℝ) ≤ Real.log 141 * (ex (72426 / 100000) 141 * cCG cZ 141) ∧ Real.log 141 * (ex (72426 / 100000) 141 * cCG cZ 141) ≤ (31444088757617 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_141 eC_141 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_142 : (4955827057163611 / 1000000000000000 : ℝ) ≤ Real.log 142 ∧ Real.log 142 ≤ (1238956764809903 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_142
  constructor <;> linarith [h.1, h.2]

theorem eC_142 : (-19290387016183 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 142 * cCG cZ 142 ∧ ex (72426 / 100000) 142 * cCG cZ 142 ≤ (-4822594213559 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_142 cCB_142 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_142 : (-5479994698869 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 142 * cCG cZ 142) ∧ kappa * (ex (72426 / 100000) 142 * cCG cZ 142) ≤ (-684998976509 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_142 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_142 : (19763722928849 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 142 * sCG cZ 142 ∧ ex (72426 / 100000) 142 * sCG cZ 142 ≤ (4940933273497 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_142 sCB_142 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_142 : (2807229756177 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 142 * sCG cZ 142) ∧ kappa * (ex (72426 / 100000) 142 * sCG cZ 142) ≤ (2807231200029 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_142 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_142 : (-19119964391601 / 200000000000000 : ℝ) ≤ Real.log 142 * (ex (72426 / 100000) 142 * cCG cZ 142) ∧ Real.log 142 * (ex (72426 / 100000) 142 * cCG cZ 142) ≤ (-19119954311421 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_142 eC_142 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_142 : (-3394738251643 / 125000000000000 : ℝ) ≤ kappa * (Real.log 142 * (ex (72426 / 100000) 142 * cCG cZ 142)) ∧ kappa * (Real.log 142 * (ex (72426 / 100000) 142 * cCG cZ 142)) ≤ (-3394736461913 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_142 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_143 : (4962844629822257 / 1000000000000000 : ℝ) ≤ Real.log 143 ∧ Real.log 143 ≤ (2481422315949129 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_143
  constructor <;> linarith [h.1, h.2]

theorem eC_143 : (-24830877499567 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 143 * cCG cZ 143 ∧ ex (72426 / 100000) 143 * cCG cZ 143 ≤ (-12415433684441 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_143 cCB_143 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_143 : (-1763482984449 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 143 * cCG cZ 143) ∧ kappa * (ex (72426 / 100000) 143 * cCG cZ 143) ≤ (-176348226497 / 25000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_143 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_143 : (-5882979405011 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 143 * sCG cZ 143 ∧ ex (72426 / 100000) 143 * sCG cZ 143 ≤ (-5882974349517 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_143 sCB_143 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_143 : (-3342462328617 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 143 * sCG cZ 143) ∧ kappa * (ex (72426 / 100000) 143 * sCG cZ 143) ≤ (-417807432037 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_143 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_143 : (-2464635742081 / 20000000000000 : ℝ) ≤ Real.log 143 * (ex (72426 / 100000) 143 * cCG cZ 143) ∧ Real.log 143 * (ex (72426 / 100000) 143 * cCG cZ 143) ≤ (-30807934193871 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_143 eC_143 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_143 : (-273496626963 / 7812500000000 : ℝ) ≤ kappa * (Real.log 143 * (ex (72426 / 100000) 143 * cCG cZ 143)) ∧ kappa * (Real.log 143 * (ex (72426 / 100000) 143 * cCG cZ 143)) ≤ (-8751888488493 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_143 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_144 : (4969813299138351 / 1000000000000000 : ℝ) ≤ Real.log 144 ∧ Real.log 144 ≤ (4969813301214351 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_144
  constructor <;> linarith [h.1, h.2]

theorem eC_144 : (703343197471 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 144 * cCG cZ 144 ∧ ex (72426 / 100000) 144 * cCG cZ 144 ≤ (703345712153 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_144 cCB_144 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_144 : (-27193972603613 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 144 * sCG cZ 144 ∧ ex (72426 / 100000) 144 * sCG cZ 144 ≤ (-27193962508131 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_144 sCB_144 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_144 : (13981937506599 / 1000000000000000 : ℝ) ≤ Real.log 144 * (ex (72426 / 100000) 144 * cCG cZ 144) ∧ Real.log 144 * (ex (72426 / 100000) 144 * cCG cZ 144) ≤ (13981987502441 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_144 eC_144 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_146 : (4983606621270687 / 1000000000000000 : ℝ) ≤ Real.log 146 ∧ Real.log 146 ≤ (4983606623346687 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_146
  constructor <;> linarith [h.1, h.2]

theorem eC_146 : (15309934793421 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 146 * cCG cZ 146 ∧ ex (72426 / 100000) 146 * cCG cZ 146 ≤ (15309944761921 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_146 cCB_146 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_146 : (5580362699163 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 146 * sCG cZ 146 ∧ ex (72426 / 100000) 146 * sCG cZ 146 ≤ (22321460775843 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_146 sCB_146 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_146 : (15259738481543 / 200000000000000 : ℝ) ≤ Real.log 146 * (ex (72426 / 100000) 146 * cCG cZ 146) ∧ Real.log 146 * (ex (72426 / 100000) 146 * cCG cZ 146) ≤ (38149371059291 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_146 eC_146 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_147 : (2495216293170543 / 500000000000000 : ℝ) ≤ Real.log 147 ∧ Real.log 147 ≤ (4990432588417087 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_147
  constructor <;> linarith [h.1, h.2]

theorem eC_147 : (-15318421630489 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 147 * cCG cZ 147 ∧ ex (72426 / 100000) 147 * cCG cZ 147 ≤ (-3063682344211 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_147 cCB_147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_147 : (-2175821284967 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 147 * cCG cZ 147) ∧ kappa * (ex (72426 / 100000) 147 * cCG cZ 147) ≤ (-4351639754871 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_147 : (443070740021 / 20000000000000 : ℝ) ≤ ex (72426 / 100000) 147 * sCG cZ 147 ∧ ex (72426 / 100000) 147 * sCG cZ 147 ≤ (11076773460459 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_147 sCB_147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_147 : (6293355608941 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 147 * sCG cZ 147) ∧ kappa * (ex (72426 / 100000) 147 * sCG cZ 147) ≤ (6293358426969 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_147 : (-38222775253953 / 500000000000000 : ℝ) ≤ Real.log 147 * (ex (72426 / 100000) 147 * cCG cZ 147) ∧ Real.log 147 * (ex (72426 / 100000) 147 * cCG cZ 147) ≤ (-38222750511871 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_147 eC_147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_147 : (-1085828944707 / 50000000000000 : ℝ) ≤ kappa * (Real.log 147 * (ex (72426 / 100000) 147 * cCG cZ 147)) ∧ kappa * (Real.log 147 * (ex (72426 / 100000) 147 * cCG cZ 147)) ≤ (-868662593469 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_147 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_148 : (999442454665293 / 200000000000000 : ℝ) ≤ Real.log 148 ∧ Real.log 148 ≤ (2498606137701233 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_148
  constructor <;> linarith [h.1, h.2]

theorem eC_148 : (-13041428083241 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 148 * cCG cZ 148 ∧ ex (72426 / 100000) 148 * cCG cZ 148 ≤ (-26082846277277 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_148 cCB_148 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_148 : (-3704796420201 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 148 * cCG cZ 148) ∧ kappa * (ex (72426 / 100000) 148 * cCG cZ 148) ≤ (-1481918006217 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_148 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_148 : (-1233352896633 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 148 * sCG cZ 148 ∧ ex (72426 / 100000) 148 * sCG cZ 148 ≤ (-616675462399 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_148 sCB_148 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_148 : (-1751848557967 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 148 * sCG cZ 148) ∧ kappa * (ex (72426 / 100000) 148 * sCG cZ 148) ≤ (-1751845757181 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_148 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_148 : (-130341569012701 / 1000000000000000 : ℝ) ≤ Real.log 148 * (ex (72426 / 100000) 148 * cCG cZ 148) ∧ Real.log 148 * (ex (72426 / 100000) 148 * cCG cZ 148) ≤ (-1018293121407 / 7812500000000 : ℝ) := by
  exact mul_bounds_of lgB_148 eC_148 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_148 : (-9256827074447 / 250000000000000 : ℝ) ≤ kappa * (Real.log 148 * (ex (72426 / 100000) 148 * cCG cZ 148)) ∧ kappa * (Real.log 148 * (ex (72426 / 100000) 148 * cCG cZ 148)) ≤ (-4628411780457 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_148 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_149 : (5003946305507809 / 1000000000000000 : ℝ) ≤ Real.log 149 ∧ Real.log 149 ≤ (500394630758381 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_149
  constructor <;> linarith [h.1, h.2]

theorem eC_149 : (-987931154137 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 149 * cCG cZ 149 ∧ ex (72426 / 100000) 149 * cCG cZ 149 ≤ (-1975857412427 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_149 cCB_149 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_149 : (-26377173545391 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 149 * sCG cZ 149 ∧ ex (72426 / 100000) 149 * sCG cZ 149 ≤ (-13188581859941 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_149 sCB_149 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_149 : (-4943554450891 / 250000000000000 : ℝ) ≤ Real.log 149 * (ex (72426 / 100000) 149 * cCG cZ 149) ∧ Real.log 149 * (ex (72426 / 100000) 149 * cCG cZ 149) ≤ (-2471771099781 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_149 eC_149 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_151 : (2508639918188637 / 500000000000000 : ℝ) ≤ Real.log 151 ∧ Real.log 151 ≤ (200691193538131 / 40000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_151
  constructor <;> linarith [h.1, h.2]

theorem eC_151 : (21241644976467 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 151 * cCG cZ 151 ∧ ex (72426 / 100000) 151 * cCG cZ 151 ≤ (331900854963 / 15625000000000 : ℝ) := by
  exact mul_bounds_of exB_151 cCB_151 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_151 : (314041883851 / 20000000000000 : ℝ) ≤ ex (72426 / 100000) 151 * sCG cZ 151 ∧ ex (72426 / 100000) 151 * sCG cZ 151 ≤ (1570210392513 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_151 sCB_151 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_151 : (13321909628989 / 125000000000000 : ℝ) ≤ Real.log 151 * (ex (72426 / 100000) 151 * cCG cZ 151) ∧ Real.log 151 * (ex (72426 / 100000) 151 * cCG cZ 151) ≤ (106575325950161 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_151 eC_151 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_152 : (5023880520408627 / 1000000000000000 : ℝ) ≤ Real.log 152 ∧ Real.log 152 ≤ (5023880522484627 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_152
  constructor <;> linarith [h.1, h.2]

theorem eC_152 : (-6047669227579 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 152 * cCG cZ 152 ∧ ex (72426 / 100000) 152 * cCG cZ 152 ≤ (-6047659552853 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_152 cCB_152 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_152 : (-859008045817 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 152 * cCG cZ 152) ∧ kappa * (ex (72426 / 100000) 152 * cCG cZ 152) ≤ (-859006671623 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_152 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_152 : (25584163641903 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 152 * sCG cZ 152 ∧ ex (72426 / 100000) 152 * sCG cZ 152 ≤ (25584173346091 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_152 sCB_152 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_152 : (454245296553 / 62500000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 152 * sCG cZ 152) ∧ kappa * (ex (72426 / 100000) 152 * sCG cZ 152) ≤ (1453585500321 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_152 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_152 : (-1898922977429 / 62500000000000 : ℝ) ≤ Real.log 152 * (ex (72426 / 100000) 152 * cCG cZ 152) ∧ Real.log 152 * (ex (72426 / 100000) 152 * cCG cZ 152) ≤ (-30382719021641 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_152 eC_152 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_152 : (-4315553790037 / 500000000000000 : ℝ) ≤ kappa * (Real.log 152 * (ex (72426 / 100000) 152 * cCG cZ 152)) ∧ kappa * (Real.log 152 * (ex (72426 / 100000) 152 * cCG cZ 152)) ≤ (-8631093768939 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_152 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_153 : (2515218960477393 / 500000000000000 : ℝ) ≤ Real.log 153 ∧ Real.log 153 ≤ (2515218961515393 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_153
  constructor <;> linarith [h.1, h.2]

theorem eC_153 : (-205936962451 / 8000000000000 : ℝ) ≤ ex (72426 / 100000) 153 * cCG cZ 153 ∧ ex (72426 / 100000) 153 * cCG cZ 153 ≤ (-12871055321693 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_153 cCB_153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_153 : (-365639846153 / 50000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 153 * cCG cZ 153) ∧ kappa * (ex (72426 / 100000) 153 * cCG cZ 153) ≤ (-7312794178007 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_153 : (2341676122739 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 153 * sCG cZ 153 ∧ ex (72426 / 100000) 153 * sCG cZ 153 ≤ (4683361876707 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_153 sCB_153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_153 : (1330442227863 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 153 * sCG cZ 153) ∧ kappa * (ex (72426 / 100000) 153 * sCG cZ 153) ≤ (665222481947 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_153 : (-12949413820841 / 100000000000000 : ℝ) ≤ Real.log 153 * (ex (72426 / 100000) 153 * cCG cZ 153) ∧ Real.log 153 * (ex (72426 / 100000) 153 * cCG cZ 153) ≤ (-64747044772951 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_153 eC_153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_153 : (-574790171331 / 15625000000000 : ℝ) ≤ kappa * (Real.log 153 * (ex (72426 / 100000) 153 * cCG cZ 153)) ∧ kappa * (Real.log 153 * (ex (72426 / 100000) 153 * cCG cZ 153)) ≤ (-574789955331 / 15625000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_154 : (5036952601975979 / 1000000000000000 : ℝ) ≤ Real.log 154 ∧ Real.log 154 ≤ (251847630202599 / 50000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_154
  constructor <;> linarith [h.1, h.2]

theorem eC_154 : (-7347791314887 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 154 * cCG cZ 154 ∧ ex (72426 / 100000) 154 * cCG cZ 154 ≤ (-2939114608153 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_154 cCB_154 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_154 : (-10749426615211 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 154 * sCG cZ 154 ∧ ex (72426 / 100000) 154 * sCG cZ 154 ≤ (-67183886347 / 3125000000000 : ℝ) := by
  exact mul_bounds_of exB_154 sCB_154 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_154 : (-37010476597551 / 500000000000000 : ℝ) ≤ Real.log 154 * (ex (72426 / 100000) 154 * cCG cZ 154) ∧ Real.log 154 * (ex (72426 / 100000) 154 * cCG cZ 154) ≤ (-74020904865209 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_154 eC_154 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_156 : (5049856006811887 / 1000000000000000 : ℝ) ≤ Real.log 156 ∧ Real.log 156 ≤ (315616000555493 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_156
  constructor <;> linarith [h.1, h.2]

theorem eC_156 : (25644292078823 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 156 * cCG cZ 156 ∧ ex (72426 / 100000) 156 * cCG cZ 156 ≤ (25644301599787 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_156 cCB_156 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_156 : (2823621365997 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 156 * sCG cZ 156 ∧ ex (72426 / 100000) 156 * sCG cZ 156 ≤ (2823630852539 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_156 sCB_156 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_156 : (64749991197341 / 500000000000000 : ℝ) ≤ Real.log 156 * (ex (72426 / 100000) 156 * cCG cZ 156) ∧ Real.log 156 * (ex (72426 / 100000) 156 * cCG cZ 156) ≤ (64750015263709 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_156 eC_156 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_157 : (2528122902455329 / 500000000000000 : ℝ) ≤ Real.log 157 ∧ Real.log 157 ≤ (5056245806986659 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_157
  constructor <;> linarith [h.1, h.2]

theorem eC_157 : (8370958840331 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 157 * cCG cZ 157 ∧ ex (72426 / 100000) 157 * cCG cZ 157 ≤ (418548414913 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_157 cCB_157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_157 : (594503495847 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 157 * cCG cZ 157) ∧ kappa * (ex (72426 / 100000) 157 * cCG cZ 157) ≤ (2378016670189 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_157 : (4855501345543 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 157 * sCG cZ 157 ∧ ex (72426 / 100000) 157 * sCG cZ 157 ≤ (24277516209639 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_157 sCB_157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_157 : (3448365449019 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 157 * sCG cZ 157) ∧ kappa * (ex (72426 / 100000) 157 * sCG cZ 157) ≤ (1379346718331 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_157 : (42325625519503 / 1000000000000000 : ℝ) ≤ Real.log 157 * (ex (72426 / 100000) 157 * cCG cZ 157) ∧ Real.log 157 * (ex (72426 / 100000) 157 * cCG cZ 157) ≤ (1322677292453 / 31250000000000 : ℝ) := by
  exact mul_bounds_of lgB_157 eC_157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_157 : (12023823227527 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 157 * (ex (72426 / 100000) 157 * cCG cZ 157)) ∧ kappa * (Real.log 157 * (ex (72426 / 100000) 157 * cCG cZ 157)) ≤ (751489801099 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_158 : (5062595032589317 / 1000000000000000 : ℝ) ≤ Real.log 158 ∧ Real.log 158 ≤ (2531297517332659 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_158
  constructor <;> linarith [h.1, h.2]

theorem eC_158 : (-18156254475753 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 158 * cCG cZ 158 ∧ ex (72426 / 100000) 158 * cCG cZ 158 ≤ (-18156245050001 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_158 cCB_158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_158 : (-1289452852799 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 158 * cCG cZ 158) ∧ kappa * (ex (72426 / 100000) 158 * cCG cZ 158) ≤ (-161181522923 / 31250000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_158 : (17993990227081 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 158 * sCG cZ 158 ∧ ex (72426 / 100000) 158 * sCG cZ 158 ≤ (2249249956251 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_158 sCB_158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_158 : (2555857769291 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 158 * sCG cZ 158) ∧ kappa * (ex (72426 / 100000) 158 * sCG cZ 158) ≤ (5111718215439 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_158 : (-22979440939267 / 250000000000000 : ℝ) ≤ Real.log 158 * (ex (72426 / 100000) 158 * cCG cZ 158) ∧ Real.log 158 * (ex (72426 / 100000) 158 * cCG cZ 158) ≤ (-91917716000609 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_158 eC_158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_158 : (-26111910440057 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 158 * (ex (72426 / 100000) 158 * cCG cZ 158)) ∧ kappa * (Real.log 158 * (ex (72426 / 100000) 158 * cCG cZ 158)) ≤ (-26111896873447 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_159 : (2534452100891291 / 500000000000000 : ℝ) ≤ Real.log 159 ∧ Real.log 159 ≤ (2534452101929291 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_159
  constructor <;> linarith [h.1, h.2]

theorem eC_159 : (-6010042436111 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 159 * cCG cZ 159 ∧ ex (72426 / 100000) 159 * cCG cZ 159 ≤ (-3005020044463 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_159 cCB_159 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_159 : (-4170111134121 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 159 * sCG cZ 159 ∧ ex (72426 / 100000) 159 * sCG cZ 159 ≤ (-8340212903187 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_159 sCB_159 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_159 : (-121857317479087 / 1000000000000000 : ℝ) ≤ Real.log 159 * (ex (72426 / 100000) 159 * cCG cZ 159) ∧ Real.log 159 * (ex (72426 / 100000) 159 * cCG cZ 159) ≤ (-24371453967711 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_159 eC_159 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_161 : (5081404364546813 / 1000000000000000 : ℝ) ≤ Real.log 161 ∧ Real.log 161 ≤ (2540702183311407 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_161
  constructor <;> linarith [h.1, h.2]

theorem eC_161 : (10414222587321 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 161 * cCG cZ 161 ∧ ex (72426 / 100000) 161 * cCG cZ 161 ≤ (20828454461739 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_161 cCB_161 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_161 : (-3553573643059 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 161 * sCG cZ 161 ∧ ex (72426 / 100000) 161 * sCG cZ 161 ≤ (-568571411809 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_161 sCB_161 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_161 : (105837752217149 / 1000000000000000 : ℝ) ≤ Real.log 161 * (ex (72426 / 100000) 161 * cCG cZ 161) ∧ Real.log 161 * (ex (72426 / 100000) 161 * cCG cZ 161) ≤ (21167559890377 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_161 eC_161 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_162 : (2543798167397367 / 500000000000000 : ℝ) ≤ Real.log 162 ∧ Real.log 162 ≤ (1017519267374147 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_162
  constructor <;> linarith [h.1, h.2]

theorem eC_162 : (11043481214081 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 162 * cCG cZ 162 ∧ ex (72426 / 100000) 162 * cCG cZ 162 ≤ (2208697167291 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_162 cCB_162 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_162 : (6274443167931 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 162 * cCG cZ 162) ∧ kappa * (ex (72426 / 100000) 162 * cCG cZ 162) ≤ (6274445794171 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_162 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_162 : (1491425456829 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 162 * sCG cZ 162 ∧ ex (72426 / 100000) 162 * sCG cZ 162 ≤ (5965706442023 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_162 sCB_162 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_162 : (3389461741881 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 162 * sCG cZ 162) ∧ kappa * (ex (72426 / 100000) 162 * sCG cZ 162) ≤ (677892872753 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_162 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_162 : (22473909819253 / 200000000000000 : ℝ) ≤ Real.log 162 * (ex (72426 / 100000) 162 * cCG cZ 162) ∧ Real.log 162 * (ex (72426 / 100000) 162 * cCG cZ 162) ≤ (22473919235133 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_162 eC_162 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_162 : (6384366812809 / 200000000000000 : ℝ) ≤ kappa * (Real.log 162 * (ex (72426 / 100000) 162 * cCG cZ 162)) ∧ kappa * (Real.log 162 * (ex (72426 / 100000) 162 * cCG cZ 162)) ≤ (31921847438317 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_162 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_163 : (5093750200369113 / 1000000000000000 : ℝ) ≤ Real.log 163 ∧ Real.log 163 ≤ (5093750202445113 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_163
  constructor <;> linarith [h.1, h.2]

theorem eC_163 : (-74325358351 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 163 * cCG cZ 163 ∧ ex (72426 / 100000) 163 * cCG cZ 163 ≤ (-148646123933 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_163 cCB_163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_163 : (-42228553467 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 163 * cCG cZ 163) ∧ kappa * (ex (72426 / 100000) 163 * cCG cZ 163) ≤ (-42227248757 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_163 : (12495113331673 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 163 * sCG cZ 163 ∧ ex (72426 / 100000) 163 * sCG cZ 163 ≤ (24990235886143 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_163 sCB_163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_163 : (3549599847939 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 163 * sCG cZ 163) ∧ kappa * (ex (72426 / 100000) 163 * sCG cZ 163) ≤ (3549601157941 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_163 : (-1514379236589 / 1000000000000000 : ℝ) ≤ Real.log 163 * (ex (72426 / 100000) 163 * cCG cZ 163) ∧ Real.log 163 * (ex (72426 / 100000) 163 * cCG cZ 163) ≤ (-302866489427 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_163 eC_163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_163 : (-215101702771 / 500000000000000 : ℝ) ≤ kappa * (Real.log 163 * (ex (72426 / 100000) 163 * cCG cZ 163)) ∧ kappa * (Real.log 163 * (ex (72426 / 100000) 163 * cCG cZ 163)) ≤ (-215095056819 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_164 : (5099866427386549 / 1000000000000000 : ℝ) ≤ Real.log 164 ∧ Real.log 164 ≤ (5099866429462549 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_164
  constructor <;> linarith [h.1, h.2]

theorem eC_164 : (-1104552110201 / 50000000000000 : ℝ) ≤ ex (72426 / 100000) 164 * cCG cZ 164 ∧ ex (72426 / 100000) 164 * cCG cZ 164 ≤ (-22091033031387 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_164 cCB_164 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_164 : (5724438994189 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 164 * sCG cZ 164 ∧ ex (72426 / 100000) 164 * sCG cZ 164 ≤ (5724443572473 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_164 sCB_164 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_164 : (-56330682264061 / 500000000000000 : ℝ) ≤ Real.log 164 * (ex (72426 / 100000) 164 * cCG cZ 164) ∧ Real.log 164 * (ex (72426 / 100000) 164 * cCG cZ 164) ≤ (-112661317703057 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_164 eC_164 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_166 : (5111987787918893 / 1000000000000000 : ℝ) ≤ Real.log 166 ∧ Real.log 166 ≤ (2555993894997447 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_166
  constructor <;> linarith [h.1, h.2]

theorem eC_166 : (286090758183 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 166 * cCG cZ 166 ∧ ex (72426 / 100000) 166 * cCG cZ 166 ≤ (286091892167 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_166 cCB_166 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_166 : (-24557639241869 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 166 * sCG cZ 166 ∧ ex (72426 / 100000) 166 * sCG cZ 166 ≤ (-24557630136389 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_166 sCB_166 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_166 : (11699939696543 / 1000000000000000 : ℝ) ≤ Real.log 166 * (ex (72426 / 100000) 166 * cCG cZ 166) ∧ Real.log 166 * (ex (72426 / 100000) 166 * cCG cZ 166) ≤ (5849993038297 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_166 eC_166 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_167 : (1023598762395821 / 200000000000000 : ℝ) ≤ Real.log 167 ∧ Real.log 167 ≤ (2558996907027553 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_167
  constructor <;> linarith [h.1, h.2]

theorem eC_167 : (701773953067 / 31250000000000 : ℝ) ≤ ex (72426 / 100000) 167 * cCG cZ 167 ∧ ex (72426 / 100000) 167 * cCG cZ 167 ≤ (22456775542459 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_167 cCB_167 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_167 : (318974837727 / 50000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 167 * cCG cZ 167) ∧ kappa * (ex (72426 / 100000) 167 * cCG cZ 167) ≤ (6379499323841 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_167 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_167 : (-9936797050423 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 167 * sCG cZ 167 ∧ ex (72426 / 100000) 167 * sCG cZ 167 ≤ (-1987357605001 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_167 sCB_167 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_167 : (-2822835804921 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 167 * sCG cZ 167) ∧ kappa * (ex (72426 / 100000) 167 * sCG cZ 167) ≤ (-705708310247 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_167 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_167 : (718334949841 / 6250000000000 : ℝ) ≤ Real.log 167 * (ex (72426 / 100000) 167 * cCG cZ 167) ∧ Real.log 167 * (ex (72426 / 100000) 167 * cCG cZ 167) ≤ (11493363830993 / 100000000000000 : ℝ) := by
  exact mul_bounds_of lgB_167 eC_167 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_167 : (32650224913277 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 167 * (ex (72426 / 100000) 167 * cCG cZ 167)) ∧ kappa * (Real.log 167 * (ex (72426 / 100000) 167 * cCG cZ 167)) ≤ (6530047615237 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_167 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_168 : (5123963978965609 / 1000000000000000 : ℝ) ≤ Real.log 168 ∧ Real.log 168 ≤ (512396398104161 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_168
  constructor <;> linarith [h.1, h.2]

theorem eC_168 : (9818028914119 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 168 * cCG cZ 168 ∧ ex (72426 / 100000) 168 * cCG cZ 168 ≤ (3927213367163 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_168 cCB_168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_168 : (34863703329 / 6250000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 168 * cCG cZ 168) ∧ kappa * (ex (72426 / 100000) 168 * cCG cZ 168) ≤ (1115639018301 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_168 : (7284894159387 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 168 * sCG cZ 168 ∧ ex (72426 / 100000) 168 * sCG cZ 168 ≤ (14569797318483 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_168 sCB_168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_168 : (2069485767277 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 168 * sCG cZ 168) ∧ kappa * (ex (72426 / 100000) 168 * sCG cZ 168) ≤ (258685880699 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_168 : (100614453000777 / 1000000000000000 : ℝ) ≤ Real.log 168 * (ex (72426 / 100000) 168 * cCG cZ 168) ∧ Real.log 168 * (ex (72426 / 100000) 168 * cCG cZ 168) ≤ (50307249598021 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_168 eC_168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_168 : (14291228802493 / 500000000000000 : ℝ) ≤ kappa * (Real.log 168 * (ex (72426 / 100000) 168 * cCG cZ 168)) ∧ kappa * (Real.log 168 * (ex (72426 / 100000) 168 * cCG cZ 168)) ≤ (14291235364047 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_168 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_169 : (320618669655339 / 62500000000000 : ℝ) ≤ Real.log 169 ∧ Real.log 169 ≤ (320618669785089 / 62500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_169
  constructor <;> linarith [h.1, h.2]

theorem eC_169 : (-564736855087 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 169 * cCG cZ 169 ∧ ex (72426 / 100000) 169 * cCG cZ 169 ≤ (-564735066339 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_169 cCB_169 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_169 : (24181872342211 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 169 * sCG cZ 169 ∧ ex (72426 / 100000) 169 * sCG cZ 169 ≤ (2418188131819 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_169 sCB_169 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_169 : (-14485214340529 / 1000000000000000 : ℝ) ≤ Real.log 169 * (ex (72426 / 100000) 169 * cCG cZ 169) ∧ Real.log 169 * (ex (72426 / 100000) 169 * cCG cZ 169) ≤ (-7242584227093 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_169 eC_169 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_171 : (514166355606501 / 100000000000000 : ℝ) ≤ Real.log 171 ∧ Real.log 171 ≤ (5141663558141011 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_171
  constructor <;> linarith [h.1, h.2]

theorem eC_171 : (-9792953424741 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 171 * cCG cZ 171 ∧ ex (72426 / 100000) 171 * cCG cZ 171 ≤ (-9792948982199 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_171 cCB_171 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_171 : (-2822150171049 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 171 * sCG cZ 171 ∧ ex (72426 / 100000) 171 * sCG cZ 171 ≤ (-7055370989297 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_171 sCB_171 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_171 : (-100704143501127 / 1000000000000000 : ℝ) ≤ Real.log 171 * (ex (72426 / 100000) 171 * cCG cZ 171) ∧ Real.log 171 * (ex (72426 / 100000) 171 * cCG cZ 171) ≤ (-100704097776353 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_171 eC_171 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_172 : (5147494476375803 / 1000000000000000 : ℝ) ≤ Real.log 172 ∧ Real.log 172 ≤ (1286873619612951 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_172
  constructor <;> linarith [h.1, h.2]

theorem eC_172 : (2013540914147 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 172 * cCG cZ 172 ∧ ex (72426 / 100000) 172 * cCG cZ 172 ≤ (1006774872081 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_172 cCB_172 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_172 : (71500597203 / 125000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 172 * cCG cZ 172) ∧ kappa * (ex (72426 / 100000) 172 * cCG cZ 172) ≤ (572007286047 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_172 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_172 : (-2994175421767 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 172 * sCG cZ 172 ∧ ex (72426 / 100000) 172 * sCG cZ 172 ≤ (-23953394510999 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_172 sCB_172 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_172 : (-6804659927249 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 172 * sCG cZ 172) ∧ kappa * (ex (72426 / 100000) 172 * sCG cZ 172) ≤ (-850582176177 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_172 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_172 : (1295586341691 / 125000000000000 : ℝ) ≤ Real.log 172 * (ex (72426 / 100000) 172 * cCG cZ 172) ∧ Real.log 172 * (ex (72426 / 100000) 172 * cCG cZ 172) ≤ (5182368095081 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_172 eC_172 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_172 : (1472195716641 / 500000000000000 : ℝ) ≤ kappa * (Real.log 172 * (ex (72426 / 100000) 172 * cCG cZ 172)) ∧ kappa * (Real.log 172 * (ex (72426 / 100000) 172 * cCG cZ 172)) ≤ (9201263583 / 3125000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_172 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_173 : (5153291594060129 / 1000000000000000 : ℝ) ≤ Real.log 173 ∧ Real.log 173 ≤ (515329159613613 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_173
  constructor <;> linarith [h.1, h.2]

theorem eC_173 : (4284319352079 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 173 * cCG cZ 173 ∧ ex (72426 / 100000) 173 * cCG cZ 173 ≤ (21421605579621 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_173 cCB_173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_173 : (6085426725227 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 173 * cCG cZ 173) ∧ kappa * (ex (72426 / 100000) 173 * cCG cZ 173) ≤ (3042714615293 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_173 : (-534095045669 / 50000000000000 : ℝ) ≤ ex (72426 / 100000) 173 * sCG cZ 173 ∧ ex (72426 / 100000) 173 * sCG cZ 173 ≤ (-10681892110373 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_173 sCB_173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_173 : (-189656512367 / 62500000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 173 * sCG cZ 173) ∧ kappa * (ex (72426 / 100000) 173 * sCG cZ 173) ≤ (-3034501697121 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_173 : (110391734516689 / 1000000000000000 : ℝ) ≤ Real.log 173 * (ex (72426 / 100000) 173 * cCG cZ 173) ∧ Real.log 173 * (ex (72426 / 100000) 173 * cCG cZ 173) ≤ (27597945002301 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_173 eC_173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_173 : (6271995677877 / 200000000000000 : ℝ) ≤ kappa * (Real.log 173 * (ex (72426 / 100000) 173 * cCG cZ 173)) ∧ kappa * (Real.log 173 * (ex (72426 / 100000) 173 * cCG cZ 173)) ≤ (3919998914107 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_174 : (5159055298776879 / 1000000000000000 : ℝ) ≤ Real.log 174 ∧ Real.log 174 ≤ (64488191260661 / 12500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_174
  constructor <;> linarith [h.1, h.2]

theorem eC_174 : (10124113719777 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 174 * cCG cZ 174 ∧ ex (72426 / 100000) 174 * cCG cZ 174 ≤ (2531029528529 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_174 cCB_174 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_174 : (1257907133981 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 174 * sCG cZ 174 ∧ ex (72426 / 100000) 174 * sCG cZ 174 ≤ (3144770029217 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_174 sCB_174 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_174 : (10446172506287 / 100000000000000 : ℝ) ≤ Real.log 174 * (ex (72426 / 100000) 174 * cCG cZ 174) ∧ Real.log 174 * (ex (72426 / 100000) 174 * cCG cZ 174) ≤ (52230885223091 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_174 eC_174 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_176 : (2585241997300251 / 500000000000000 : ℝ) ≤ Real.log 176 ∧ Real.log 176 ≤ (5170483996676503 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_176
  constructor <;> linarith [h.1, h.2]

theorem eC_176 : (-19951417347831 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 176 * cCG cZ 176 ∧ ex (72426 / 100000) 176 * cCG cZ 176 ≤ (-4987852157519 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_176 cCB_176 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_176 : (6341050934239 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 176 * sCG cZ 176 ∧ ex (72426 / 100000) 176 * sCG cZ 176 ≤ (6341055287603 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_176 sCB_176 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_176 : (-4126339364319 / 40000000000000 : ℝ) ≤ Real.log 176 * (ex (72426 / 100000) 176 * cCG cZ 176) ∧ Real.log 176 * (ex (72426 / 100000) 176 * cCG cZ 176) ≤ (-51579219495771 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_176 eC_176 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_177 : (5176149732136179 / 1000000000000000 : ℝ) ≤ Real.log 177 ∧ Real.log 177 ≤ (258807486710609 / 50000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_177
  constructor <;> linarith [h.1, h.2]

theorem eC_177 : (-21352186587773 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 177 * cCG cZ 177 ∧ ex (72426 / 100000) 177 * cCG cZ 177 ≤ (-4270435579897 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_177 cCB_177 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_177 : (-6065708749757 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 177 * cCG cZ 177) ∧ kappa * (ex (72426 / 100000) 177 * cCG cZ 177) ≤ (-1516426570399 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_177 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_177 : (-9920234694849 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 177 * sCG cZ 177 ∧ ex (72426 / 100000) 177 * sCG cZ 177 ≤ (-4960113011913 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_177 sCB_177 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_177 : (-1409065393393 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 177 * sCG cZ 177) ∧ kappa * (ex (72426 / 100000) 177 * sCG cZ 177) ≤ (-2818128323529 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_177 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_177 : (-110522114931151 / 1000000000000000 : ℝ) ≤ Real.log 177 * (ex (72426 / 100000) 177 * cCG cZ 177) ∧ Real.log 177 * (ex (72426 / 100000) 177 * cCG cZ 177) ≤ (-110522069914943 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_177 eC_177 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_177 : (-15698508366431 / 500000000000000 : ℝ) ≤ kappa * (Real.log 177 * (ex (72426 / 100000) 177 * cCG cZ 177)) ∧ kappa * (Real.log 177 * (ex (72426 / 100000) 177 * cCG cZ 177)) ≤ (-313970039447 / 10000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_177 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_178 : (1036356709970887 / 200000000000000 : ℝ) ≤ Real.log 178 ∧ Real.log 178 ≤ (1295445887982609 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_178
  constructor <;> linarith [h.1, h.2]

theorem eC_178 : (-164017928279 / 50000000000000 : ℝ) ≤ ex (72426 / 100000) 178 * cCG cZ 178 ∧ ex (72426 / 100000) 178 * cCG cZ 178 ≤ (-1640174974899 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_178 cCB_178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_178 : (-232970281191 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 178 * cCG cZ 178) ∧ kappa * (ex (72426 / 100000) 178 * cCG cZ 178) ≤ (-2329696693 / 2500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_178 : (-23217683982713 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 178 * sCG cZ 178 ∧ ex (72426 / 100000) 178 * sCG cZ 178 ≤ (-23217675336821 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_178 sCB_178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_178 : (-3297828732999 / 500000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 178 * sCG cZ 178) ∧ kappa * (ex (72426 / 100000) 178 * sCG cZ 178) ≤ (-6595655009881 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_178 : (-16998108059557 / 1000000000000000 : ℝ) ≤ Real.log 178 * (ex (72426 / 100000) 178 * cCG cZ 178) ∧ Real.log 178 * (ex (72426 / 100000) 178 * cCG cZ 178) ≤ (-16998063407629 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_178 eC_178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_178 : (-965761256931 / 200000000000000 : ℝ) ≤ kappa * (Real.log 178 * (ex (72426 / 100000) 178 * cCG cZ 178)) ∧ kappa * (Real.log 178 * (ex (72426 / 100000) 178 * cCG cZ 178)) ≤ (-4828793599977 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_179 : (1037477161080621 / 200000000000000 : ℝ) ≤ Real.log 179 ∧ Real.log 179 ≤ (2593692903739553 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_179
  constructor <;> linarith [h.1, h.2]

theorem eC_179 : (17538328188109 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 179 * cCG cZ 179 ∧ ex (72426 / 100000) 179 * cCG cZ 179 ≤ (3507667356543 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_179 cCB_179 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_179 : (-7710133992087 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 179 * sCG cZ 179 ∧ ex (72426 / 100000) 179 * sCG cZ 179 ≤ (-15420259393679 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_179 sCB_179 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_179 : (90978074693497 / 1000000000000000 : ℝ) ≤ Real.log 179 * (ex (72426 / 100000) 179 * cCG cZ 179) ∧ Real.log 179 * (ex (72426 / 100000) 179 * cCG cZ 179) ≤ (18195623862689 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_179 eC_179 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_181 : (324906064426761 / 62500000000000 : ℝ) ≤ Real.log 181 ∧ Real.log 181 ≤ (5198497032904177 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_181
  constructor <;> linarith [h.1, h.2]

theorem eC_181 : (7476951384783 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 181 * cCG cZ 181 ∧ ex (72426 / 100000) 181 * cCG cZ 181 ≤ (7476959914469 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_181 cCB_181 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_181 : (10963177967339 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 181 * sCG cZ 181 ∧ ex (72426 / 100000) 181 * sCG cZ 181 ≤ (2192636448619 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_181 sCB_181 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_181 : (38868909573441 / 1000000000000000 : ℝ) ≤ Real.log 181 * (ex (72426 / 100000) 181 * cCG cZ 181) ∧ Real.log 181 * (ex (72426 / 100000) 181 * cCG cZ 181) ≤ (38868953930511 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_181 eC_181 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_182 : (2602003343319573 / 500000000000000 : ℝ) ≤ Real.log 182 ∧ Real.log 182 ≤ (2602003344357573 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_182
  constructor <;> linarith [h.1, h.2]

theorem eC_182 : (-346768510633 / 25000000000000 : ℝ) ≤ ex (72426 / 100000) 182 * cCG cZ 182 ∧ ex (72426 / 100000) 182 * cCG cZ 182 ≤ (-3467682984887 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_182 cCB_182 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_182 : (-492548334673 / 125000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 182 * cCG cZ 182) ∧ kappa * (ex (72426 / 100000) 182 * cCG cZ 182) ≤ (-3940384266753 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_182 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_182 : (18439268501841 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 182 * sCG cZ 182 ∧ ex (72426 / 100000) 182 * sCG cZ 182 ≤ (18439276994751 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_182 sCB_182 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_182 : (5238209765119 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 182 * sCG cZ 182) ∧ kappa * (ex (72426 / 100000) 182 * sCG cZ 182) ≤ (2619106088889 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_182 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_182 : (-72183425950797 / 1000000000000000 : ℝ) ≤ Real.log 182 * (ex (72426 / 100000) 182 * cCG cZ 182) ∧ Real.log 182 * (ex (72426 / 100000) 182 * cCG cZ 182) ≤ (-36091690880993 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_182 eC_182 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_182 : (-5126449656307 / 250000000000000 : ℝ) ≤ kappa * (Real.log 182 * (ex (72426 / 100000) 182 * cCG cZ 182)) ∧ kappa * (Real.log 182 * (ex (72426 / 100000) 182 * cCG cZ 182)) ≤ (-1281611629507 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_182 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_183 : (5209486152403771 / 1000000000000000 : ℝ) ≤ Real.log 183 ∧ Real.log 183 ≤ (1302371538619943 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_183
  constructor <;> linarith [h.1, h.2]

theorem eC_183 : (-4592374377549 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 183 * cCG cZ 183 ∧ ex (72426 / 100000) 183 * cCG cZ 183 ≤ (-4592372681801 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_183 cCB_183 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_183 : (-6522986610657 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 183 * cCG cZ 183) ∧ kappa * (ex (72426 / 100000) 183 * cCG cZ 183) ≤ (-815373025253 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_183 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_183 : (-486753771719 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 183 * sCG cZ 183 ∧ ex (72426 / 100000) 183 * sCG cZ 183 ≤ (-973499097913 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_183 sCB_183 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_183 : (-17284568257 / 62500000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 183 * sCG cZ 183) ∧ kappa * (ex (72426 / 100000) 183 * sCG cZ 183) ≤ (-138275346457 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_183 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_183 : (-59809776840073 / 500000000000000 : ℝ) ≤ Real.log 183 * (ex (72426 / 100000) 183 * cCG cZ 183) ∧ Real.log 183 * (ex (72426 / 100000) 183 * cCG cZ 183) ≤ (-59809754731299 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_183 eC_183 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_183 : (-33981408434073 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 183 * (ex (72426 / 100000) 183 * cCG cZ 183)) ∧ kappa * (Real.log 183 * (ex (72426 / 100000) 183 * cCG cZ 183)) ≤ (-33981395872793 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_183 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_184 : (651866969646417 / 125000000000000 : ℝ) ≤ Real.log 184 ∧ Real.log 184 ≤ (651866969905917 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_184
  constructor <;> linarith [h.1, h.2]

theorem eC_184 : (-12265743743787 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 184 * cCG cZ 184 ∧ ex (72426 / 100000) 184 * cCG cZ 184 ≤ (-6132867662717 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_184 cCB_184 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_184 : (-19328574338263 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 184 * sCG cZ 184 ∧ ex (72426 / 100000) 184 * sCG cZ 184 ≤ (-19328565909191 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_184 sCB_184 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_184 : (-1599126641581 / 25000000000000 : ℝ) ≤ Real.log 184 * (ex (72426 / 100000) 184 * cCG cZ 184) ∧ Real.log 184 * (ex (72426 / 100000) 184 * cCG cZ 184) ≤ (-12793004347321 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_184 eC_184 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_186 : (5225746673275551 / 1000000000000000 : ℝ) ≤ Real.log 186 ∧ Real.log 186 ≤ (318954264853 / 61035156250 : ℝ) := by
  have h := PsiOmega.Num.log_bound_186
  constructor <;> linarith [h.1, h.2]

theorem eC_186 : (22136093724129 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 186 * cCG cZ 186 ∧ ex (72426 / 100000) 186 * cCG cZ 186 ≤ (22136102106709 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_186 cCB_186 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_186 : (-508848845993 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 186 * sCG cZ 186 ∧ ex (72426 / 100000) 186 * sCG cZ 186 ≤ (-1272120025777 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_186 sCB_186 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_186 : (57838809069091 / 500000000000000 : ℝ) ≤ Real.log 186 * (ex (72426 / 100000) 186 * cCG cZ 186) ∧ Real.log 186 * (ex (72426 / 100000) 186 * cCG cZ 186) ≤ (57838830994689 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_186 eC_186 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_187 : (5231108616416937 / 1000000000000000 : ℝ) ≤ Real.log 187 ∧ Real.log 187 ≤ (5231108618492937 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_187
  constructor <;> linarith [h.1, h.2]

theorem eC_187 : (2123397291393 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 187 * cCG cZ 187 ∧ ex (72426 / 100000) 187 * cCG cZ 187 ≤ (8493593330731 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_187 cCB_187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_187 : (4825701377857 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 187 * cCG cZ 187) ∧ kappa * (ex (72426 / 100000) 187 * cCG cZ 187) ≤ (4825703744327 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_187 : (1868085582377 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 187 * sCG cZ 187 ∧ ex (72426 / 100000) 187 * sCG cZ 187 ≤ (186808662317 / 12500000000000 : ℝ) := by
  exact mul_bounds_of exB_187 sCB_187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_187 : (4245471728429 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 187 * sCG cZ 187) ∧ kappa * (ex (72426 / 100000) 187 * sCG cZ 187) ≤ (424547409377 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_187 : (44430887468329 / 500000000000000 : ℝ) ≤ Real.log 187 * (ex (72426 / 100000) 187 * cCG cZ 187) ∧ Real.log 187 * (ex (72426 / 100000) 187 * cCG cZ 187) ≤ (88861818548723 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_187 eC_187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_187 : (25243768057967 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 187 * (ex (72426 / 100000) 187 * cCG cZ 187)) ∧ kappa * (Real.log 187 * (ex (72426 / 100000) 187 * cCG cZ 187)) ≤ (12621890223621 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_188 : (5236441962392299 / 1000000000000000 : ℝ) ≤ Real.log 188 ∧ Real.log 188 ≤ (52364419644683 / 10000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_188
  constructor <;> linarith [h.1, h.2]

theorem eC_188 : (-131011047751 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 188 * cCG cZ 188 ∧ ex (72426 / 100000) 188 * cCG cZ 188 ≤ (-2096168485421 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_188 cCB_188 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_188 : (-595479890843 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 188 * cCG cZ 188) ∧ kappa * (ex (72426 / 100000) 188 * cCG cZ 188) ≤ (-297738769533 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_188 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_188 : (897618608691 / 40000000000000 : ℝ) ≤ ex (72426 / 100000) 188 * sCG cZ 188 ∧ ex (72426 / 100000) 188 * sCG cZ 188 ≤ (5610118381653 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_188 sCB_188 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_188 : (6374865902257 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 188 * sCG cZ 188) ∧ kappa * (ex (72426 / 100000) 188 * sCG cZ 188) ≤ (6374868262767 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_188 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_188 : (-10976507972037 / 1000000000000000 : ℝ) ≤ Real.log 188 * (ex (72426 / 100000) 188 * cCG cZ 188) ∧ Real.log 188 * (ex (72426 / 100000) 188 * cCG cZ 188) ≤ (-5488232308651 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_188 eC_188 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_188 : (-3118195889403 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 188 * (ex (72426 / 100000) 188 * cCG cZ 188)) ∧ kappa * (Real.log 188 * (ex (72426 / 100000) 188 * cCG cZ 188)) ≤ (-3118183573231 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_188 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_189 : (5241747014621993 / 1000000000000000 : ℝ) ≤ Real.log 189 ∧ Real.log 189 ≤ (5241747016697993 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_189
  constructor <;> linarith [h.1, h.2]

theorem eC_189 : (-4813567538817 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 189 * cCG cZ 189 ∧ ex (72426 / 100000) 189 * cCG cZ 189 ≤ (-962713094033 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_189 cCB_189 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_189 : (5773933625467 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 189 * sCG cZ 189 ∧ ex (72426 / 100000) 189 * sCG cZ 189 ≤ (2886968878467 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_189 sCB_189 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_189 : (-50463006572537 / 500000000000000 : ℝ) ≤ Real.log 189 * (ex (72426 / 100000) 189 * cCG cZ 189) ∧ Real.log 189 * (ex (72426 / 100000) 189 * cCG cZ 189) ≤ (-100925969731699 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_189 eC_189 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_191 : (262613671380449 / 50000000000000 : ℝ) ≤ Real.log 191 ∧ Real.log 191 ≤ (5252273429684981 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_191
  constructor <;> linarith [h.1, h.2]

theorem eC_191 : (-345869594643 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 191 * cCG cZ 191 ∧ ex (72426 / 100000) 191 * cCG cZ 191 ≤ (-1383476330563 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_191 cCB_191 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_191 : (-1348941057613 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 191 * sCG cZ 191 ∧ ex (72426 / 100000) 191 * sCG cZ 191 ≤ (-4316609741103 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_191 sCB_191 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_191 : (-2906562691327 / 100000000000000 : ℝ) ≤ Real.log 191 * (ex (72426 / 100000) 191 * cCG cZ 191) ∧ Real.log 191 * (ex (72426 / 100000) 191 * cCG cZ 191) ≤ (-3633197984371 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_191 eC_191 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_192 : (1314373842897533 / 250000000000000 : ℝ) ≤ Real.log 192 ∧ Real.log 192 ≤ (1314373843416533 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_192
  constructor <;> linarith [h.1, h.2]

theorem eC_192 : (3453569685539 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 192 * cCG cZ 192 ∧ ex (72426 / 100000) 192 * cCG cZ 192 ≤ (2762857383129 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_192 cCB_192 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_192 : (122635846763 / 31250000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 192 * cCG cZ 192) ∧ kappa * (ex (72426 / 100000) 192 * cCG cZ 192) ≤ (1962174709167 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_192 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_192 : (-2171826027053 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 192 * sCG cZ 192 ∧ ex (72426 / 100000) 192 * sCG cZ 192 ≤ (-8687300018591 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_192 sCB_192 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_192 : (-616970261153 / 125000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 192 * sCG cZ 192) ∧ kappa * (ex (72426 / 100000) 192 * sCG cZ 192) ≤ (-616969970709 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_192 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_192 : (72628506548741 / 1000000000000000 : ℝ) ≤ Real.log 192 * (ex (72426 / 100000) 192 * cCG cZ 192) ∧ Real.log 192 * (ex (72426 / 100000) 192 * cCG cZ 192) ≤ (72628549549501 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_192 eC_192 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_192 : (20632236695923 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 192 * (ex (72426 / 100000) 192 * cCG cZ 192)) ∧ kappa * (Real.log 192 * (ex (72426 / 100000) 192 * cCG cZ 192)) ≤ (20632248911539 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_192 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_193 : (1315672547116809 / 250000000000000 : ℝ) ≤ Real.log 193 ∧ Real.log 193 ≤ (1315672547635809 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_193
  constructor <;> linarith [h.1, h.2]

theorem eC_193 : (11054899592513 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 193 * cCG cZ 193 ∧ ex (72426 / 100000) 193 * cCG cZ 193 ≤ (22109807336603 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_193 cCB_193 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_193 : (1256186122397 / 200000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 193 * cCG cZ 193) ∧ kappa * (ex (72426 / 100000) 193 * cCG cZ 193) ≤ (3140466463839 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_193 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_193 : (41741760917 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 193 * sCG cZ 193 ∧ ex (72426 / 100000) 193 * sCG cZ 193 ≤ (208712863979 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_193 sCB_193 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_193 : (23715919059 / 200000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 193 * sCG cZ 193) ∧ kappa * (ex (72426 / 100000) 193 * sCG cZ 193) ≤ (118581901673 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_193 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_193 : (116357023240017 / 1000000000000000 : ℝ) ≤ Real.log 193 * (ex (72426 / 100000) 193 * cCG cZ 193) ∧ Real.log 193 * (ex (72426 / 100000) 193 * cCG cZ 193) ≤ (58178533092571 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_193 eC_193 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_193 : (1652729595307 / 50000000000000 : ℝ) ≤ kappa * (Real.log 193 * (ex (72426 / 100000) 193 * cCG cZ 193)) ∧ kappa * (Real.log 193 * (ex (72426 / 100000) 193 * cCG cZ 193)) ≤ (33054604105951 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_193 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_194 : (2633929079312839 / 500000000000000 : ℝ) ≤ Real.log 194 ∧ Real.log 194 ≤ (5267858160701679 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_194
  constructor <;> linarith [h.1, h.2]

theorem eC_194 : (6567180949053 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 194 * cCG cZ 194 ∧ ex (72426 / 100000) 194 * cCG cZ 194 ≤ (13134370011689 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_194 cCB_194 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_194 : (17687816573153 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 194 * sCG cZ 194 ∧ ex (72426 / 100000) 194 * sCG cZ 194 ≤ (8843912346911 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_194 sCB_194 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_194 : (69189955483279 / 1000000000000000 : ℝ) ≤ Real.log 194 * (ex (72426 / 100000) 194 * cCG cZ 194) ∧ Real.log 194 * (ex (72426 / 100000) 194 * cCG cZ 194) ≤ (8648749781469 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_194 eC_194 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_196 : (5278114658792867 / 1000000000000000 : ℝ) ≤ Real.log 196 ∧ Real.log 196 ≤ (1319528665217217 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_196
  constructor <;> linarith [h.1, h.2]

theorem eC_196 : (-315091044063 / 15625000000000 : ℝ) ≤ ex (72426 / 100000) 196 * cCG cZ 196 ∧ ex (72426 / 100000) 196 * cCG cZ 196 ≤ (-2520727345899 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_196 cCB_196 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_196 : (338354525881 / 40000000000000 : ℝ) ≤ ex (72426 / 100000) 196 * sCG cZ 196 ∧ ex (72426 / 100000) 196 * sCG cZ 196 ≤ (1691774236433 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_196 sCB_196 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_196 : (-53218773093677 / 500000000000000 : ℝ) ≤ Real.log 196 * (ex (72426 / 100000) 196 * cCG cZ 196) ∧ Real.log 196 * (ex (72426 / 100000) 196 * cCG cZ 196) ≤ (-26609375910419 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_196 eC_196 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_197 : (5283203728300339 / 1000000000000000 : ℝ) ≤ Real.log 197 ∧ Real.log 197 ≤ (5283203730376339 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_197
  constructor <;> linarith [h.1, h.2]

theorem eC_197 : (-19098701464973 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 197 * cCG cZ 197 ∧ ex (72426 / 100000) 197 * cCG cZ 197 ≤ (-596834169991 / 31250000000000 : ℝ) := by
  exact mul_bounds_of exB_197 cCB_197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_197 : (-1356385212691 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 197 * cCG cZ 197) ∧ kappa * (ex (72426 / 100000) 197 * cCG cZ 197) ≤ (-2712769285477 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_197 : (-10485248723041 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 197 * sCG cZ 197 ∧ ex (72426 / 100000) 197 * sCG cZ 197 ≤ (-5242620355407 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_197 sCB_197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_197 : (-2978639431671 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 197 * sCG cZ 197) ∧ kappa * (ex (72426 / 100000) 197 * sCG cZ 197) ≤ (-744659288891 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_197 : (-10090233082509 / 100000000000000 : ℝ) ≤ Real.log 197 * (ex (72426 / 100000) 197 * cCG cZ 197) ∧ Real.log 197 * (ex (72426 / 100000) 197 * cCG cZ 197) ≤ (-100902288386351 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_197 eC_197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_197 : (-28664237662061 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 197 * (ex (72426 / 100000) 197 * cCG cZ 197)) ∧ kappa * (Real.log 197 * (ex (72426 / 100000) 197 * cCG cZ 197)) ≤ (-3583028200763 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_198 : (1057653406051377 / 200000000000000 : ℝ) ≤ Real.log 198 ∧ Real.log 198 ≤ (2644133516166443 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_198
  constructor <;> linarith [h.1, h.2]

theorem eC_198 : (-1879294714147 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 198 * cCG cZ 198 ∧ ex (72426 / 100000) 198 * cCG cZ 198 ≤ (-1879290724061 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_198 cCB_198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_198 : (-1067736490979 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 198 * cCG cZ 198) ∧ kappa * (ex (72426 / 100000) 198 * cCG cZ 198) ≤ (-533867111989 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_198 : (-21380012870853 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 198 * sCG cZ 198 ∧ ex (72426 / 100000) 198 * sCG cZ 198 ≤ (-21380004864037 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_198 sCB_198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_198 : (-379600850853 / 62500000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 198 * sCG cZ 198) ∧ kappa * (ex (72426 / 100000) 198 * sCG cZ 198) ≤ (-3036805669539 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_198 : (-19876424561723 / 1000000000000000 : ℝ) ≤ Real.log 198 * (ex (72426 / 100000) 198 * cCG cZ 198) ∧ Real.log 198 * (ex (72426 / 100000) 198 * cCG cZ 198) ≤ (-9938191176319 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_198 eC_198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_198 : (-5646475684461 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 198 * (ex (72426 / 100000) 198 * cCG cZ 198)) ∧ kappa * (Real.log 198 * (ex (72426 / 100000) 198 * cCG cZ 198)) ≤ (-5646463693743 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_199 : (5293304824286843 / 1000000000000000 : ℝ) ≤ Real.log 199 ∧ Real.log 199 ≤ (5293304826362843 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_199
  constructor <;> linarith [h.1, h.2]

theorem eC_199 : (354982898879 / 25000000000000 : ℝ) ≤ ex (72426 / 100000) 199 * cCG cZ 199 ∧ ex (72426 / 100000) 199 * cCG cZ 199 ≤ (3549830979809 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_199 cCB_199 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_199 : (-16315175835719 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 199 * sCG cZ 199 ∧ ex (72426 / 100000) 199 * sCG cZ 199 ≤ (-16315167867667 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_199 sCB_199 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_199 : (75161307647021 / 1000000000000000 : ℝ) ≤ Real.log 199 * (ex (72426 / 100000) 199 * cCG cZ 199) ∧ Real.log 199 * (ex (72426 / 100000) 199 * cCG cZ 199) ≤ (37580674916391 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_199 eC_199 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_201 : (2651652453810713 / 500000000000000 : ℝ) ≤ Real.log 201 ∧ Real.log 201 ≤ (5303304909697427 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_201
  constructor <;> linarith [h.1, h.2]

theorem eC_201 : (3284462726873 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 201 * cCG cZ 201 ∧ ex (72426 / 100000) 201 * cCG cZ 201 ≤ (13137858819657 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_201 cCB_201 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_201 : (8492271247621 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 201 * sCG cZ 201 ∧ ex (72426 / 100000) 201 * sCG cZ 201 ≤ (16984550413507 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_201 sCB_201 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_201 : (696740291933 / 10000000000000 : ℝ) ≤ Real.log 201 * (ex (72426 / 100000) 201 * cCG cZ 201) ∧ Real.log 201 * (ex (72426 / 100000) 201 * cCG cZ 201) ≤ (69674071181199 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_201 eC_201 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_202 : (1061653539392711 / 200000000000000 : ℝ) ≤ Real.log 202 ∧ Real.log 202 ≤ (1327066924759889 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_202
  constructor <;> linarith [h.1, h.2]

theorem eC_202 : (-4638968210373 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 202 * cCG cZ 202 ∧ ex (72426 / 100000) 202 * cCG cZ 202 ≤ (-927792069727 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_202 cCB_202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_202 : (-1317833653609 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 202 * cCG cZ 202) ∧ kappa * (ex (72426 / 100000) 202 * cCG cZ 202) ≤ (-1317831420253 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_202 : (20886723724543 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 202 * sCG cZ 202 ∧ ex (72426 / 100000) 202 * sCG cZ 202 ≤ (2610841451357 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_202 sCB_202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_202 : (5933480504627 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 202 * sCG cZ 202) ∧ kappa * (ex (72426 / 100000) 202 * sCG cZ 202) ≤ (1483370686241 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_202 : (-4924977021599 / 200000000000000 : ℝ) ≤ Real.log 202 * (ex (72426 / 100000) 202 * cCG cZ 202) ∧ Real.log 202 * (ex (72426 / 100000) 202 * cCG cZ 202) ≤ (-24624843366153 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_202 eC_202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_202 : (-43721336351 / 6250000000000 : ℝ) ≤ kappa * (Real.log 202 * (ex (72426 / 100000) 202 * cCG cZ 202)) ∧ kappa * (Real.log 202 * (ex (72426 / 100000) 202 * cCG cZ 202)) ≤ (-218606311193 / 31250000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_203 : (2656602989302069 / 500000000000000 : ℝ) ≤ Real.log 203 ∧ Real.log 203 ≤ (2656602990340069 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_203
  constructor <;> linarith [h.1, h.2]

theorem eC_203 : (-591052900581 / 31250000000000 : ℝ) ≤ ex (72426 / 100000) 203 * cCG cZ 203 ∧ ex (72426 / 100000) 203 * cCG cZ 203 ≤ (-1891368496389 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_203 cCB_203 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_203 : (-5372983771397 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 203 * cCG cZ 203) ∧ kappa * (ex (72426 / 100000) 203 * cCG cZ 203) ≤ (-134324538501 / 25000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eC_203 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_203 : (2459481688423 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 203 * sCG cZ 203 ∧ ex (72426 / 100000) 203 * sCG cZ 203 ≤ (9837934594659 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_203 sCB_203 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_203 : (69868720639 / 25000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 203 * sCG cZ 203) ∧ kappa * (ex (72426 / 100000) 203 * sCG cZ 203) ≤ (349343881627 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG eS_203 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_203 : (-10049234580049 / 100000000000000 : ℝ) ≤ Real.log 203 * (ex (72426 / 100000) 203 * cCG cZ 203) ∧ Real.log 203 * (ex (72426 / 100000) 203 * cCG cZ 203) ≤ (-4019692161103 / 40000000000000 : ℝ) := by
  exact mul_bounds_of lgB_203 eC_203 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_203 : (-7136942377071 / 250000000000000 : ℝ) ≤ kappa * (Real.log 203 * (ex (72426 / 100000) 203 * cCG cZ 203)) ∧ kappa * (Real.log 203 * (ex (72426 / 100000) 203 * cCG cZ 203)) ≤ (-28547757641473 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaBG leC_203 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_204 : (5318119993406567 / 1000000000000000 : ℝ) ≤ Real.log 204 ∧ Real.log 204 ≤ (5318119995482567 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_204
  constructor <;> linarith [h.1, h.2]

theorem eC_204 : (-19658989542969 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 204 * cCG cZ 204 ∧ ex (72426 / 100000) 204 * cCG cZ 204 ≤ (-122868635701 / 6250000000000 : ℝ) := by
  exact mul_bounds_of exB_204 cCB_204 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_204 : (-4025329156841 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 204 * sCG cZ 204 ∧ ex (72426 / 100000) 204 * sCG cZ 204 ≤ (-8050650500433 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_204 sCB_204 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_204 : (-104548865379447 / 1000000000000000 : ℝ) ≤ Real.log 204 * (ex (72426 / 100000) 204 * cCG cZ 204) ∧ Real.log 204 * (ex (72426 / 100000) 204 * cCG cZ 204) ≤ (-26137205923363 / 250000000000000 : ℝ) := by
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

theorem PReB_0 : (180542429301499 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 1 * cCG cZ 1 + kappa * (ex (72426 / 100000) 2 * cCG cZ 2) - kappa * (ex (72426 / 100000) 3 * cCG cZ 3) - ex (72426 / 100000) 4 * cCG cZ 4 ∧ ex (72426 / 100000) 1 * cCG cZ 1 + kappa * (ex (72426 / 100000) 2 * cCG cZ 2) - kappa * (ex (72426 / 100000) 3 * cCG cZ 3) - ex (72426 / 100000) 4 * cCG cZ 4 ≤ (361084890097883 / 1000000000000000 : ℝ) := by
  have h0 : ex (72426 / 100000) 1 * cCG cZ 1 = (1 : ℝ) := by rw [ex_oneG, cCG_one]; norm_num
  have h1 := keC_2
  have h2 := keC_3
  have h3 := eC_4
  constructor <;> linarith [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_1 : (-42512679528627 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 6 * cCG cZ 6 + kappa * (ex (72426 / 100000) 7 * cCG cZ 7) - kappa * (ex (72426 / 100000) 8 * cCG cZ 8) - ex (72426 / 100000) 9 * cCG cZ 9 ∧ ex (72426 / 100000) 6 * cCG cZ 6 + kappa * (ex (72426 / 100000) 7 * cCG cZ 7) - kappa * (ex (72426 / 100000) 8 * cCG cZ 8) - ex (72426 / 100000) 9 * cCG cZ 9 ≤ (-212563355362027 / 1000000000000000 : ℝ) := by
  have h0 := eC_6
  have h1 := keC_7
  have h2 := keC_8
  have h3 := eC_9
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_2 : (-92946240053437 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 11 * cCG cZ 11 + kappa * (ex (72426 / 100000) 12 * cCG cZ 12) - kappa * (ex (72426 / 100000) 13 * cCG cZ 13) - ex (72426 / 100000) 14 * cCG cZ 14 ∧ ex (72426 / 100000) 11 * cCG cZ 11 + kappa * (ex (72426 / 100000) 12 * cCG cZ 12) - kappa * (ex (72426 / 100000) 13 * cCG cZ 13) - ex (72426 / 100000) 14 * cCG cZ 14 ≤ (-92946223736529 / 500000000000000 : ℝ) := by
  have h0 := eC_11
  have h1 := keC_12
  have h2 := keC_13
  have h3 := eC_14
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_3 : (83165422461543 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 16 * cCG cZ 16 + kappa * (ex (72426 / 100000) 17 * cCG cZ 17) - kappa * (ex (72426 / 100000) 18 * cCG cZ 18) - ex (72426 / 100000) 19 * cCG cZ 19 ∧ ex (72426 / 100000) 16 * cCG cZ 16 + kappa * (ex (72426 / 100000) 17 * cCG cZ 17) - kappa * (ex (72426 / 100000) 18 * cCG cZ 18) - ex (72426 / 100000) 19 * cCG cZ 19 ≤ (4158272755301 / 50000000000000 : ℝ) := by
  have h0 := eC_16
  have h1 := keC_17
  have h2 := keC_18
  have h3 := eC_19
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_4 : (6588600182127 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 21 * cCG cZ 21 + kappa * (ex (72426 / 100000) 22 * cCG cZ 22) - kappa * (ex (72426 / 100000) 23 * cCG cZ 23) - ex (72426 / 100000) 24 * cCG cZ 24 ∧ ex (72426 / 100000) 21 * cCG cZ 21 + kappa * (ex (72426 / 100000) 22 * cCG cZ 22) - kappa * (ex (72426 / 100000) 23 * cCG cZ 23) - ex (72426 / 100000) 24 * cCG cZ 24 ≤ (1317726254331 / 200000000000000 : ℝ) := by
  have h0 := eC_21
  have h1 := keC_22
  have h2 := keC_23
  have h3 := eC_24
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_5 : (-20860012265757 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 26 * cCG cZ 26 + kappa * (ex (72426 / 100000) 27 * cCG cZ 27) - kappa * (ex (72426 / 100000) 28 * cCG cZ 28) - ex (72426 / 100000) 29 * cCG cZ 29 ∧ ex (72426 / 100000) 26 * cCG cZ 26 + kappa * (ex (72426 / 100000) 27 * cCG cZ 27) - kappa * (ex (72426 / 100000) 28 * cCG cZ 28) - ex (72426 / 100000) 29 * cCG cZ 29 ≤ (-20859998536299 / 500000000000000 : ℝ) := by
  have h0 := eC_26
  have h1 := keC_27
  have h2 := keC_28
  have h3 := eC_29
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_6 : (-7639866083391 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 31 * cCG cZ 31 + kappa * (ex (72426 / 100000) 32 * cCG cZ 32) - kappa * (ex (72426 / 100000) 33 * cCG cZ 33) - ex (72426 / 100000) 34 * cCG cZ 34 ∧ ex (72426 / 100000) 31 * cCG cZ 31 + kappa * (ex (72426 / 100000) 32 * cCG cZ 32) - kappa * (ex (72426 / 100000) 33 * cCG cZ 33) - ex (72426 / 100000) 34 * cCG cZ 34 ≤ (-122237832757369 / 1000000000000000 : ℝ) := by
  have h0 := eC_31
  have h1 := keC_32
  have h2 := keC_33
  have h3 := eC_34
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_7 : (-68789596072991 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 36 * cCG cZ 36 + kappa * (ex (72426 / 100000) 37 * cCG cZ 37) - kappa * (ex (72426 / 100000) 38 * cCG cZ 38) - ex (72426 / 100000) 39 * cCG cZ 39 ∧ ex (72426 / 100000) 36 * cCG cZ 36 + kappa * (ex (72426 / 100000) 37 * cCG cZ 37) - kappa * (ex (72426 / 100000) 38 * cCG cZ 38) - ex (72426 / 100000) 39 * cCG cZ 39 ≤ (-68789573976157 / 1000000000000000 : ℝ) := by
  have h0 := eC_36
  have h1 := keC_37
  have h2 := keC_38
  have h3 := eC_39
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_8 : (2805137198299 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 41 * cCG cZ 41 + kappa * (ex (72426 / 100000) 42 * cCG cZ 42) - kappa * (ex (72426 / 100000) 43 * cCG cZ 43) - ex (72426 / 100000) 44 * cCG cZ 44 ∧ ex (72426 / 100000) 41 * cCG cZ 41 + kappa * (ex (72426 / 100000) 42 * cCG cZ 42) - kappa * (ex (72426 / 100000) 43 * cCG cZ 43) - ex (72426 / 100000) 44 * cCG cZ 44 ≤ (2805147320423 / 500000000000000 : ℝ) := by
  have h0 := eC_41
  have h1 := keC_42
  have h2 := keC_43
  have h3 := eC_44
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_9 : (1290461632593 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 46 * cCG cZ 46 + kappa * (ex (72426 / 100000) 47 * cCG cZ 47) - kappa * (ex (72426 / 100000) 48 * cCG cZ 48) - ex (72426 / 100000) 49 * cCG cZ 49 ∧ ex (72426 / 100000) 46 * cCG cZ 46 + kappa * (ex (72426 / 100000) 47 * cCG cZ 47) - kappa * (ex (72426 / 100000) 48 * cCG cZ 48) - ex (72426 / 100000) 49 * cCG cZ 49 ≤ (806539689451 / 62500000000000 : ℝ) := by
  have h0 := eC_46
  have h1 := keC_47
  have h2 := keC_48
  have h3 := eC_49
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_10 : (-53943007186497 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 51 * cCG cZ 51 + kappa * (ex (72426 / 100000) 52 * cCG cZ 52) - kappa * (ex (72426 / 100000) 53 * cCG cZ 53) - ex (72426 / 100000) 54 * cCG cZ 54 ∧ ex (72426 / 100000) 51 * cCG cZ 51 + kappa * (ex (72426 / 100000) 52 * cCG cZ 52) - kappa * (ex (72426 / 100000) 53 * cCG cZ 53) - ex (72426 / 100000) 54 * cCG cZ 54 ≤ (-1078859796119 / 20000000000000 : ℝ) := by
  have h0 := eC_51
  have h1 := keC_52
  have h2 := keC_53
  have h3 := eC_54
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_11 : (7395600499117 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 56 * cCG cZ 56 + kappa * (ex (72426 / 100000) 57 * cCG cZ 57) - kappa * (ex (72426 / 100000) 58 * cCG cZ 58) - ex (72426 / 100000) 59 * cCG cZ 59 ∧ ex (72426 / 100000) 56 * cCG cZ 56 + kappa * (ex (72426 / 100000) 57 * cCG cZ 57) - kappa * (ex (72426 / 100000) 58 * cCG cZ 58) - ex (72426 / 100000) 59 * cCG cZ 59 ≤ (29582420252317 / 1000000000000000 : ℝ) := by
  have h0 := eC_56
  have h1 := keC_57
  have h2 := keC_58
  have h3 := eC_59
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_12 : (-59774568277153 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 61 * cCG cZ 61 + kappa * (ex (72426 / 100000) 62 * cCG cZ 62) - kappa * (ex (72426 / 100000) 63 * cCG cZ 63) - ex (72426 / 100000) 64 * cCG cZ 64 ∧ ex (72426 / 100000) 61 * cCG cZ 61 + kappa * (ex (72426 / 100000) 62 * cCG cZ 62) - kappa * (ex (72426 / 100000) 63 * cCG cZ 63) - ex (72426 / 100000) 64 * cCG cZ 64 ≤ (-5977454271573 / 100000000000000 : ℝ) := by
  have h0 := eC_61
  have h1 := keC_62
  have h2 := keC_63
  have h3 := eC_64
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_13 : (-6198672861041 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 66 * cCG cZ 66 + kappa * (ex (72426 / 100000) 67 * cCG cZ 67) - kappa * (ex (72426 / 100000) 68 * cCG cZ 68) - ex (72426 / 100000) 69 * cCG cZ 69 ∧ ex (72426 / 100000) 66 * cCG cZ 66 + kappa * (ex (72426 / 100000) 67 * cCG cZ 67) - kappa * (ex (72426 / 100000) 68 * cCG cZ 68) - ex (72426 / 100000) 69 * cCG cZ 69 ≤ (-12397315658759 / 1000000000000000 : ℝ) := by
  have h0 := eC_66
  have h1 := keC_67
  have h2 := keC_68
  have h3 := eC_69
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_14 : (-28392934477 / 6250000000000 : ℝ) ≤ ex (72426 / 100000) 71 * cCG cZ 71 + kappa * (ex (72426 / 100000) 72 * cCG cZ 72) - kappa * (ex (72426 / 100000) 73 * cCG cZ 73) - ex (72426 / 100000) 74 * cCG cZ 74 ∧ ex (72426 / 100000) 71 * cCG cZ 71 + kappa * (ex (72426 / 100000) 72 * cCG cZ 72) - kappa * (ex (72426 / 100000) 73 * cCG cZ 73) - ex (72426 / 100000) 74 * cCG cZ 74 ≤ (-1135709275933 / 250000000000000 : ℝ) := by
  have h0 := eC_71
  have h1 := keC_72
  have h2 := keC_73
  have h3 := eC_74
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_15 : (-1024643848357 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 76 * cCG cZ 76 + kappa * (ex (72426 / 100000) 77 * cCG cZ 77) - kappa * (ex (72426 / 100000) 78 * cCG cZ 78) - ex (72426 / 100000) 79 * cCG cZ 79 ∧ ex (72426 / 100000) 76 * cCG cZ 76 + kappa * (ex (72426 / 100000) 77 * cCG cZ 77) - kappa * (ex (72426 / 100000) 78 * cCG cZ 78) - ex (72426 / 100000) 79 * cCG cZ 79 ≤ (-256152596641 / 250000000000000 : ℝ) := by
  have h0 := eC_76
  have h1 := keC_77
  have h2 := keC_78
  have h3 := eC_79
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_16 : (790416932613 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 81 * cCG cZ 81 + kappa * (ex (72426 / 100000) 82 * cCG cZ 82) - kappa * (ex (72426 / 100000) 83 * cCG cZ 83) - ex (72426 / 100000) 84 * cCG cZ 84 ∧ ex (72426 / 100000) 81 * cCG cZ 81 + kappa * (ex (72426 / 100000) 82 * cCG cZ 82) - kappa * (ex (72426 / 100000) 83 * cCG cZ 83) - ex (72426 / 100000) 84 * cCG cZ 84 ≤ (790420313491 / 100000000000000 : ℝ) := by
  have h0 := eC_81
  have h1 := keC_82
  have h2 := keC_83
  have h3 := eC_84
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_17 : (-13820348193517 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 86 * cCG cZ 86 + kappa * (ex (72426 / 100000) 87 * cCG cZ 87) - kappa * (ex (72426 / 100000) 88 * cCG cZ 88) - ex (72426 / 100000) 89 * cCG cZ 89 ∧ ex (72426 / 100000) 86 * cCG cZ 86 + kappa * (ex (72426 / 100000) 87 * cCG cZ 87) - kappa * (ex (72426 / 100000) 88 * cCG cZ 88) - ex (72426 / 100000) 89 * cCG cZ 89 ≤ (-172754142501 / 6250000000000 : ℝ) := by
  have h0 := eC_86
  have h1 := keC_87
  have h2 := keC_88
  have h3 := eC_89
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_18 : (35018205727521 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 91 * cCG cZ 91 + kappa * (ex (72426 / 100000) 92 * cCG cZ 92) - kappa * (ex (72426 / 100000) 93 * cCG cZ 93) - ex (72426 / 100000) 94 * cCG cZ 94 ∧ ex (72426 / 100000) 91 * cCG cZ 91 + kappa * (ex (72426 / 100000) 92 * cCG cZ 92) - kappa * (ex (72426 / 100000) 93 * cCG cZ 93) - ex (72426 / 100000) 94 * cCG cZ 94 ≤ (1400729557387 / 40000000000000 : ℝ) := by
  have h0 := eC_91
  have h1 := keC_92
  have h2 := keC_93
  have h3 := eC_94
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_19 : (-11042354169901 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 96 * cCG cZ 96 + kappa * (ex (72426 / 100000) 97 * cCG cZ 97) - kappa * (ex (72426 / 100000) 98 * cCG cZ 98) - ex (72426 / 100000) 99 * cCG cZ 99 ∧ ex (72426 / 100000) 96 * cCG cZ 96 + kappa * (ex (72426 / 100000) 97 * cCG cZ 97) - kappa * (ex (72426 / 100000) 98 * cCG cZ 98) - ex (72426 / 100000) 99 * cCG cZ 99 ≤ (-5521173008853 / 125000000000000 : ℝ) := by
  have h0 := eC_96
  have h1 := keC_97
  have h2 := keC_98
  have h3 := eC_99
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_20 : (49620809933593 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 101 * cCG cZ 101 + kappa * (ex (72426 / 100000) 102 * cCG cZ 102) - kappa * (ex (72426 / 100000) 103 * cCG cZ 103) - ex (72426 / 100000) 104 * cCG cZ 104 ∧ ex (72426 / 100000) 101 * cCG cZ 101 + kappa * (ex (72426 / 100000) 102 * cCG cZ 102) - kappa * (ex (72426 / 100000) 103 * cCG cZ 103) - ex (72426 / 100000) 104 * cCG cZ 104 ≤ (49620841900831 / 1000000000000000 : ℝ) := by
  have h0 := eC_101
  have h1 := keC_102
  have h2 := keC_103
  have h3 := eC_104
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_21 : (-2931232541337 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 106 * cCG cZ 106 + kappa * (ex (72426 / 100000) 107 * cCG cZ 107) - kappa * (ex (72426 / 100000) 108 * cCG cZ 108) - ex (72426 / 100000) 109 * cCG cZ 109 ∧ ex (72426 / 100000) 106 * cCG cZ 106 + kappa * (ex (72426 / 100000) 107 * cCG cZ 107) - kappa * (ex (72426 / 100000) 108 * cCG cZ 108) - ex (72426 / 100000) 109 * cCG cZ 109 ≤ (-14656131436601 / 1000000000000000 : ℝ) := by
  have h0 := eC_106
  have h1 := keC_107
  have h2 := keC_108
  have h3 := eC_109
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_22 : (-26791942892023 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 111 * cCG cZ 111 + kappa * (ex (72426 / 100000) 112 * cCG cZ 112) - kappa * (ex (72426 / 100000) 113 * cCG cZ 113) - ex (72426 / 100000) 114 * cCG cZ 114 ∧ ex (72426 / 100000) 111 * cCG cZ 111 + kappa * (ex (72426 / 100000) 112 * cCG cZ 112) - kappa * (ex (72426 / 100000) 113 * cCG cZ 113) - ex (72426 / 100000) 114 * cCG cZ 114 ≤ (-53583855222021 / 1000000000000000 : ℝ) := by
  have h0 := eC_111
  have h1 := keC_112
  have h2 := keC_113
  have h3 := eC_114
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_23 : (2099862780297 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 116 * cCG cZ 116 + kappa * (ex (72426 / 100000) 117 * cCG cZ 117) - kappa * (ex (72426 / 100000) 118 * cCG cZ 118) - ex (72426 / 100000) 119 * cCG cZ 119 ∧ ex (72426 / 100000) 116 * cCG cZ 116 + kappa * (ex (72426 / 100000) 117 * cCG cZ 117) - kappa * (ex (72426 / 100000) 118 * cCG cZ 118) - ex (72426 / 100000) 119 * cCG cZ 119 ≤ (3359786416051 / 200000000000000 : ℝ) := by
  have h0 := eC_116
  have h1 := keC_117
  have h2 := keC_118
  have h3 := eC_119
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_24 : (3820204212859 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 121 * cCG cZ 121 + kappa * (ex (72426 / 100000) 122 * cCG cZ 122) - kappa * (ex (72426 / 100000) 123 * cCG cZ 123) - ex (72426 / 100000) 124 * cCG cZ 124 ∧ ex (72426 / 100000) 121 * cCG cZ 121 + kappa * (ex (72426 / 100000) 122 * cCG cZ 122) - kappa * (ex (72426 / 100000) 123 * cCG cZ 123) - ex (72426 / 100000) 124 * cCG cZ 124 ≤ (61123296497833 / 1000000000000000 : ℝ) := by
  have h0 := eC_121
  have h1 := keC_122
  have h2 := keC_123
  have h3 := eC_124
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_25 : (52831067019611 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 126 * cCG cZ 126 + kappa * (ex (72426 / 100000) 127 * cCG cZ 127) - kappa * (ex (72426 / 100000) 128 * cCG cZ 128) - ex (72426 / 100000) 129 * cCG cZ 129 ∧ ex (72426 / 100000) 126 * cCG cZ 126 + kappa * (ex (72426 / 100000) 127 * cCG cZ 127) - kappa * (ex (72426 / 100000) 128 * cCG cZ 128) - ex (72426 / 100000) 129 * cCG cZ 129 ≤ (5283109529593 / 100000000000000 : ℝ) := by
  have h0 := eC_126
  have h1 := keC_127
  have h2 := keC_128
  have h3 := eC_129
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_26 : (1815155151383 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 131 * cCG cZ 131 + kappa * (ex (72426 / 100000) 132 * cCG cZ 132) - kappa * (ex (72426 / 100000) 133 * cCG cZ 133) - ex (72426 / 100000) 134 * cCG cZ 134 ∧ ex (72426 / 100000) 131 * cCG cZ 131 + kappa * (ex (72426 / 100000) 132 * cCG cZ 132) - kappa * (ex (72426 / 100000) 133 * cCG cZ 133) - ex (72426 / 100000) 134 * cCG cZ 134 ≤ (907578434237 / 31250000000000 : ℝ) := by
  have h0 := eC_131
  have h1 := keC_132
  have h2 := keC_133
  have h3 := eC_134
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_27 : (2680238883047 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 136 * cCG cZ 136 + kappa * (ex (72426 / 100000) 137 * cCG cZ 137) - kappa * (ex (72426 / 100000) 138 * cCG cZ 138) - ex (72426 / 100000) 139 * cCG cZ 139 ∧ ex (72426 / 100000) 136 * cCG cZ 136 + kappa * (ex (72426 / 100000) 137 * cCG cZ 137) - kappa * (ex (72426 / 100000) 138 * cCG cZ 138) - ex (72426 / 100000) 139 * cCG cZ 139 ≤ (6700610555151 / 500000000000000 : ℝ) := by
  have h0 := eC_136
  have h1 := keC_137
  have h2 := keC_138
  have h3 := eC_139
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_28 : (11468407271793 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 141 * cCG cZ 141 + kappa * (ex (72426 / 100000) 142 * cCG cZ 142) - kappa * (ex (72426 / 100000) 143 * cCG cZ 143) - ex (72426 / 100000) 144 * cCG cZ 144 ∧ ex (72426 / 100000) 141 * cCG cZ 141 + kappa * (ex (72426 / 100000) 142 * cCG cZ 142) - kappa * (ex (72426 / 100000) 143 * cCG cZ 143) - ex (72426 / 100000) 144 * cCG cZ 144 ≤ (11468433323981 / 1000000000000000 : ℝ) := by
  have h0 := eC_141
  have h1 := keC_142
  have h2 := keC_143
  have h3 := eC_144
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_29 : (11159798539713 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 146 * cCG cZ 146 + kappa * (ex (72426 / 100000) 147 * cCG cZ 147) - kappa * (ex (72426 / 100000) 148 * cCG cZ 148) - ex (72426 / 100000) 149 * cCG cZ 149 ∧ ex (72426 / 100000) 146 * cCG cZ 146 + kappa * (ex (72426 / 100000) 147 * cCG cZ 147) - kappa * (ex (72426 / 100000) 148 * cCG cZ 148) - ex (72426 / 100000) 149 * cCG cZ 149 ≤ (348744101 / 15625000000 : ℝ) := by
  have h0 := eC_146
  have h1 := keC_147
  have h2 := keC_148
  have h3 := eC_149
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_30 : (8306399220721 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 151 * cCG cZ 151 + kappa * (ex (72426 / 100000) 152 * cCG cZ 152) - kappa * (ex (72426 / 100000) 153 * cCG cZ 153) - ex (72426 / 100000) 154 * cCG cZ 154 ∧ ex (72426 / 100000) 151 * cCG cZ 151 + kappa * (ex (72426 / 100000) 152 * cCG cZ 152) - kappa * (ex (72426 / 100000) 153 * cCG cZ 153) - ex (72426 / 100000) 154 * cCG cZ 154 ≤ (2076601046361 / 50000000000000 : ℝ) := by
  have h0 := eC_151
  have h1 := keC_152
  have h2 := keC_153
  have h3 := eC_154
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_31 : (57220275151451 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 156 * cCG cZ 156 + kappa * (ex (72426 / 100000) 157 * cCG cZ 157) - kappa * (ex (72426 / 100000) 158 * cCG cZ 158) - ex (72426 / 100000) 159 * cCG cZ 159 ∧ ex (72426 / 100000) 156 * cCG cZ 156 + kappa * (ex (72426 / 100000) 157 * cCG cZ 157) - kappa * (ex (72426 / 100000) 158 * cCG cZ 158) - ex (72426 / 100000) 159 * cCG cZ 159 ≤ (3576268714101 / 62500000000000 : ℝ) := by
  have h0 := eC_156
  have h1 := keC_157
  have h2 := keC_158
  have h3 := eC_159
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_32 : (24639187935737 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 161 * cCG cZ 161 + kappa * (ex (72426 / 100000) 162 * cCG cZ 162) - kappa * (ex (72426 / 100000) 163 * cCG cZ 163) - ex (72426 / 100000) 164 * cCG cZ 164 ∧ ex (72426 / 100000) 161 * cCG cZ 161 + kappa * (ex (72426 / 100000) 162 * cCG cZ 162) - kappa * (ex (72426 / 100000) 163 * cCG cZ 163) - ex (72426 / 100000) 164 * cCG cZ 164 ≤ (3079899972929 / 62500000000000 : ℝ) := by
  have h0 := eC_161
  have h1 := keC_162
  have h2 := keC_163
  have h3 := eC_164
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_33 : (2956851530097 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 166 * cCG cZ 166 + kappa * (ex (72426 / 100000) 167 * cCG cZ 167) - kappa * (ex (72426 / 100000) 168 * cCG cZ 168) - ex (72426 / 100000) 169 * cCG cZ 169 ∧ ex (72426 / 100000) 166 * cCG cZ 166 + kappa * (ex (72426 / 100000) 167 * cCG cZ 167) - kappa * (ex (72426 / 100000) 168 * cCG cZ 168) - ex (72426 / 100000) 169 * cCG cZ 169 ≤ (1478431550993 / 250000000000000 : ℝ) := by
  have h0 := eC_166
  have h1 := keC_167
  have h2 := keC_168
  have h3 := eC_169
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_34 : (-11336891882669 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 171 * cCG cZ 171 + kappa * (ex (72426 / 100000) 172 * cCG cZ 172) - kappa * (ex (72426 / 100000) 173 * cCG cZ 173) - ex (72426 / 100000) 174 * cCG cZ 174 ∧ ex (72426 / 100000) 171 * cCG cZ 171 + kappa * (ex (72426 / 100000) 172 * cCG cZ 172) - kappa * (ex (72426 / 100000) 173 * cCG cZ 173) - ex (72426 / 100000) 174 * cCG cZ 174 ≤ (-11336886210783 / 250000000000000 : ℝ) := by
  have h0 := eC_171
  have h1 := keC_172
  have h2 := keC_173
  have h3 := eC_174
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_35 : (-42623584203103 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 176 * cCG cZ 176 + kappa * (ex (72426 / 100000) 177 * cCG cZ 177) - kappa * (ex (72426 / 100000) 178 * cCG cZ 178) - ex (72426 / 100000) 179 * cCG cZ 179 ∧ ex (72426 / 100000) 176 * cCG cZ 176 + kappa * (ex (72426 / 100000) 177 * cCG cZ 177) - kappa * (ex (72426 / 100000) 178 * cCG cZ 178) - ex (72426 / 100000) 179 * cCG cZ 179 ≤ (-42623561975017 / 1000000000000000 : ℝ) := by
  have h0 := eC_176
  have h1 := keC_177
  have h2 := keC_178
  have h3 := eC_179
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_36 : (22325284234857 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 181 * cCG cZ 181 + kappa * (ex (72426 / 100000) 182 * cCG cZ 182) - kappa * (ex (72426 / 100000) 183 * cCG cZ 183) - ex (72426 / 100000) 184 * cCG cZ 184 ∧ ex (72426 / 100000) 181 * cCG cZ 181 + kappa * (ex (72426 / 100000) 182 * cCG cZ 182) - kappa * (ex (72426 / 100000) 183 * cCG cZ 183) - ex (72426 / 100000) 184 * cCG cZ 184 ≤ (279066325027 / 12500000000000 : ℝ) := by
  have h0 := eC_181
  have h1 := keC_182
  have h2 := keC_183
  have h3 := eC_184
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_37 : (2925720907607 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 186 * cCG cZ 186 + kappa * (ex (72426 / 100000) 187 * cCG cZ 187) - kappa * (ex (72426 / 100000) 188 * cCG cZ 188) - ex (72426 / 100000) 189 * cCG cZ 189 ∧ ex (72426 / 100000) 186 * cCG cZ 186 + kappa * (ex (72426 / 100000) 187 * cCG cZ 187) - kappa * (ex (72426 / 100000) 188 * cCG cZ 188) - ex (72426 / 100000) 189 * cCG cZ 189 ≤ (46811555897147 / 1000000000000000 : ℝ) := by
  have h0 := eC_186
  have h1 := keC_187
  have h2 := keC_188
  have h3 := eC_189
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_38 : (-21024869357239 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 191 * cCG cZ 191 + kappa * (ex (72426 / 100000) 192 * cCG cZ 192) - kappa * (ex (72426 / 100000) 193 * cCG cZ 193) - ex (72426 / 100000) 194 * cCG cZ 194 ∧ ex (72426 / 100000) 191 * cCG cZ 191 + kappa * (ex (72426 / 100000) 192 * cCG cZ 192) - kappa * (ex (72426 / 100000) 193 * cCG cZ 193) - ex (72426 / 100000) 194 * cCG cZ 194 ≤ (-21024848414009 / 1000000000000000 : ℝ) := by
  have h0 := eC_191
  have h1 := keC_192
  have h2 := keC_193
  have h3 := eC_194
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_39 : (-19361478683027 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 196 * cCG cZ 196 + kappa * (ex (72426 / 100000) 197 * cCG cZ 197) - kappa * (ex (72426 / 100000) 198 * cCG cZ 198) - ex (72426 / 100000) 199 * cCG cZ 199 ∧ ex (72426 / 100000) 196 * cCG cZ 196 + kappa * (ex (72426 / 100000) 197 * cCG cZ 197) - kappa * (ex (72426 / 100000) 198 * cCG cZ 198) - ex (72426 / 100000) 199 * cCG cZ 199 ≤ (-38722936802327 / 1000000000000000 : ℝ) := by
  have h0 := eC_196
  have h1 := keC_197
  have h2 := keC_198
  have h3 := eC_199
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_40 : (36851980506083 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 201 * cCG cZ 201 + kappa * (ex (72426 / 100000) 202 * cCG cZ 202) - kappa * (ex (72426 / 100000) 203 * cCG cZ 203) - ex (72426 / 100000) 204 * cCG cZ 204 ∧ ex (72426 / 100000) 201 * cCG cZ 201 + kappa * (ex (72426 / 100000) 202 * cCG cZ 202) - kappa * (ex (72426 / 100000) 203 * cCG cZ 203) - ex (72426 / 100000) 204 * cCG cZ 204 ≤ (3685200071377 / 100000000000000 : ℝ) := by
  have h0 := eC_201
  have h1 := keC_202
  have h2 := keC_203
  have h3 := eC_204
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_0 : (179753145103 / 1562500000000 : ℝ) ≤ ex (72426 / 100000) 1 * sCG cZ 1 + kappa * (ex (72426 / 100000) 2 * sCG cZ 2) - kappa * (ex (72426 / 100000) 3 * sCG cZ 3) - ex (72426 / 100000) 4 * sCG cZ 4 ∧ ex (72426 / 100000) 1 * sCG cZ 1 + kappa * (ex (72426 / 100000) 2 * sCG cZ 2) - kappa * (ex (72426 / 100000) 3 * sCG cZ 3) - ex (72426 / 100000) 4 * sCG cZ 4 ≤ (11504204426057 / 100000000000000 : ℝ) := by
  have h0 : ex (72426 / 100000) 1 * sCG cZ 1 = (0 : ℝ) := by rw [sCG_one]; norm_num
  have h1 := keS_2
  have h2 := keS_3
  have h3 := eS_4
  constructor <;> linarith [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_1 : (294444322055217 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 6 * sCG cZ 6 + kappa * (ex (72426 / 100000) 7 * sCG cZ 7) - kappa * (ex (72426 / 100000) 8 * sCG cZ 8) - ex (72426 / 100000) 9 * sCG cZ 9 ∧ ex (72426 / 100000) 6 * sCG cZ 6 + kappa * (ex (72426 / 100000) 7 * sCG cZ 7) - kappa * (ex (72426 / 100000) 8 * sCG cZ 8) - ex (72426 / 100000) 9 * sCG cZ 9 ≤ (7361109109089 / 25000000000000 : ℝ) := by
  have h0 := eS_6
  have h1 := keS_7
  have h2 := keS_8
  have h3 := eS_9
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_2 : (-70399924198043 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 11 * sCG cZ 11 + kappa * (ex (72426 / 100000) 12 * sCG cZ 12) - kappa * (ex (72426 / 100000) 13 * sCG cZ 13) - ex (72426 / 100000) 14 * sCG cZ 14 ∧ ex (72426 / 100000) 11 * sCG cZ 11 + kappa * (ex (72426 / 100000) 12 * sCG cZ 12) - kappa * (ex (72426 / 100000) 13 * sCG cZ 13) - ex (72426 / 100000) 14 * sCG cZ 14 ≤ (-8799988484703 / 62500000000000 : ℝ) := by
  have h0 := eS_11
  have h1 := keS_12
  have h2 := keS_13
  have h3 := eS_14
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_3 : (5503059625559 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 16 * sCG cZ 16 + kappa * (ex (72426 / 100000) 17 * sCG cZ 17) - kappa * (ex (72426 / 100000) 18 * sCG cZ 18) - ex (72426 / 100000) 19 * sCG cZ 19 ∧ ex (72426 / 100000) 16 * sCG cZ 16 + kappa * (ex (72426 / 100000) 17 * sCG cZ 17) - kappa * (ex (72426 / 100000) 18 * sCG cZ 18) - ex (72426 / 100000) 19 * sCG cZ 19 ≤ (2751533894353 / 125000000000000 : ℝ) := by
  have h0 := eS_16
  have h1 := keS_17
  have h2 := keS_18
  have h3 := eS_19
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_4 : (-18564559793343 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 21 * sCG cZ 21 + kappa * (ex (72426 / 100000) 22 * sCG cZ 22) - kappa * (ex (72426 / 100000) 23 * sCG cZ 23) - ex (72426 / 100000) 24 * sCG cZ 24 ∧ ex (72426 / 100000) 21 * sCG cZ 21 + kappa * (ex (72426 / 100000) 22 * sCG cZ 22) - kappa * (ex (72426 / 100000) 23 * sCG cZ 23) - ex (72426 / 100000) 24 * sCG cZ 24 ≤ (-185645566863989 / 1000000000000000 : ℝ) := by
  have h0 := eS_21
  have h1 := keS_22
  have h2 := keS_23
  have h3 := eS_24
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_5 : (15356781416081 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 26 * sCG cZ 26 + kappa * (ex (72426 / 100000) 27 * sCG cZ 27) - kappa * (ex (72426 / 100000) 28 * sCG cZ 28) - ex (72426 / 100000) 29 * sCG cZ 29 ∧ ex (72426 / 100000) 26 * sCG cZ 26 + kappa * (ex (72426 / 100000) 27 * sCG cZ 27) - kappa * (ex (72426 / 100000) 28 * sCG cZ 28) - ex (72426 / 100000) 29 * sCG cZ 29 ≤ (15356808926403 / 1000000000000000 : ℝ) := by
  have h0 := eS_26
  have h1 := keS_27
  have h2 := keS_28
  have h3 := eS_29
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_6 : (-120915546283897 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 31 * sCG cZ 31 + kappa * (ex (72426 / 100000) 32 * sCG cZ 32) - kappa * (ex (72426 / 100000) 33 * sCG cZ 33) - ex (72426 / 100000) 34 * sCG cZ 34 ∧ ex (72426 / 100000) 31 * sCG cZ 31 + kappa * (ex (72426 / 100000) 32 * sCG cZ 32) - kappa * (ex (72426 / 100000) 33 * sCG cZ 33) - ex (72426 / 100000) 34 * sCG cZ 34 ≤ (-120915521713821 / 1000000000000000 : ℝ) := by
  have h0 := eS_31
  have h1 := keS_32
  have h2 := keS_33
  have h3 := eS_34
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_7 : (-28150899035477 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 36 * sCG cZ 36 + kappa * (ex (72426 / 100000) 37 * sCG cZ 37) - kappa * (ex (72426 / 100000) 38 * sCG cZ 38) - ex (72426 / 100000) 39 * sCG cZ 39 ∧ ex (72426 / 100000) 36 * sCG cZ 36 + kappa * (ex (72426 / 100000) 37 * sCG cZ 37) - kappa * (ex (72426 / 100000) 38 * sCG cZ 38) - ex (72426 / 100000) 39 * sCG cZ 39 ≤ (-112603574043331 / 1000000000000000 : ℝ) := by
  have h0 := eS_36
  have h1 := keS_37
  have h2 := keS_38
  have h3 := eS_39
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_8 : (6764390445167 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 41 * sCG cZ 41 + kappa * (ex (72426 / 100000) 42 * sCG cZ 42) - kappa * (ex (72426 / 100000) 43 * sCG cZ 43) - ex (72426 / 100000) 44 * sCG cZ 44 ∧ ex (72426 / 100000) 41 * sCG cZ 41 + kappa * (ex (72426 / 100000) 42 * sCG cZ 42) - kappa * (ex (72426 / 100000) 43 * sCG cZ 43) - ex (72426 / 100000) 44 * sCG cZ 44 ≤ (3382197749989 / 125000000000000 : ℝ) := by
  have h0 := eS_41
  have h1 := keS_42
  have h2 := keS_43
  have h3 := eS_44
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_9 : (-22027644156193 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 46 * sCG cZ 46 + kappa * (ex (72426 / 100000) 47 * sCG cZ 47) - kappa * (ex (72426 / 100000) 48 * sCG cZ 48) - ex (72426 / 100000) 49 * sCG cZ 49 ∧ ex (72426 / 100000) 46 * sCG cZ 46 + kappa * (ex (72426 / 100000) 47 * sCG cZ 47) - kappa * (ex (72426 / 100000) 48 * sCG cZ 48) - ex (72426 / 100000) 49 * sCG cZ 49 ≤ (-4405526960451 / 100000000000000 : ℝ) := by
  have h0 := eS_46
  have h1 := keS_47
  have h2 := keS_48
  have h3 := eS_49
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_10 : (-26236316244021 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 51 * sCG cZ 51 + kappa * (ex (72426 / 100000) 52 * sCG cZ 52) - kappa * (ex (72426 / 100000) 53 * sCG cZ 53) - ex (72426 / 100000) 54 * sCG cZ 54 ∧ ex (72426 / 100000) 51 * sCG cZ 51 + kappa * (ex (72426 / 100000) 52 * sCG cZ 52) - kappa * (ex (72426 / 100000) 53 * sCG cZ 53) - ex (72426 / 100000) 54 * sCG cZ 54 ≤ (-10494523021111 / 200000000000000 : ℝ) := by
  have h0 := eS_51
  have h1 := keS_52
  have h2 := keS_53
  have h3 := eS_54
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_11 : (2786256339271 / 40000000000000 : ℝ) ≤ ex (72426 / 100000) 56 * sCG cZ 56 + kappa * (ex (72426 / 100000) 57 * sCG cZ 57) - kappa * (ex (72426 / 100000) 58 * sCG cZ 58) - ex (72426 / 100000) 59 * sCG cZ 59 ∧ ex (72426 / 100000) 56 * sCG cZ 56 + kappa * (ex (72426 / 100000) 57 * sCG cZ 57) - kappa * (ex (72426 / 100000) 58 * sCG cZ 58) - ex (72426 / 100000) 59 * sCG cZ 59 ≤ (1393128535579 / 20000000000000 : ℝ) := by
  have h0 := eS_56
  have h1 := keS_57
  have h2 := keS_58
  have h3 := eS_59
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_12 : (-13029733194229 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 61 * sCG cZ 61 + kappa * (ex (72426 / 100000) 62 * sCG cZ 62) - kappa * (ex (72426 / 100000) 63 * sCG cZ 63) - ex (72426 / 100000) 64 * sCG cZ 64 ∧ ex (72426 / 100000) 61 * sCG cZ 61 + kappa * (ex (72426 / 100000) 62 * sCG cZ 62) - kappa * (ex (72426 / 100000) 63 * sCG cZ 63) - ex (72426 / 100000) 64 * sCG cZ 64 ≤ (-13029707686469 / 1000000000000000 : ℝ) := by
  have h0 := eS_61
  have h1 := keS_62
  have h2 := keS_63
  have h3 := eS_64
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_13 : (-39105858282529 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 66 * sCG cZ 66 + kappa * (ex (72426 / 100000) 67 * sCG cZ 67) - kappa * (ex (72426 / 100000) 68 * sCG cZ 68) - ex (72426 / 100000) 69 * sCG cZ 69 ∧ ex (72426 / 100000) 66 * sCG cZ 66 + kappa * (ex (72426 / 100000) 67 * sCG cZ 67) - kappa * (ex (72426 / 100000) 68 * sCG cZ 68) - ex (72426 / 100000) 69 * sCG cZ 69 ≤ (-9776457050551 / 250000000000000 : ℝ) := by
  have h0 := eS_66
  have h1 := keS_67
  have h2 := keS_68
  have h3 := eS_69
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_14 : (-9902377861991 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 71 * sCG cZ 71 + kappa * (ex (72426 / 100000) 72 * sCG cZ 72) - kappa * (ex (72426 / 100000) 73 * sCG cZ 73) - ex (72426 / 100000) 74 * sCG cZ 74 ∧ ex (72426 / 100000) 71 * sCG cZ 71 + kappa * (ex (72426 / 100000) 72 * sCG cZ 72) - kappa * (ex (72426 / 100000) 73 * sCG cZ 73) - ex (72426 / 100000) 74 * sCG cZ 74 ≤ (-19804723335807 / 1000000000000000 : ℝ) := by
  have h0 := eS_71
  have h1 := keS_72
  have h2 := keS_73
  have h3 := eS_74
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_15 : (-1167819336247 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 76 * sCG cZ 76 + kappa * (ex (72426 / 100000) 77 * sCG cZ 77) - kappa * (ex (72426 / 100000) 78 * sCG cZ 78) - ex (72426 / 100000) 79 * sCG cZ 79 ∧ ex (72426 / 100000) 76 * sCG cZ 76 + kappa * (ex (72426 / 100000) 77 * sCG cZ 77) - kappa * (ex (72426 / 100000) 78 * sCG cZ 78) - ex (72426 / 100000) 79 * sCG cZ 79 ≤ (-116778585137 / 100000000000000 : ℝ) := by
  have h0 := eS_76
  have h1 := keS_77
  have h2 := keS_78
  have h3 := eS_79
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_16 : (-3055919384539 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 81 * sCG cZ 81 + kappa * (ex (72426 / 100000) 82 * sCG cZ 82) - kappa * (ex (72426 / 100000) 83 * sCG cZ 83) - ex (72426 / 100000) 84 * sCG cZ 84 ∧ ex (72426 / 100000) 81 * sCG cZ 81 + kappa * (ex (72426 / 100000) 82 * sCG cZ 82) - kappa * (ex (72426 / 100000) 83 * sCG cZ 83) - ex (72426 / 100000) 84 * sCG cZ 84 ≤ (-12223643751199 / 1000000000000000 : ℝ) := by
  have h0 := eS_81
  have h1 := keS_82
  have h2 := keS_83
  have h3 := eS_84
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_17 : (122610725033 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 86 * sCG cZ 86 + kappa * (ex (72426 / 100000) 87 * sCG cZ 87) - kappa * (ex (72426 / 100000) 88 * sCG cZ 88) - ex (72426 / 100000) 89 * sCG cZ 89 ∧ ex (72426 / 100000) 86 * sCG cZ 86 + kappa * (ex (72426 / 100000) 87 * sCG cZ 87) - kappa * (ex (72426 / 100000) 88 * sCG cZ 88) - ex (72426 / 100000) 89 * sCG cZ 89 ≤ (6132219831 / 50000000000000 : ℝ) := by
  have h0 := eS_86
  have h1 := keS_87
  have h2 := keS_88
  have h3 := eS_89
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_18 : (14751714263077 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 91 * sCG cZ 91 + kappa * (ex (72426 / 100000) 92 * sCG cZ 92) - kappa * (ex (72426 / 100000) 93 * sCG cZ 93) - ex (72426 / 100000) 94 * sCG cZ 94 ∧ ex (72426 / 100000) 91 * sCG cZ 91 + kappa * (ex (72426 / 100000) 92 * sCG cZ 92) - kappa * (ex (72426 / 100000) 93 * sCG cZ 93) - ex (72426 / 100000) 94 * sCG cZ 94 ≤ (368793687927 / 25000000000000 : ℝ) := by
  have h0 := eS_91
  have h1 := keS_92
  have h2 := keS_93
  have h3 := eS_94
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_19 : (-2556615591779 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 96 * sCG cZ 96 + kappa * (ex (72426 / 100000) 97 * sCG cZ 97) - kappa * (ex (72426 / 100000) 98 * sCG cZ 98) - ex (72426 / 100000) 99 * sCG cZ 99 ∧ ex (72426 / 100000) 96 * sCG cZ 96 + kappa * (ex (72426 / 100000) 97 * sCG cZ 97) - kappa * (ex (72426 / 100000) 98 * sCG cZ 98) - ex (72426 / 100000) 99 * sCG cZ 99 ≤ (-12783045303893 / 1000000000000000 : ℝ) := by
  have h0 := eS_96
  have h1 := keS_97
  have h2 := keS_98
  have h3 := eS_99
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_20 : (-15459621555269 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 101 * sCG cZ 101 + kappa * (ex (72426 / 100000) 102 * sCG cZ 102) - kappa * (ex (72426 / 100000) 103 * sCG cZ 103) - ex (72426 / 100000) 104 * sCG cZ 104 ∧ ex (72426 / 100000) 101 * sCG cZ 101 + kappa * (ex (72426 / 100000) 102 * sCG cZ 102) - kappa * (ex (72426 / 100000) 103 * sCG cZ 103) - ex (72426 / 100000) 104 * sCG cZ 104 ≤ (-15459589560709 / 1000000000000000 : ℝ) := by
  have h0 := eS_101
  have h1 := keS_102
  have h2 := keS_103
  have h3 := eS_104
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_21 : (54391175291561 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 106 * sCG cZ 106 + kappa * (ex (72426 / 100000) 107 * sCG cZ 107) - kappa * (ex (72426 / 100000) 108 * sCG cZ 108) - ex (72426 / 100000) 109 * sCG cZ 109 ∧ ex (72426 / 100000) 106 * sCG cZ 106 + kappa * (ex (72426 / 100000) 107 * sCG cZ 107) - kappa * (ex (72426 / 100000) 108 * sCG cZ 108) - ex (72426 / 100000) 109 * sCG cZ 109 ≤ (6798900818583 / 125000000000000 : ℝ) := by
  have h0 := eS_106
  have h1 := keS_107
  have h2 := keS_108
  have h3 := eS_109
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_22 : (-25565840402107 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 111 * sCG cZ 111 + kappa * (ex (72426 / 100000) 112 * sCG cZ 112) - kappa * (ex (72426 / 100000) 113 * sCG cZ 113) - ex (72426 / 100000) 114 * sCG cZ 114 ∧ ex (72426 / 100000) 111 * sCG cZ 111 + kappa * (ex (72426 / 100000) 112 * sCG cZ 112) - kappa * (ex (72426 / 100000) 113 * sCG cZ 113) - ex (72426 / 100000) 114 * sCG cZ 114 ≤ (-12782904920231 / 500000000000000 : ℝ) := by
  have h0 := eS_111
  have h1 := keS_112
  have h2 := keS_113
  have h3 := eS_114
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_23 : (-11802500624629 / 200000000000000 : ℝ) ≤ ex (72426 / 100000) 116 * sCG cZ 116 + kappa * (ex (72426 / 100000) 117 * sCG cZ 117) - kappa * (ex (72426 / 100000) 118 * sCG cZ 118) - ex (72426 / 100000) 119 * sCG cZ 119 ∧ ex (72426 / 100000) 116 * sCG cZ 116 + kappa * (ex (72426 / 100000) 117 * sCG cZ 117) - kappa * (ex (72426 / 100000) 118 * sCG cZ 118) - ex (72426 / 100000) 119 * sCG cZ 119 ≤ (-14753118318367 / 250000000000000 : ℝ) := by
  have h0 := eS_116
  have h1 := keS_117
  have h2 := keS_118
  have h3 := eS_119
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_24 : (-6549014214439 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 121 * sCG cZ 121 + kappa * (ex (72426 / 100000) 122 * sCG cZ 122) - kappa * (ex (72426 / 100000) 123 * sCG cZ 123) - ex (72426 / 100000) 124 * sCG cZ 124 ∧ ex (72426 / 100000) 121 * sCG cZ 121 + kappa * (ex (72426 / 100000) 122 * sCG cZ 122) - kappa * (ex (72426 / 100000) 123 * sCG cZ 123) - ex (72426 / 100000) 124 * sCG cZ 124 ≤ (-13097999356231 / 1000000000000000 : ℝ) := by
  have h0 := eS_121
  have h1 := keS_122
  have h2 := keS_123
  have h3 := eS_124
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_25 : (34341219585079 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 126 * sCG cZ 126 + kappa * (ex (72426 / 100000) 127 * sCG cZ 127) - kappa * (ex (72426 / 100000) 128 * sCG cZ 128) - ex (72426 / 100000) 129 * sCG cZ 129 ∧ ex (72426 / 100000) 126 * sCG cZ 126 + kappa * (ex (72426 / 100000) 127 * sCG cZ 127) - kappa * (ex (72426 / 100000) 128 * sCG cZ 128) - ex (72426 / 100000) 129 * sCG cZ 129 ≤ (34341247840821 / 1000000000000000 : ℝ) := by
  have h0 := eS_126
  have h1 := keS_127
  have h2 := keS_128
  have h3 := eS_129
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_26 : (6988775656669 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 131 * sCG cZ 131 + kappa * (ex (72426 / 100000) 132 * sCG cZ 132) - kappa * (ex (72426 / 100000) 133 * sCG cZ 133) - ex (72426 / 100000) 134 * sCG cZ 134 ∧ ex (72426 / 100000) 131 * sCG cZ 131 + kappa * (ex (72426 / 100000) 132 * sCG cZ 132) - kappa * (ex (72426 / 100000) 133 * sCG cZ 133) - ex (72426 / 100000) 134 * sCG cZ 134 ≤ (55910232756351 / 1000000000000000 : ℝ) := by
  have h0 := eS_131
  have h1 := keS_132
  have h2 := keS_133
  have h3 := eS_134
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_27 : (30575706590839 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 136 * sCG cZ 136 + kappa * (ex (72426 / 100000) 137 * sCG cZ 137) - kappa * (ex (72426 / 100000) 138 * sCG cZ 138) - ex (72426 / 100000) 139 * sCG cZ 139 ∧ ex (72426 / 100000) 136 * sCG cZ 136 + kappa * (ex (72426 / 100000) 137 * sCG cZ 137) - kappa * (ex (72426 / 100000) 138 * sCG cZ 138) - ex (72426 / 100000) 139 * sCG cZ 139 ≤ (61151439921113 / 1000000000000000 : ℝ) := by
  have h0 := eS_136
  have h1 := keS_137
  have h2 := keS_138
  have h3 := eS_139
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_28 : (15207616301493 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 141 * sCG cZ 141 + kappa * (ex (72426 / 100000) 142 * sCG cZ 142) - kappa * (ex (72426 / 100000) 143 * sCG cZ 143) - ex (72426 / 100000) 144 * sCG cZ 144 ∧ ex (72426 / 100000) 141 * sCG cZ 141 + kappa * (ex (72426 / 100000) 142 * sCG cZ 142) - kappa * (ex (72426 / 100000) 143 * sCG cZ 143) - ex (72426 / 100000) 144 * sCG cZ 144 ≤ (60830491308279 / 1000000000000000 : ℝ) := by
  have h0 := eS_141
  have h1 := keS_142
  have h2 := keS_143
  have h3 := eS_144
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_29 : (1773244246333 / 31250000000000 : ℝ) ≤ ex (72426 / 100000) 146 * sCG cZ 146 + kappa * (ex (72426 / 100000) 147 * sCG cZ 147) - kappa * (ex (72426 / 100000) 148 * sCG cZ 148) - ex (72426 / 100000) 149 * sCG cZ 149 ∧ ex (72426 / 100000) 146 * sCG cZ 146 + kappa * (ex (72426 / 100000) 147 * sCG cZ 147) - kappa * (ex (72426 / 100000) 148 * sCG cZ 148) - ex (72426 / 100000) 149 * sCG cZ 149 ≤ (5674384130617 / 100000000000000 : ℝ) := by
  have h0 := eS_146
  have h1 := keS_147
  have h2 := keS_148
  have h3 := eS_149
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_30 : (674037775071 / 15625000000000 : ℝ) ≤ ex (72426 / 100000) 151 * sCG cZ 151 + kappa * (ex (72426 / 100000) 152 * sCG cZ 152) - kappa * (ex (72426 / 100000) 153 * sCG cZ 153) - ex (72426 / 100000) 154 * sCG cZ 154 ∧ ex (72426 / 100000) 151 * sCG cZ 151 + kappa * (ex (72426 / 100000) 152 * sCG cZ 152) - kappa * (ex (72426 / 100000) 153 * sCG cZ 153) - ex (72426 / 100000) 154 * sCG cZ 154 ≤ (21569221214647 / 500000000000000 : ℝ) := by
  have h0 := eS_151
  have h1 := keS_152
  have h2 := keS_153
  have h3 := eS_154
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_31 : (12948846951783 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 156 * sCG cZ 156 + kappa * (ex (72426 / 100000) 157 * sCG cZ 157) - kappa * (ex (72426 / 100000) 158 * sCG cZ 158) - ex (72426 / 100000) 159 * sCG cZ 159 ∧ ex (72426 / 100000) 156 * sCG cZ 156 + kappa * (ex (72426 / 100000) 157 * sCG cZ 157) - kappa * (ex (72426 / 100000) 158 * sCG cZ 158) - ex (72426 / 100000) 159 * sCG cZ 159 ≤ (6474435586927 / 500000000000000 : ℝ) := by
  have h0 := eS_156
  have h1 := keS_157
  have h2 := keS_158
  have h3 := eS_159
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_32 : (-29372922291183 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 161 * sCG cZ 161 + kappa * (ex (72426 / 100000) 162 * sCG cZ 162) - kappa * (ex (72426 / 100000) 163 * sCG cZ 163) - ex (72426 / 100000) 164 * sCG cZ 164 ∧ ex (72426 / 100000) 161 * sCG cZ 161 + kappa * (ex (72426 / 100000) 162 * sCG cZ 162) - kappa * (ex (72426 / 100000) 163 * sCG cZ 163) - ex (72426 / 100000) 164 * sCG cZ 164 ≤ (-7343224653929 / 250000000000000 : ℝ) := by
  have h0 := eS_161
  have h1 := keS_162
  have h2 := keS_163
  have h3 := eS_164
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_33 : (-13925332614041 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 166 * sCG cZ 166 + kappa * (ex (72426 / 100000) 167 * sCG cZ 167) - kappa * (ex (72426 / 100000) 168 * sCG cZ 168) - ex (72426 / 100000) 169 * sCG cZ 169 ∧ ex (72426 / 100000) 166 * sCG cZ 166 + kappa * (ex (72426 / 100000) 167 * sCG cZ 167) - kappa * (ex (72426 / 100000) 168 * sCG cZ 168) - ex (72426 / 100000) 169 * sCG cZ 169 ≤ (-27850653627071 / 500000000000000 : ℝ) := by
  have h0 := eS_166
  have h1 := keS_167
  have h2 := keS_168
  have h3 := eS_169
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_34 : (-30459989202241 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 171 * sCG cZ 171 + kappa * (ex (72426 / 100000) 172 * sCG cZ 172) - kappa * (ex (72426 / 100000) 173 * sCG cZ 173) - ex (72426 / 100000) 174 * sCG cZ 174 ∧ ex (72426 / 100000) 171 * sCG cZ 171 + kappa * (ex (72426 / 100000) 172 * sCG cZ 172) - kappa * (ex (72426 / 100000) 173 * sCG cZ 173) - ex (72426 / 100000) 174 * sCG cZ 174 ≤ (-7614991632487 / 250000000000000 : ℝ) := by
  have h0 := eS_171
  have h1 := keS_172
  have h2 := keS_173
  have h3 := eS_174
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_35 : (7969971371313 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 176 * sCG cZ 176 + kappa * (ex (72426 / 100000) 177 * sCG cZ 177) - kappa * (ex (72426 / 100000) 178 * sCG cZ 178) - ex (72426 / 100000) 179 * sCG cZ 179 ∧ ex (72426 / 100000) 176 * sCG cZ 176 + kappa * (ex (72426 / 100000) 177 * sCG cZ 177) - kappa * (ex (72426 / 100000) 178 * sCG cZ 178) - ex (72426 / 100000) 179 * sCG cZ 179 ≤ (31879907701849 / 1000000000000000 : ℝ) := by
  have h0 := eS_176
  have h1 := keS_177
  have h2 := keS_178
  have h3 := eS_179
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_36 : (23384841150951 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 181 * sCG cZ 181 + kappa * (ex (72426 / 100000) 182 * sCG cZ 182) - kappa * (ex (72426 / 100000) 183 * sCG cZ 183) - ex (72426 / 100000) 184 * sCG cZ 184 ∧ ex (72426 / 100000) 181 * sCG cZ 181 + kappa * (ex (72426 / 100000) 182 * sCG cZ 182) - kappa * (ex (72426 / 100000) 183 * sCG cZ 183) - ex (72426 / 100000) 184 * sCG cZ 184 ≤ (46769704094343 / 1000000000000000 : ℝ) := by
  have h0 := eS_181
  have h1 := keS_182
  have h2 := keS_183
  have h3 := eS_184
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_37 : (-2345720063517 / 125000000000000 : ℝ) ≤ ex (72426 / 100000) 186 * sCG cZ 186 + kappa * (ex (72426 / 100000) 187 * sCG cZ 187) - kappa * (ex (72426 / 100000) 188 * sCG cZ 188) - ex (72426 / 100000) 189 * sCG cZ 189 ∧ ex (72426 / 100000) 186 * sCG cZ 186 + kappa * (ex (72426 / 100000) 187 * sCG cZ 187) - kappa * (ex (72426 / 100000) 188 * sCG cZ 188) - ex (72426 / 100000) 189 * sCG cZ 189 ≤ (-18765739162529 / 1000000000000000 : ℝ) := by
  have h0 := eS_186
  have h1 := keS_187
  have h2 := keS_188
  have h3 := eS_189
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_38 : (-44325225606527 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 191 * sCG cZ 191 + kappa * (ex (72426 / 100000) 192 * sCG cZ 192) - kappa * (ex (72426 / 100000) 193 * sCG cZ 193) - ex (72426 / 100000) 194 * sCG cZ 194 ∧ ex (72426 / 100000) 191 * sCG cZ 191 + kappa * (ex (72426 / 100000) 192 * sCG cZ 192) - kappa * (ex (72426 / 100000) 193 * sCG cZ 193) - ex (72426 / 100000) 194 * sCG cZ 194 ≤ (-8865040927927 / 200000000000000 : ℝ) := by
  have h0 := eS_191
  have h1 := keS_192
  have h2 := keS_193
  have h3 := eS_194
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_39 : (27869002922099 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 196 * sCG cZ 196 + kappa * (ex (72426 / 100000) 197 * sCG cZ 197) - kappa * (ex (72426 / 100000) 198 * sCG cZ 198) - ex (72426 / 100000) 199 * sCG cZ 199 ∧ ex (72426 / 100000) 196 * sCG cZ 196 + kappa * (ex (72426 / 100000) 197 * sCG cZ 197) - kappa * (ex (72426 / 100000) 198 * sCG cZ 198) - ex (72426 / 100000) 199 * sCG cZ 199 ≤ (108863372953 / 3906250000000 : ℝ) := by
  have h0 := eS_196
  have h1 := keS_197
  have h2 := keS_198
  have h3 := eS_199
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_40 : (14086961223643 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 201 * sCG cZ 201 + kappa * (ex (72426 / 100000) 202 * sCG cZ 202) - kappa * (ex (72426 / 100000) 203 * sCG cZ 203) - ex (72426 / 100000) 204 * sCG cZ 204 ∧ ex (72426 / 100000) 201 * sCG cZ 201 + kappa * (ex (72426 / 100000) 202 * sCG cZ 202) - kappa * (ex (72426 / 100000) 203 * sCG cZ 203) - ex (72426 / 100000) 204 * sCG cZ 204 ≤ (28173942646593 / 1000000000000000 : ℝ) := by
  have h0 := eS_201
  have h1 := keS_202
  have h2 := keS_203
  have h3 := eS_204
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_0 : (-368652071783701 / 500000000000000 : ℝ) ≤ Real.log 1 * (ex (72426 / 100000) 1 * cCG cZ 1) + kappa * (Real.log 2 * (ex (72426 / 100000) 2 * cCG cZ 2)) - kappa * (Real.log 3 * (ex (72426 / 100000) 3 * cCG cZ 3)) - Real.log 4 * (ex (72426 / 100000) 4 * cCG cZ 4) ∧ Real.log 1 * (ex (72426 / 100000) 1 * cCG cZ 1) + kappa * (Real.log 2 * (ex (72426 / 100000) 2 * cCG cZ 2)) - kappa * (Real.log 3 * (ex (72426 / 100000) 3 * cCG cZ 3)) - Real.log 4 * (ex (72426 / 100000) 4 * cCG cZ 4) ≤ (-36865205291323 / 50000000000000 : ℝ) := by
  have h0 : Real.log 1 * (ex (72426 / 100000) 1 * cCG cZ 1) = (0 : ℝ) := by rw [Real.log_one]; norm_num
  have h1 := kleC_2
  have h2 := kleC_3
  have h3 := leC_4
  constructor <;> linarith [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_1 : (-386441011054881 / 1000000000000000 : ℝ) ≤ Real.log 6 * (ex (72426 / 100000) 6 * cCG cZ 6) + kappa * (Real.log 7 * (ex (72426 / 100000) 7 * cCG cZ 7)) - kappa * (Real.log 8 * (ex (72426 / 100000) 8 * cCG cZ 8)) - Real.log 9 * (ex (72426 / 100000) 9 * cCG cZ 9) ∧ Real.log 6 * (ex (72426 / 100000) 6 * cCG cZ 6) + kappa * (Real.log 7 * (ex (72426 / 100000) 7 * cCG cZ 7)) - kappa * (Real.log 8 * (ex (72426 / 100000) 8 * cCG cZ 8)) - Real.log 9 * (ex (72426 / 100000) 9 * cCG cZ 9) ≤ (-193220463405601 / 500000000000000 : ℝ) := by
  have h0 := leC_6
  have h1 := kleC_7
  have h2 := kleC_8
  have h3 := leC_9
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_2 : (-113668585032599 / 250000000000000 : ℝ) ≤ Real.log 11 * (ex (72426 / 100000) 11 * cCG cZ 11) + kappa * (Real.log 12 * (ex (72426 / 100000) 12 * cCG cZ 12)) - kappa * (Real.log 13 * (ex (72426 / 100000) 13 * cCG cZ 13)) - Real.log 14 * (ex (72426 / 100000) 14 * cCG cZ 14) ∧ Real.log 11 * (ex (72426 / 100000) 11 * cCG cZ 11) + kappa * (Real.log 12 * (ex (72426 / 100000) 12 * cCG cZ 12)) - kappa * (Real.log 13 * (ex (72426 / 100000) 13 * cCG cZ 13)) - Real.log 14 * (ex (72426 / 100000) 14 * cCG cZ 14) ≤ (-454674258062571 / 1000000000000000 : ℝ) := by
  have h0 := leC_11
  have h1 := kleC_12
  have h2 := kleC_13
  have h3 := leC_14
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_3 : (55863146791091 / 250000000000000 : ℝ) ≤ Real.log 16 * (ex (72426 / 100000) 16 * cCG cZ 16) + kappa * (Real.log 17 * (ex (72426 / 100000) 17 * cCG cZ 17)) - kappa * (Real.log 18 * (ex (72426 / 100000) 18 * cCG cZ 18)) - Real.log 19 * (ex (72426 / 100000) 19 * cCG cZ 19) ∧ Real.log 16 * (ex (72426 / 100000) 16 * cCG cZ 16) + kappa * (Real.log 17 * (ex (72426 / 100000) 17 * cCG cZ 17)) - kappa * (Real.log 18 * (ex (72426 / 100000) 18 * cCG cZ 18)) - Real.log 19 * (ex (72426 / 100000) 19 * cCG cZ 19) ≤ (44690536133803 / 200000000000000 : ℝ) := by
  have h0 := leC_16
  have h1 := kleC_17
  have h2 := kleC_18
  have h3 := leC_19
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_4 : (29738714665591 / 1000000000000000 : ℝ) ≤ Real.log 21 * (ex (72426 / 100000) 21 * cCG cZ 21) + kappa * (Real.log 22 * (ex (72426 / 100000) 22 * cCG cZ 22)) - kappa * (Real.log 23 * (ex (72426 / 100000) 23 * cCG cZ 23)) - Real.log 24 * (ex (72426 / 100000) 24 * cCG cZ 24) ∧ Real.log 21 * (ex (72426 / 100000) 21 * cCG cZ 21) + kappa * (Real.log 22 * (ex (72426 / 100000) 22 * cCG cZ 22)) - kappa * (Real.log 23 * (ex (72426 / 100000) 23 * cCG cZ 23)) - Real.log 24 * (ex (72426 / 100000) 24 * cCG cZ 24) ≤ (29738811467637 / 1000000000000000 : ℝ) := by
  have h0 := leC_21
  have h1 := kleC_22
  have h2 := kleC_23
  have h3 := leC_24
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_5 : (-66414712914967 / 500000000000000 : ℝ) ≤ Real.log 26 * (ex (72426 / 100000) 26 * cCG cZ 26) + kappa * (Real.log 27 * (ex (72426 / 100000) 27 * cCG cZ 27)) - kappa * (Real.log 28 * (ex (72426 / 100000) 28 * cCG cZ 28)) - Real.log 29 * (ex (72426 / 100000) 29 * cCG cZ 29) ∧ Real.log 26 * (ex (72426 / 100000) 26 * cCG cZ 26) + kappa * (Real.log 27 * (ex (72426 / 100000) 27 * cCG cZ 27)) - kappa * (Real.log 28 * (ex (72426 / 100000) 28 * cCG cZ 28)) - Real.log 29 * (ex (72426 / 100000) 29 * cCG cZ 29) ≤ (-66414667414873 / 500000000000000 : ℝ) := by
  have h0 := leC_26
  have h1 := kleC_27
  have h2 := kleC_28
  have h3 := leC_29
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_6 : (-423159185115549 / 1000000000000000 : ℝ) ≤ Real.log 31 * (ex (72426 / 100000) 31 * cCG cZ 31) + kappa * (Real.log 32 * (ex (72426 / 100000) 32 * cCG cZ 32)) - kappa * (Real.log 33 * (ex (72426 / 100000) 33 * cCG cZ 33)) - Real.log 34 * (ex (72426 / 100000) 34 * cCG cZ 34) ∧ Real.log 31 * (ex (72426 / 100000) 31 * cCG cZ 31) + kappa * (Real.log 32 * (ex (72426 / 100000) 32 * cCG cZ 32)) - kappa * (Real.log 33 * (ex (72426 / 100000) 33 * cCG cZ 33)) - Real.log 34 * (ex (72426 / 100000) 34 * cCG cZ 34) ≤ (-423159099513311 / 1000000000000000 : ℝ) := by
  have h0 := leC_31
  have h1 := kleC_32
  have h2 := kleC_33
  have h3 := leC_34
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_7 : (-126120645862227 / 500000000000000 : ℝ) ≤ Real.log 36 * (ex (72426 / 100000) 36 * cCG cZ 36) + kappa * (Real.log 37 * (ex (72426 / 100000) 37 * cCG cZ 37)) - kappa * (Real.log 38 * (ex (72426 / 100000) 38 * cCG cZ 38)) - Real.log 39 * (ex (72426 / 100000) 39 * cCG cZ 39) ∧ Real.log 36 * (ex (72426 / 100000) 36 * cCG cZ 36) + kappa * (Real.log 37 * (ex (72426 / 100000) 37 * cCG cZ 37)) - kappa * (Real.log 38 * (ex (72426 / 100000) 38 * cCG cZ 38)) - Real.log 39 * (ex (72426 / 100000) 39 * cCG cZ 39) ≤ (-252241211597833 / 1000000000000000 : ℝ) := by
  have h0 := leC_36
  have h1 := kleC_37
  have h2 := kleC_38
  have h3 := leC_39
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_8 : (25064135648383 / 1000000000000000 : ℝ) ≤ Real.log 41 * (ex (72426 / 100000) 41 * cCG cZ 41) + kappa * (Real.log 42 * (ex (72426 / 100000) 42 * cCG cZ 42)) - kappa * (Real.log 43 * (ex (72426 / 100000) 43 * cCG cZ 43)) - Real.log 44 * (ex (72426 / 100000) 44 * cCG cZ 44) ∧ Real.log 41 * (ex (72426 / 100000) 41 * cCG cZ 41) + kappa * (Real.log 42 * (ex (72426 / 100000) 42 * cCG cZ 42)) - kappa * (Real.log 43 * (ex (72426 / 100000) 43 * cCG cZ 43)) - Real.log 44 * (ex (72426 / 100000) 44 * cCG cZ 44) ≤ (25064211621827 / 1000000000000000 : ℝ) := by
  have h0 := leC_41
  have h1 := kleC_42
  have h2 := kleC_43
  have h3 := leC_44
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_9 : (52425591197081 / 1000000000000000 : ℝ) ≤ Real.log 46 * (ex (72426 / 100000) 46 * cCG cZ 46) + kappa * (Real.log 47 * (ex (72426 / 100000) 47 * cCG cZ 47)) - kappa * (Real.log 48 * (ex (72426 / 100000) 48 * cCG cZ 48)) - Real.log 49 * (ex (72426 / 100000) 49 * cCG cZ 49) ∧ Real.log 46 * (ex (72426 / 100000) 46 * cCG cZ 46) + kappa * (Real.log 47 * (ex (72426 / 100000) 47 * cCG cZ 47)) - kappa * (Real.log 48 * (ex (72426 / 100000) 48 * cCG cZ 48)) - Real.log 49 * (ex (72426 / 100000) 49 * cCG cZ 49) ≤ (52425663462817 / 1000000000000000 : ℝ) := by
  have h0 := leC_46
  have h1 := kleC_47
  have h2 := kleC_48
  have h3 := leC_49
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_10 : (-212834426623831 / 1000000000000000 : ℝ) ≤ Real.log 51 * (ex (72426 / 100000) 51 * cCG cZ 51) + kappa * (Real.log 52 * (ex (72426 / 100000) 52 * cCG cZ 52)) - kappa * (Real.log 53 * (ex (72426 / 100000) 53 * cCG cZ 53)) - Real.log 54 * (ex (72426 / 100000) 54 * cCG cZ 54) ∧ Real.log 51 * (ex (72426 / 100000) 51 * cCG cZ 51) + kappa * (Real.log 52 * (ex (72426 / 100000) 52 * cCG cZ 52)) - kappa * (Real.log 53 * (ex (72426 / 100000) 53 * cCG cZ 53)) - Real.log 54 * (ex (72426 / 100000) 54 * cCG cZ 54) ≤ (-42566871546813 / 200000000000000 : ℝ) := by
  have h0 := leC_51
  have h1 := kleC_52
  have h2 := kleC_53
  have h3 := leC_54
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_11 : (120082426562397 / 1000000000000000 : ℝ) ≤ Real.log 56 * (ex (72426 / 100000) 56 * cCG cZ 56) + kappa * (Real.log 57 * (ex (72426 / 100000) 57 * cCG cZ 57)) - kappa * (Real.log 58 * (ex (72426 / 100000) 58 * cCG cZ 58)) - Real.log 59 * (ex (72426 / 100000) 59 * cCG cZ 59) ∧ Real.log 56 * (ex (72426 / 100000) 56 * cCG cZ 56) + kappa * (Real.log 57 * (ex (72426 / 100000) 57 * cCG cZ 57)) - kappa * (Real.log 58 * (ex (72426 / 100000) 58 * cCG cZ 58)) - Real.log 59 * (ex (72426 / 100000) 59 * cCG cZ 59) ≤ (120082500604747 / 1000000000000000 : ℝ) := by
  have h0 := leC_56
  have h1 := kleC_57
  have h2 := kleC_58
  have h3 := leC_59
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_12 : (-123675049270173 / 500000000000000 : ℝ) ≤ Real.log 61 * (ex (72426 / 100000) 61 * cCG cZ 61) + kappa * (Real.log 62 * (ex (72426 / 100000) 62 * cCG cZ 62)) - kappa * (Real.log 63 * (ex (72426 / 100000) 63 * cCG cZ 63)) - Real.log 64 * (ex (72426 / 100000) 64 * cCG cZ 64) ∧ Real.log 61 * (ex (72426 / 100000) 61 * cCG cZ 61) + kappa * (Real.log 62 * (ex (72426 / 100000) 62 * cCG cZ 62)) - kappa * (Real.log 63 * (ex (72426 / 100000) 63 * cCG cZ 63)) - Real.log 64 * (ex (72426 / 100000) 64 * cCG cZ 64) ≤ (-123674996340591 / 500000000000000 : ℝ) := by
  have h0 := leC_61
  have h1 := kleC_62
  have h2 := kleC_63
  have h3 := leC_64
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_13 : (-837117442959 / 15625000000000 : ℝ) ≤ Real.log 66 * (ex (72426 / 100000) 66 * cCG cZ 66) + kappa * (Real.log 67 * (ex (72426 / 100000) 67 * cCG cZ 67)) - kappa * (Real.log 68 * (ex (72426 / 100000) 68 * cCG cZ 68)) - Real.log 69 * (ex (72426 / 100000) 69 * cCG cZ 69) ∧ Real.log 66 * (ex (72426 / 100000) 66 * cCG cZ 66) + kappa * (Real.log 67 * (ex (72426 / 100000) 67 * cCG cZ 67)) - kappa * (Real.log 68 * (ex (72426 / 100000) 68 * cCG cZ 68)) - Real.log 69 * (ex (72426 / 100000) 69 * cCG cZ 69) ≤ (-26787694803849 / 500000000000000 : ℝ) := by
  have h0 := leC_66
  have h1 := kleC_67
  have h2 := kleC_68
  have h3 := leC_69
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_14 : (-1310473460809 / 62500000000000 : ℝ) ≤ Real.log 71 * (ex (72426 / 100000) 71 * cCG cZ 71) + kappa * (Real.log 72 * (ex (72426 / 100000) 72 * cCG cZ 72)) - kappa * (Real.log 73 * (ex (72426 / 100000) 73 * cCG cZ 73)) - Real.log 74 * (ex (72426 / 100000) 74 * cCG cZ 74) ∧ Real.log 71 * (ex (72426 / 100000) 71 * cCG cZ 71) + kappa * (Real.log 72 * (ex (72426 / 100000) 72 * cCG cZ 72)) - kappa * (Real.log 73 * (ex (72426 / 100000) 73 * cCG cZ 73)) - Real.log 74 * (ex (72426 / 100000) 74 * cCG cZ 74) ≤ (-5241859098781 / 250000000000000 : ℝ) := by
  have h0 := leC_71
  have h1 := kleC_72
  have h2 := kleC_73
  have h3 := leC_74
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_15 : (-5249667574593 / 1000000000000000 : ℝ) ≤ Real.log 76 * (ex (72426 / 100000) 76 * cCG cZ 76) + kappa * (Real.log 77 * (ex (72426 / 100000) 77 * cCG cZ 77)) - kappa * (Real.log 78 * (ex (72426 / 100000) 78 * cCG cZ 78)) - Real.log 79 * (ex (72426 / 100000) 79 * cCG cZ 79) ∧ Real.log 76 * (ex (72426 / 100000) 76 * cCG cZ 76) + kappa * (Real.log 77 * (ex (72426 / 100000) 77 * cCG cZ 77)) - kappa * (Real.log 78 * (ex (72426 / 100000) 78 * cCG cZ 78)) - Real.log 79 * (ex (72426 / 100000) 79 * cCG cZ 79) ≤ (-262476095121 / 50000000000000 : ℝ) := by
  have h0 := leC_76
  have h1 := kleC_77
  have h2 := kleC_78
  have h3 := leC_79
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_16 : (18022344767499 / 500000000000000 : ℝ) ≤ Real.log 81 * (ex (72426 / 100000) 81 * cCG cZ 81) + kappa * (Real.log 82 * (ex (72426 / 100000) 82 * cCG cZ 82)) - kappa * (Real.log 83 * (ex (72426 / 100000) 83 * cCG cZ 83)) - Real.log 84 * (ex (72426 / 100000) 84 * cCG cZ 84) ∧ Real.log 81 * (ex (72426 / 100000) 81 * cCG cZ 81) + kappa * (Real.log 82 * (ex (72426 / 100000) 82 * cCG cZ 82)) - kappa * (Real.log 83 * (ex (72426 / 100000) 83 * cCG cZ 83)) - Real.log 84 * (ex (72426 / 100000) 84 * cCG cZ 84) ≤ (9011209716247 / 250000000000000 : ℝ) := by
  have h0 := leC_81
  have h1 := kleC_82
  have h2 := kleC_83
  have h3 := leC_84
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_17 : (-61790148654979 / 500000000000000 : ℝ) ≤ Real.log 86 * (ex (72426 / 100000) 86 * cCG cZ 86) + kappa * (Real.log 87 * (ex (72426 / 100000) 87 * cCG cZ 87)) - kappa * (Real.log 88 * (ex (72426 / 100000) 88 * cCG cZ 88)) - Real.log 89 * (ex (72426 / 100000) 89 * cCG cZ 89) ∧ Real.log 86 * (ex (72426 / 100000) 86 * cCG cZ 86) + kappa * (Real.log 87 * (ex (72426 / 100000) 87 * cCG cZ 87)) - kappa * (Real.log 88 * (ex (72426 / 100000) 88 * cCG cZ 88)) - Real.log 89 * (ex (72426 / 100000) 89 * cCG cZ 89) ≤ (-123580147074321 / 1000000000000000 : ℝ) := by
  have h0 := leC_86
  have h1 := kleC_87
  have h2 := kleC_88
  have h3 := leC_89
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_18 : (9880431110071 / 62500000000000 : ℝ) ≤ Real.log 91 * (ex (72426 / 100000) 91 * cCG cZ 91) + kappa * (Real.log 92 * (ex (72426 / 100000) 92 * cCG cZ 92)) - kappa * (Real.log 93 * (ex (72426 / 100000) 93 * cCG cZ 93)) - Real.log 94 * (ex (72426 / 100000) 94 * cCG cZ 94) ∧ Real.log 91 * (ex (72426 / 100000) 91 * cCG cZ 91) + kappa * (Real.log 92 * (ex (72426 / 100000) 92 * cCG cZ 92)) - kappa * (Real.log 93 * (ex (72426 / 100000) 93 * cCG cZ 93)) - Real.log 94 * (ex (72426 / 100000) 94 * cCG cZ 94) ≤ (39521762044513 / 250000000000000 : ℝ) := by
  have h0 := leC_91
  have h1 := kleC_92
  have h2 := kleC_93
  have h3 := leC_94
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_19 : (-101004628967449 / 500000000000000 : ℝ) ≤ Real.log 96 * (ex (72426 / 100000) 96 * cCG cZ 96) + kappa * (Real.log 97 * (ex (72426 / 100000) 97 * cCG cZ 97)) - kappa * (Real.log 98 * (ex (72426 / 100000) 98 * cCG cZ 98)) - Real.log 99 * (ex (72426 / 100000) 99 * cCG cZ 99) ∧ Real.log 96 * (ex (72426 / 100000) 96 * cCG cZ 96) + kappa * (Real.log 97 * (ex (72426 / 100000) 97 * cCG cZ 97)) - kappa * (Real.log 98 * (ex (72426 / 100000) 98 * cCG cZ 98)) - Real.log 99 * (ex (72426 / 100000) 99 * cCG cZ 99) ≤ (-101004554255297 / 500000000000000 : ℝ) := by
  have h0 := leC_96
  have h1 := kleC_97
  have h2 := kleC_98
  have h3 := leC_99
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_20 : (114981980941319 / 500000000000000 : ℝ) ≤ Real.log 101 * (ex (72426 / 100000) 101 * cCG cZ 101) + kappa * (Real.log 102 * (ex (72426 / 100000) 102 * cCG cZ 102)) - kappa * (Real.log 103 * (ex (72426 / 100000) 103 * cCG cZ 103)) - Real.log 104 * (ex (72426 / 100000) 104 * cCG cZ 104) ∧ Real.log 101 * (ex (72426 / 100000) 101 * cCG cZ 101) + kappa * (Real.log 102 * (ex (72426 / 100000) 102 * cCG cZ 102)) - kappa * (Real.log 103 * (ex (72426 / 100000) 103 * cCG cZ 103)) - Real.log 104 * (ex (72426 / 100000) 104 * cCG cZ 104) ≤ (229964109981371 / 1000000000000000 : ℝ) := by
  have h0 := leC_101
  have h1 := kleC_102
  have h2 := kleC_103
  have h3 := leC_104
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_21 : (-13840490063491 / 200000000000000 : ℝ) ≤ Real.log 106 * (ex (72426 / 100000) 106 * cCG cZ 106) + kappa * (Real.log 107 * (ex (72426 / 100000) 107 * cCG cZ 107)) - kappa * (Real.log 108 * (ex (72426 / 100000) 108 * cCG cZ 108)) - Real.log 109 * (ex (72426 / 100000) 109 * cCG cZ 109) ∧ Real.log 106 * (ex (72426 / 100000) 106 * cCG cZ 106) + kappa * (Real.log 107 * (ex (72426 / 100000) 107 * cCG cZ 107)) - kappa * (Real.log 108 * (ex (72426 / 100000) 108 * cCG cZ 108)) - Real.log 109 * (ex (72426 / 100000) 109 * cCG cZ 109) ≤ (-69202303928017 / 1000000000000000 : ℝ) := by
  have h0 := leC_106
  have h1 := kleC_107
  have h2 := kleC_108
  have h3 := leC_109
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_22 : (-252823329328129 / 1000000000000000 : ℝ) ≤ Real.log 111 * (ex (72426 / 100000) 111 * cCG cZ 111) + kappa * (Real.log 112 * (ex (72426 / 100000) 112 * cCG cZ 112)) - kappa * (Real.log 113 * (ex (72426 / 100000) 113 * cCG cZ 113)) - Real.log 114 * (ex (72426 / 100000) 114 * cCG cZ 114) ∧ Real.log 111 * (ex (72426 / 100000) 111 * cCG cZ 111) + kappa * (Real.log 112 * (ex (72426 / 100000) 112 * cCG cZ 112)) - kappa * (Real.log 113 * (ex (72426 / 100000) 113 * cCG cZ 113)) - Real.log 114 * (ex (72426 / 100000) 114 * cCG cZ 114) ≤ (-252823184880369 / 1000000000000000 : ℝ) := by
  have h0 := leC_111
  have h1 := kleC_112
  have h2 := kleC_113
  have h3 := leC_114
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_23 : (80506511054531 / 1000000000000000 : ℝ) ≤ Real.log 116 * (ex (72426 / 100000) 116 * cCG cZ 116) + kappa * (Real.log 117 * (ex (72426 / 100000) 117 * cCG cZ 117)) - kappa * (Real.log 118 * (ex (72426 / 100000) 118 * cCG cZ 118)) - Real.log 119 * (ex (72426 / 100000) 119 * cCG cZ 119) ∧ Real.log 116 * (ex (72426 / 100000) 116 * cCG cZ 116) + kappa * (Real.log 117 * (ex (72426 / 100000) 117 * cCG cZ 117)) - kappa * (Real.log 118 * (ex (72426 / 100000) 118 * cCG cZ 118)) - Real.log 119 * (ex (72426 / 100000) 119 * cCG cZ 119) ≤ (2012666334407 / 25000000000000 : ℝ) := by
  have h0 := leC_116
  have h1 := kleC_117
  have h2 := kleC_118
  have h3 := leC_119
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_24 : (9186090134113 / 31250000000000 : ℝ) ≤ Real.log 121 * (ex (72426 / 100000) 121 * cCG cZ 121) + kappa * (Real.log 122 * (ex (72426 / 100000) 122 * cCG cZ 122)) - kappa * (Real.log 123 * (ex (72426 / 100000) 123 * cCG cZ 123)) - Real.log 124 * (ex (72426 / 100000) 124 * cCG cZ 124) ∧ Real.log 121 * (ex (72426 / 100000) 121 * cCG cZ 121) + kappa * (Real.log 122 * (ex (72426 / 100000) 122 * cCG cZ 122)) - kappa * (Real.log 123 * (ex (72426 / 100000) 123 * cCG cZ 123)) - Real.log 124 * (ex (72426 / 100000) 124 * cCG cZ 124) ≤ (293955024292319 / 1000000000000000 : ℝ) := by
  have h0 := leC_121
  have h1 := kleC_122
  have h2 := kleC_123
  have h3 := leC_124
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_25 : (255965252882069 / 1000000000000000 : ℝ) ≤ Real.log 126 * (ex (72426 / 100000) 126 * cCG cZ 126) + kappa * (Real.log 127 * (ex (72426 / 100000) 127 * cCG cZ 127)) - kappa * (Real.log 128 * (ex (72426 / 100000) 128 * cCG cZ 128)) - Real.log 129 * (ex (72426 / 100000) 129 * cCG cZ 129) ∧ Real.log 126 * (ex (72426 / 100000) 126 * cCG cZ 126) + kappa * (Real.log 127 * (ex (72426 / 100000) 127 * cCG cZ 127)) - kappa * (Real.log 128 * (ex (72426 / 100000) 128 * cCG cZ 128)) - Real.log 129 * (ex (72426 / 100000) 129 * cCG cZ 129) ≤ (255965390074531 / 1000000000000000 : ℝ) := by
  have h0 := leC_126
  have h1 := kleC_127
  have h2 := kleC_128
  have h3 := leC_129
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_26 : (70857519794673 / 500000000000000 : ℝ) ≤ Real.log 131 * (ex (72426 / 100000) 131 * cCG cZ 131) + kappa * (Real.log 132 * (ex (72426 / 100000) 132 * cCG cZ 132)) - kappa * (Real.log 133 * (ex (72426 / 100000) 133 * cCG cZ 133)) - Real.log 134 * (ex (72426 / 100000) 134 * cCG cZ 134) ∧ Real.log 131 * (ex (72426 / 100000) 131 * cCG cZ 131) + kappa * (Real.log 132 * (ex (72426 / 100000) 132 * cCG cZ 132)) - kappa * (Real.log 133 * (ex (72426 / 100000) 133 * cCG cZ 133)) - Real.log 134 * (ex (72426 / 100000) 134 * cCG cZ 134) ≤ (28343034782311 / 200000000000000 : ℝ) := by
  have h0 := leC_131
  have h1 := kleC_132
  have h2 := kleC_133
  have h3 := leC_134
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_27 : (32907979714019 / 500000000000000 : ℝ) ≤ Real.log 136 * (ex (72426 / 100000) 136 * cCG cZ 136) + kappa * (Real.log 137 * (ex (72426 / 100000) 137 * cCG cZ 137)) - kappa * (Real.log 138 * (ex (72426 / 100000) 138 * cCG cZ 138)) - Real.log 139 * (ex (72426 / 100000) 139 * cCG cZ 139) ∧ Real.log 136 * (ex (72426 / 100000) 136 * cCG cZ 136) + kappa * (Real.log 137 * (ex (72426 / 100000) 137 * cCG cZ 137)) - kappa * (Real.log 138 * (ex (72426 / 100000) 138 * cCG cZ 138)) - Real.log 139 * (ex (72426 / 100000) 139 * cCG cZ 139) ≤ (8227011365939 / 125000000000000 : ℝ) := by
  have h0 := leC_136
  have h1 := kleC_137
  have h2 := kleC_138
  have h3 := leC_139
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_28 : (454046298461 / 8000000000000 : ℝ) ≤ Real.log 141 * (ex (72426 / 100000) 141 * cCG cZ 141) + kappa * (Real.log 142 * (ex (72426 / 100000) 142 * cCG cZ 142)) - kappa * (Real.log 143 * (ex (72426 / 100000) 143 * cCG cZ 143)) - Real.log 144 * (ex (72426 / 100000) 144 * cCG cZ 144) ∧ Real.log 141 * (ex (72426 / 100000) 141 * cCG cZ 141) + kappa * (Real.log 142 * (ex (72426 / 100000) 142 * cCG cZ 142)) - kappa * (Real.log 143 * (ex (72426 / 100000) 143 * cCG cZ 143)) - Real.log 144 * (ex (72426 / 100000) 144 * cCG cZ 144) ≤ (11351183312919 / 200000000000000 : ℝ) := by
  have h0 := leC_141
  have h1 := kleC_142
  have h2 := kleC_143
  have h3 := leC_144
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_29 : (111383576555479 / 1000000000000000 : ℝ) ≤ Real.log 146 * (ex (72426 / 100000) 146 * cCG cZ 146) + kappa * (Real.log 147 * (ex (72426 / 100000) 147 * cCG cZ 147)) - kappa * (Real.log 148 * (ex (72426 / 100000) 148 * cCG cZ 148)) - Real.log 149 * (ex (72426 / 100000) 149 * cCG cZ 149) ∧ Real.log 146 * (ex (72426 / 100000) 146 * cCG cZ 146) + kappa * (Real.log 147 * (ex (72426 / 100000) 147 * cCG cZ 147)) - kappa * (Real.log 148 * (ex (72426 / 100000) 148 * cCG cZ 148)) - Real.log 149 * (ex (72426 / 100000) 149 * cCG cZ 149) ≤ (111383703383209 / 1000000000000000 : ℝ) := by
  have h0 := leC_146
  have h1 := kleC_147
  have h2 := kleC_148
  have h3 := leC_149
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_30 : (208751631458231 / 1000000000000000 : ℝ) ≤ Real.log 151 * (ex (72426 / 100000) 151 * cCG cZ 151) + kappa * (Real.log 152 * (ex (72426 / 100000) 152 * cCG cZ 152)) - kappa * (Real.log 153 * (ex (72426 / 100000) 153 * cCG cZ 153)) - Real.log 154 * (ex (72426 / 100000) 154 * cCG cZ 154) ∧ Real.log 151 * (ex (72426 / 100000) 151 * cCG cZ 151) + kappa * (Real.log 152 * (ex (72426 / 100000) 152 * cCG cZ 152)) - kappa * (Real.log 153 * (ex (72426 / 100000) 153 * cCG cZ 153)) - Real.log 154 * (ex (72426 / 100000) 154 * cCG cZ 154) ≤ (52187939085377 / 250000000000000 : ℝ) := by
  have h0 := leC_151
  have h1 := kleC_152
  have h2 := kleC_153
  have h3 := leC_154
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_31 : (289492972334211 / 1000000000000000 : ℝ) ≤ Real.log 156 * (ex (72426 / 100000) 156 * cCG cZ 156) + kappa * (Real.log 157 * (ex (72426 / 100000) 157 * cCG cZ 157)) - kappa * (Real.log 158 * (ex (72426 / 100000) 158 * cCG cZ 158)) - Real.log 159 * (ex (72426 / 100000) 159 * cCG cZ 159) ∧ Real.log 156 * (ex (72426 / 100000) 156 * cCG cZ 156) + kappa * (Real.log 157 * (ex (72426 / 100000) 157 * cCG cZ 157)) - kappa * (Real.log 158 * (ex (72426 / 100000) 158 * cCG cZ 158)) - Real.log 159 * (ex (72426 / 100000) 159 * cCG cZ 159) ≤ (144746547632073 / 500000000000000 : ℝ) := by
  have h0 := leC_156
  have h1 := kleC_157
  have h2 := kleC_158
  have h3 := leC_159
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_32 : (250851094097889 / 1000000000000000 : ℝ) ≤ Real.log 161 * (ex (72426 / 100000) 161 * cCG cZ 161) + kappa * (Real.log 162 * (ex (72426 / 100000) 162 * cCG cZ 162)) - kappa * (Real.log 163 * (ex (72426 / 100000) 163 * cCG cZ 163)) - Real.log 164 * (ex (72426 / 100000) 164 * cCG cZ 164) ∧ Real.log 161 * (ex (72426 / 100000) 161 * cCG cZ 161) + kappa * (Real.log 162 * (ex (72426 / 100000) 162 * cCG cZ 162)) - kappa * (Real.log 163 * (ex (72426 / 100000) 163 * cCG cZ 163)) - Real.log 164 * (ex (72426 / 100000) 164 * cCG cZ 164) ≤ (125425607411933 / 500000000000000 : ℝ) := by
  have h0 := leC_161
  have h1 := kleC_162
  have h2 := kleC_163
  have h3 := leC_164
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_33 : (3781607791989 / 125000000000000 : ℝ) ≤ Real.log 166 * (ex (72426 / 100000) 166 * cCG cZ 166) + kappa * (Real.log 167 * (ex (72426 / 100000) 167 * cCG cZ 167)) - kappa * (Real.log 168 * (ex (72426 / 100000) 168 * cCG cZ 168)) - Real.log 169 * (ex (72426 / 100000) 169 * cCG cZ 169) ∧ Real.log 166 * (ex (72426 / 100000) 166 * cCG cZ 166) + kappa * (Real.log 167 * (ex (72426 / 100000) 167 * cCG cZ 167)) - kappa * (Real.log 168 * (ex (72426 / 100000) 168 * cCG cZ 168)) - Real.log 169 * (ex (72426 / 100000) 169 * cCG cZ 169) ≤ (15126490444161 / 500000000000000 : ℝ) := by
  have h0 := leC_166
  have h1 := kleC_167
  have h2 := kleC_168
  have h3 := leC_169
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_34 : (-233581513826883 / 1000000000000000 : ℝ) ≤ Real.log 171 * (ex (72426 / 100000) 171 * cCG cZ 171) + kappa * (Real.log 172 * (ex (72426 / 100000) 172 * cCG cZ 172)) - kappa * (Real.log 173 * (ex (72426 / 100000) 173 * cCG cZ 173)) - Real.log 174 * (ex (72426 / 100000) 174 * cCG cZ 174) ∧ Real.log 171 * (ex (72426 / 100000) 171 * cCG cZ 171) + kappa * (Real.log 172 * (ex (72426 / 100000) 172 * cCG cZ 172)) - kappa * (Real.log 173 * (ex (72426 / 100000) 173 * cCG cZ 173)) - Real.log 174 * (ex (72426 / 100000) 174 * cCG cZ 174) ≤ (-1824854663141 / 7812500000000 : ℝ) := by
  have h0 := leC_171
  have h1 := kleC_172
  have h2 := kleC_173
  have h3 := leC_174
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_35 : (-44140965310861 / 200000000000000 : ℝ) ≤ Real.log 176 * (ex (72426 / 100000) 176 * cCG cZ 176) + kappa * (Real.log 177 * (ex (72426 / 100000) 177 * cCG cZ 177)) - kappa * (Real.log 178 * (ex (72426 / 100000) 178 * cCG cZ 178)) - Real.log 179 * (ex (72426 / 100000) 179 * cCG cZ 179) ∧ Real.log 176 * (ex (72426 / 100000) 176 * cCG cZ 176) + kappa * (Real.log 177 * (ex (72426 / 100000) 177 * cCG cZ 177)) - kappa * (Real.log 178 * (ex (72426 / 100000) 178 * cCG cZ 178)) - Real.log 179 * (ex (72426 / 100000) 179 * cCG cZ 179) ≤ (-55176177836271 / 250000000000000 : ℝ) := by
  have h0 := leC_176
  have h1 := kleC_177
  have h2 := kleC_178
  have h3 := leC_179
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_36 : (116309528557611 / 1000000000000000 : ℝ) ≤ Real.log 181 * (ex (72426 / 100000) 181 * cCG cZ 181) + kappa * (Real.log 182 * (ex (72426 / 100000) 182 * cCG cZ 182)) - kappa * (Real.log 183 * (ex (72426 / 100000) 183 * cCG cZ 183)) - Real.log 184 * (ex (72426 / 100000) 184 * cCG cZ 184) ∧ Real.log 181 * (ex (72426 / 100000) 181 * cCG cZ 181) + kappa * (Real.log 182 * (ex (72426 / 100000) 182 * cCG cZ 182)) - kappa * (Real.log 183 * (ex (72426 / 100000) 183 * cCG cZ 183)) - Real.log 184 * (ex (72426 / 100000) 184 * cCG cZ 184) ≤ (908669077779 / 7812500000000 : ℝ) := by
  have h0 := leC_181
  have h1 := kleC_182
  have h2 := kleC_183
  have h3 := leC_184
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_37 : (244965539501079 / 1000000000000000 : ℝ) ≤ Real.log 186 * (ex (72426 / 100000) 186 * cCG cZ 186) + kappa * (Real.log 187 * (ex (72426 / 100000) 187 * cCG cZ 187)) - kappa * (Real.log 188 * (ex (72426 / 100000) 188 * cCG cZ 188)) - Real.log 189 * (ex (72426 / 100000) 189 * cCG cZ 189) ∧ Real.log 186 * (ex (72426 / 100000) 186 * cCG cZ 186) + kappa * (Real.log 187 * (ex (72426 / 100000) 187 * cCG cZ 187)) - kappa * (Real.log 188 * (ex (72426 / 100000) 188 * cCG cZ 188)) - Real.log 189 * (ex (72426 / 100000) 189 * cCG cZ 189) ≤ (244965651471097 / 1000000000000000 : ℝ) := by
  have h0 := leC_186
  have h1 := kleC_187
  have h2 := kleC_188
  have h3 := leC_189
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_38 : (-2213559851501 / 20000000000000 : ℝ) ≤ Real.log 191 * (ex (72426 / 100000) 191 * cCG cZ 191) + kappa * (Real.log 192 * (ex (72426 / 100000) 192 * cCG cZ 192)) - kappa * (Real.log 193 * (ex (72426 / 100000) 193 * cCG cZ 193)) - Real.log 194 * (ex (72426 / 100000) 194 * cCG cZ 194) ∧ Real.log 191 * (ex (72426 / 100000) 191 * cCG cZ 191) + kappa * (Real.log 192 * (ex (72426 / 100000) 192 * cCG cZ 192)) - kappa * (Real.log 193 * (ex (72426 / 100000) 193 * cCG cZ 193)) - Real.log 194 * (ex (72426 / 100000) 194 * cCG cZ 194) ≤ (-6917367647053 / 62500000000000 : ℝ) := by
  have h0 := leC_191
  have h1 := kleC_192
  have h2 := kleC_193
  have h3 := leC_194
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_39 : (-102308334994227 / 500000000000000 : ℝ) ≤ Real.log 196 * (ex (72426 / 100000) 196 * cCG cZ 196) + kappa * (Real.log 197 * (ex (72426 / 100000) 197 * cCG cZ 197)) - kappa * (Real.log 198 * (ex (72426 / 100000) 198 * cCG cZ 198)) - Real.log 199 * (ex (72426 / 100000) 199 * cCG cZ 199) ∧ Real.log 196 * (ex (72426 / 100000) 196 * cCG cZ 196) + kappa * (Real.log 197 * (ex (72426 / 100000) 197 * cCG cZ 197)) - kappa * (Real.log 198 * (ex (72426 / 100000) 198 * cCG cZ 198)) - Real.log 199 * (ex (72426 / 100000) 199 * cCG cZ 199) ≤ (-10230828060517 / 50000000000000 : ℝ) := by
  have h0 := leC_196
  have h1 := kleC_197
  have h2 := kleC_198
  have h3 := leC_199
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_40 : (39155039342413 / 200000000000000 : ℝ) ≤ Real.log 201 * (ex (72426 / 100000) 201 * cCG cZ 201) + kappa * (Real.log 202 * (ex (72426 / 100000) 202 * cCG cZ 202)) - kappa * (Real.log 203 * (ex (72426 / 100000) 203 * cCG cZ 203)) - Real.log 204 * (ex (72426 / 100000) 204 * cCG cZ 204) ∧ Real.log 201 * (ex (72426 / 100000) 201 * cCG cZ 201) + kappa * (Real.log 202 * (ex (72426 / 100000) 202 * cCG cZ 202)) - kappa * (Real.log 203 * (ex (72426 / 100000) 203 * cCG cZ 203)) - Real.log 204 * (ex (72426 / 100000) 204 * cCG cZ 204) ≤ (97887652055377 / 500000000000000 : ℝ) := by
  have h0 := leC_201
  have h1 := kleC_202
  have h2 := kleC_203
  have h3 := leC_204
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReT_1 : (-174798476503 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 206 * (cCG cZ 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (72426 / 100000) 206 * (cCG cZ 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-43697991817 / 250000000000000 : ℝ) := by
  have hc := cCB_206
  have hs := sCB_206
  have hin : (-258957883993 / 31250000000000 : ℝ) ≤ cCG cZ 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-12947412059 / 1562500000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-174798476503 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 206 * (cCG cZ 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (72426 / 100000) 206 * (cCG cZ 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-43697991817 / 250000000000000 : ℝ) :=
    mul_bounds_of exB_206 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem PReT_2 : (2718772004877 / 1000000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 207 * (cCG cZ 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (72426 / 100000) 207 * (cCG cZ 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (2718773833767 / 1000000000000000 : ℝ) := by
  have hc := cCB_207
  have hs := sCB_207
  have hin : (455300654630561 / 1000000000000000 : ℝ) ≤ cCG cZ 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (11382524005437 / 25000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (4785238587337 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 207 * (cCG cZ 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (72426 / 100000) 207 * (cCG cZ 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (9570483612631 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_207 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PReT_3 : (885110731273 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 208 * (cCG cZ 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (72426 / 100000) 208 * (cCG cZ 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (3540444729091 / 1000000000000000 : ℝ) := by
  have hc := cCB_208
  have hs := sCB_208
  have hin : (297487660199873 / 500000000000000 : ℝ) ≤ cCG cZ 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (74371952832899 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (1246287961699 / 100000000000000 : ℝ) ≤ ex (72426 / 100000) 208 * (cCG cZ 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (72426 / 100000) 208 * (cCG cZ 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (12462885967327 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_208 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PReT_4 : (6745444862979 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 209 * (cCG cZ 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (72426 / 100000) 209 * (cCG cZ 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (42159069569 / 6250000000000 : ℝ) := by
  have hc := cCB_209
  have hs := sCB_209
  have hin : (64629343154519 / 200000000000000 : ℝ) ≤ cCG cZ 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (323147015560773 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (6745444862979 / 1000000000000000 : ℝ) ≤ ex (72426 / 100000) 209 * (cCG cZ 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (72426 / 100000) 209 * (cCG cZ 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sCG cZ 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (42159069569 / 6250000000000 : ℝ) :=
    mul_bounds_of exB_209 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem PImT_1 : (3213557367599 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 206 * (cCG cZ 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (72426 / 100000) 206 * (cCG cZ 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (12854235998819 / 1000000000000000 : ℝ) := by
  have hc := cCB_206
  have hs := sCB_206
  have hin : (609379053759953 / 1000000000000000 : ℝ) ≤ cCG cZ 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (304689681165111 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (3213557367599 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 206 * (cCG cZ 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (72426 / 100000) 206 * (cCG cZ 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (12854235998819 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_206 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem PImT_2 : (476071080661 / 200000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 207 * (cCG cZ 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (72426 / 100000) 207 * (cCG cZ 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (2380357231683 / 1000000000000000 : ℝ) := by
  have hc := cCB_207
  have hs := sCB_207
  have hin : (199313765816713 / 500000000000000 : ℝ) ≤ cCG cZ 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (199313918610173 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (4189600491339 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 207 * (cCG cZ 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (72426 / 100000) 207 * (cCG cZ 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (523700463677 / 62500000000000 : ℝ) :=
    mul_bounds_of exB_207 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PImT_3 : (-126494686269 / 250000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 208 * (cCG cZ 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (72426 / 100000) 208 * (cCG cZ 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-126494236423 / 250000000000000 : ℝ) := by
  have hc := cCB_208
  have hs := sCB_208
  have hin : (-85030283464703 / 1000000000000000 : ℝ) ≤ cCG cZ 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-8502998120519 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-89055978617 / 50000000000000 : ℝ) ≤ ex (72426 / 100000) 208 * (cCG cZ 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (72426 / 100000) 208 * (cCG cZ 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-222639154781 / 125000000000000 : ℝ) :=
    mul_bounds_of exB_208 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PImT_4 : (-654982443293 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 209 * (cCG cZ 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (72426 / 100000) 209 * (cCG cZ 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-327491025593 / 31250000000000 : ℝ) := by
  have hc := cCB_209
  have hs := sCB_209
  have hin : (-62755067877041 / 125000000000000 : ℝ) ≤ cCG cZ 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cCG cZ 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-10040804864563 / 20000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-654982443293 / 62500000000000 : ℝ) ≤ ex (72426 / 100000) 209 * (cCG cZ 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (72426 / 100000) 209 * (cCG cZ 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sCG cZ 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-327491025593 / 31250000000000 : ℝ) :=
    mul_bounds_of exB_209 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem AReT_1 : (517624387671 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 206 * (cCG cZ 206 * ((2751069837930832398472515390961158274618237700014485879447976907186791028182934433507177830169405697147297778533687185016608925708152693437419344342819770907678370097787484226859403 / 323761285901854881562389627221823261560600727118623577151214228751432550293953268513568194560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 206 * ((-8272482432948381899032748341574685254374016046065384031403647369750383855466099592253799923436852123273301268809189738304052956561975367871611057050319309599077271409945461225679791 / 12950451436074195262495585088872930462424029084744943086048569150057302011758130740542727782400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (72426 / 100000) 206 * (cCG cZ 206 * ((2751069837930832398472515390961158274618237700014485879447976907186791028182934433507177830169405697147297778533687185016608925708152693437419344342819770907678370097787484226859403 / 323761285901854881562389627221823261560600727118623577151214228751432550293953268513568194560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 206 * ((-8272482432948381899032748341574685254374016046065384031403647369750383855466099592253799923436852123273301268809189738304052956561975367871611057050319309599077271409945461225679791 / 12950451436074195262495585088872930462424029084744943086048569150057302011758130740542727782400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (258820854673 / 250000000000000 : ℝ) := by
  have hc := cCB_206
  have hs := sCB_206
  have hl := lgB_206
  have hv1 : (-1375201213246279 / 500000000000000 : ℝ) ≤ (2751069837930832398472515390961158274618237700014485879447976907186791028182934433507177830169405697147297778533687185016608925708152693437419344342819770907678370097787484226859403 / 323761285901854881562389627221823261560600727118623577151214228751432550293953268513568194560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (2751069837930832398472515390961158274618237700014485879447976907186791028182934433507177830169405697147297778533687185016608925708152693437419344342819770907678370097787484226859403 / 323761285901854881562389627221823261560600727118623577151214228751432550293953268513568194560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-550080485083511 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-856395187979899 / 500000000000000 : ℝ) ≤ (-8272482432948381899032748341574685254374016046065384031403647369750383855466099592253799923436852123273301268809189738304052956561975367871611057050319309599077271409945461225679791 / 12950451436074195262495585088872930462424029084744943086048569150057302011758130740542727782400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-8272482432948381899032748341574685254374016046065384031403647369750383855466099592253799923436852123273301268809189738304052956561975367871611057050319309599077271409945461225679791 / 12950451436074195262495585088872930462424029084744943086048569150057302011758130740542727782400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1712790375292659 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (-354596633881219 / 250000000000000 : ℝ) ≤ cCG cZ 206 * ((2751069837930832398472515390961158274618237700014485879447976907186791028182934433507177830169405697147297778533687185016608925708152693437419344342819770907678370097787484226859403 / 323761285901854881562389627221823261560600727118623577151214228751432550293953268513568194560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 206 * ((2751069837930832398472515390961158274618237700014485879447976907186791028182934433507177830169405697147297778533687185016608925708152693437419344342819770907678370097787484226859403 / 323761285901854881562389627221823261560600727118623577151214228751432550293953268513568194560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-283677104727647 / 200000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (1467464461243967 / 1000000000000000 : ℝ) ≤ sCG cZ 206 * ((-8272482432948381899032748341574685254374016046065384031403647369750383855466099592253799923436852123273301268809189738304052956561975367871611057050319309599077271409945461225679791 / 12950451436074195262495585088872930462424029084744943086048569150057302011758130740542727782400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sCG cZ 206 * ((-8272482432948381899032748341574685254374016046065384031403647369750383855466099592253799923436852123273301268809189738304052956561975367871611057050319309599077271409945461225679791 / 12950451436074195262495585088872930462424029084744943086048569150057302011758130740542727782400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (1467465091616551 / 1000000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (49077925719091 / 1000000000000000 : ℝ) ≤ cCG cZ 206 * ((2751069837930832398472515390961158274618237700014485879447976907186791028182934433507177830169405697147297778533687185016608925708152693437419344342819770907678370097787484226859403 / 323761285901854881562389627221823261560600727118623577151214228751432550293953268513568194560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 206 * ((-8272482432948381899032748341574685254374016046065384031403647369750383855466099592253799923436852123273301268809189738304052956561975367871611057050319309599077271409945461225679791 / 12950451436074195262495585088872930462424029084744943086048569150057302011758130740542727782400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 206 * ((2751069837930832398472515390961158274618237700014485879447976907186791028182934433507177830169405697147297778533687185016608925708152693437419344342819770907678370097787484226859403 / 323761285901854881562389627221823261560600727118623577151214228751432550293953268513568194560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 206 * ((-8272482432948381899032748341574685254374016046065384031403647369750383855466099592253799923436852123273301268809189738304052956561975367871611057050319309599077271409945461225679791 / 12950451436074195262495585088872930462424029084744943086048569150057302011758130740542727782400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (12269891994579 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (517624387671 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 206 * (cCG cZ 206 * ((2751069837930832398472515390961158274618237700014485879447976907186791028182934433507177830169405697147297778533687185016608925708152693437419344342819770907678370097787484226859403 / 323761285901854881562389627221823261560600727118623577151214228751432550293953268513568194560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 206 * ((-8272482432948381899032748341574685254374016046065384031403647369750383855466099592253799923436852123273301268809189738304052956561975367871611057050319309599077271409945461225679791 / 12950451436074195262495585088872930462424029084744943086048569150057302011758130740542727782400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (72426 / 100000) 206 * (cCG cZ 206 * ((2751069837930832398472515390961158274618237700014485879447976907186791028182934433507177830169405697147297778533687185016608925708152693437419344342819770907678370097787484226859403 / 323761285901854881562389627221823261560600727118623577151214228751432550293953268513568194560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (1177969964415150241015944478119362570531683472249641713848474056599862915950465201422275564362975948953533000818385924156461487146474789362599160083053078958318042830204623 / 2274848278060601348045716402654724200670657559173699504192473005824315228160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 206 * ((-8272482432948381899032748341574685254374016046065384031403647369750383855466099592253799923436852123273301268809189738304052956561975367871611057050319309599077271409945461225679791 / 12950451436074195262495585088872930462424029084744943086048569150057302011758130740542727782400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 206 * (14919162665123047473785204754140513381892481006017754177061024450055805689269190723952580702695935383776259409865275110007752694674520851260260115415626752208383943005943 / 46425475062461252000932987809280085727972603248442847024336183792332963840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (258820854673 / 250000000000000 : ℝ) :=
    mul_bounds_of exB_206 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem AReT_2 : (-1806089071923 / 125000000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 207 * (cCG cZ 207 * ((103758810518002895055343348715536103734340409493437369216912863689537720973204702290082847486236025735278606324137094638158444778045494442027972331654241863855949088331365071838839503 / 12425468230962787409602870910925813612994448332199492741918903221683608531902945184634422378880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 207 * ((-39446272474287368282318951145258276271084307934736114237866296312596351489735060608772428920820658502831784791635882914962947471837156538202312469111437048028045386938230230706305151 / 64828529900675412571841065622221636241710165211475614305663842895740566253406670528527421107200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ∧ kappa * (ex (72426 / 100000) 207 * (cCG cZ 207 * ((103758810518002895055343348715536103734340409493437369216912863689537720973204702290082847486236025735278606324137094638158444778045494442027972331654241863855949088331365071838839503 / 12425468230962787409602870910925813612994448332199492741918903221683608531902945184634422378880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 207 * ((-39446272474287368282318951145258276271084307934736114237866296312596351489735060608772428920820658502831784791635882914962947471837156538202312469111437048028045386938230230706305151 / 64828529900675412571841065622221636241710165211475614305663842895740566253406670528527421107200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ≤ (-14448702832517 / 1000000000000000 : ℝ) := by
  have hc := cCB_207
  have hs := sCB_207
  have hl := lgB_207
  have hv1 : (-549954174068373 / 200000000000000 : ℝ) ≤ (103758810518002895055343348715536103734340409493437369216912863689537720973204702290082847486236025735278606324137094638158444778045494442027972331654241863855949088331365071838839503 / 12425468230962787409602870910925813612994448332199492741918903221683608531902945184634422378880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (103758810518002895055343348715536103734340409493437369216912863689537720973204702290082847486236025735278606324137094638158444778045494442027972331654241863855949088331365071838839503 / 12425468230962787409602870910925813612994448332199492741918903221683608531902945184634422378880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-2749770869268141 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-67038402771683 / 40000000000000 : ℝ) ≤ (-39446272474287368282318951145258276271084307934736114237866296312596351489735060608772428920820658502831784791635882914962947471837156538202312469111437048028045386938230230706305151 / 64828529900675412571841065622221636241710165211475614305663842895740566253406670528527421107200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-39446272474287368282318951145258276271084307934736114237866296312596351489735060608772428920820658502831784791635882914962947471837156538202312469111437048028045386938230230706305151 / 64828529900675412571841065622221636241710165211475614305663842895740566253406670528527421107200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-418990017159967 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (-541719722710271 / 200000000000000 : ℝ) ≤ cCG cZ 207 * ((103758810518002895055343348715536103734340409493437369216912863689537720973204702290082847486236025735278606324137094638158444778045494442027972331654241863855949088331365071838839503 / 12425468230962787409602870910925813612994448332199492741918903221683608531902945184634422378880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 207 * ((103758810518002895055343348715536103734340409493437369216912863689537720973204702290082847486236025735278606324137094638158444778045494442027972331654241863855949088331365071838839503 / 12425468230962787409602870910925813612994448332199492741918903221683608531902945184634422378880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-2708597601762013 / 1000000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (11557479588253 / 40000000000000 : ℝ) ≤ sCG cZ 207 * ((-39446272474287368282318951145258276271084307934736114237866296312596351489735060608772428920820658502831784791635882914962947471837156538202312469111437048028045386938230230706305151 / 64828529900675412571841065622221636241710165211475614305663842895740566253406670528527421107200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sCG cZ 207 * ((-39446272474287368282318951145258276271084307934736114237866296312596351489735060608772428920820658502831784791635882914962947471837156538202312469111437048028045386938230230706305151 / 64828529900675412571841065622221636241710165211475614305663842895740566253406670528527421107200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (72234401462611 / 250000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (-241966162384503 / 100000000000000 : ℝ) ≤ cCG cZ 207 * ((103758810518002895055343348715536103734340409493437369216912863689537720973204702290082847486236025735278606324137094638158444778045494442027972331654241863855949088331365071838839503 / 12425468230962787409602870910925813612994448332199492741918903221683608531902945184634422378880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 207 * ((-39446272474287368282318951145258276271084307934736114237866296312596351489735060608772428920820658502831784791635882914962947471837156538202312469111437048028045386938230230706305151 / 64828529900675412571841065622221636241710165211475614305663842895740566253406670528527421107200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 207 * ((103758810518002895055343348715536103734340409493437369216912863689537720973204702290082847486236025735278606324137094638158444778045494442027972331654241863855949088331365071838839503 / 12425468230962787409602870910925813612994448332199492741918903221683608531902945184634422378880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 207 * ((-39446272474287368282318951145258276271084307934736114237866296312596351489735060608772428920820658502831784791635882914962947471837156538202312469111437048028045386938230230706305151 / 64828529900675412571841065622221636241710165211475614305663842895740566253406670528527421107200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-2419659995911569 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (-25430796267219 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 207 * (cCG cZ 207 * ((103758810518002895055343348715536103734340409493437369216912863689537720973204702290082847486236025735278606324137094638158444778045494442027972331654241863855949088331365071838839503 / 12425468230962787409602870910925813612994448332199492741918903221683608531902945184634422378880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 207 * ((-39446272474287368282318951145258276271084307934736114237866296312596351489735060608772428920820658502831784791635882914962947471837156538202312469111437048028045386938230230706305151 / 64828529900675412571841065622221636241710165211475614305663842895740566253406670528527421107200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (72426 / 100000) 207 * (cCG cZ 207 * ((103758810518002895055343348715536103734340409493437369216912863689537720973204702290082847486236025735278606324137094638158444778045494442027972331654241863855949088331365071838839503 / 12425468230962787409602870910925813612994448332199492741918903221683608531902945184634422378880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (5889770760156267689232328181846267152040091533101892072034873293781142142200592347487284676720463862906232235768078957469301319912713765145072536464008421351654495022220703 / 11387639291318582629166251862486662605518837934053419701413626511144897268480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 207 * ((-39446272474287368282318951145258276271084307934736114237866296312596351489735060608772428920820658502831784791635882914962947471837156538202312469111437048028045386938230230706305151 / 64828529900675412571841065622221636241710165211475614305663842895740566253406670528527421107200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 207 * (559759515207962300527890503067976035509626197651226950382999020545571118159662381706581151926283780925465613244169109089305728188695392586772940842183213023295364043204043 / 1781739480954608166468189066919681904264852193763460225391247685417228824320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-10172311647623 / 200000000000000 : ℝ) :=
    mul_bounds_of exB_207 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem AReT_3 : (-1178836659761 / 62500000000000 : ℝ) ≤ kappa * (ex (72426 / 100000) 208 * (cCG cZ 208 * ((341897602941619997563896845975777719816096854767973417775546926699391872015668610259686971665782249345257113247144570733035903550215871095871578971229092570464112247477929358766518509 / 41645950314961045721967350738823584118721333801106606477187355548534727735458339146686015733760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 208 * ((-74324267607574564798628926638114743824004805307345973256290266258744097221283545754707587343768966279670455010631471005508320614952395374429186570856838044180471080054970715865001421 / 128141385584495525298361079196380258826834873234174173775961093995491469955256428143649279180800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ∧ kappa * (ex (72426 / 100000) 208 * (cCG cZ 208 * ((341897602941619997563896845975777719816096854767973417775546926699391872015668610259686971665782249345257113247144570733035903550215871095871578971229092570464112247477929358766518509 / 41645950314961045721967350738823584118721333801106606477187355548534727735458339146686015733760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 208 * ((-74324267607574564798628926638114743824004805307345973256290266258744097221283545754707587343768966279670455010631471005508320614952395374429186570856838044180471080054970715865001421 / 128141385584495525298361079196380258826834873234174173775961093995491469955256428143649279180800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ≤ (-3772275387327 / 200000000000000 : ℝ) := by
  have hc := cCB_208
  have hs := sCB_208
  have hl := lgB_208
  have hv1 : (-2749279398112633 / 1000000000000000 : ℝ) ≤ (341897602941619997563896845975777719816096854767973417775546926699391872015668610259686971665782249345257113247144570733035903550215871095871578971229092570464112247477929358766518509 / 41645950314961045721967350738823584118721333801106606477187355548534727735458339146686015733760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (341897602941619997563896845975777719816096854767973417775546926699391872015668610259686971665782249345257113247144570733035903550215871095871578971229092570464112247477929358766518509 / 41645950314961045721967350738823584118721333801106606477187355548534727735458339146686015733760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-21994235176321 / 8000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-327977738918431 / 200000000000000 : ℝ) ≤ (-74324267607574564798628926638114743824004805307345973256290266258744097221283545754707587343768966279670455010631471005508320614952395374429186570856838044180471080054970715865001421 / 128141385584495525298361079196380258826834873234174173775961093995491469955256428143649279180800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-74324267607574564798628926638114743824004805307345973256290266258744097221283545754707587343768966279670455010631471005508320614952395374429186570856838044180471080054970715865001421 / 128141385584495525298361079196380258826834873234174173775961093995491469955256428143649279180800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-409972173488639 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (-2140678384229289 / 1000000000000000 : ℝ) ≤ cCG cZ 208 * ((341897602941619997563896845975777719816096854767973417775546926699391872015668610259686971665782249345257113247144570733035903550215871095871578971229092570464112247477929358766518509 / 41645950314961045721967350738823584118721333801106606477187355548534727735458339146686015733760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 208 * ((341897602941619997563896845975777719816096854767973417775546926699391872015668610259686971665782249345257113247144570733035903550215871095871578971229092570464112247477929358766518509 / 41645950314961045721967350738823584118721333801106606477187355548534727735458339146686015733760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-1070338687282907 / 500000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (-514499164256987 / 500000000000000 : ℝ) ≤ sCG cZ 208 * ((-74324267607574564798628926638114743824004805307345973256290266258744097221283545754707587343768966279670455010631471005508320614952395374429186570856838044180471080054970715865001421 / 128141385584495525298361079196380258826834873234174173775961093995491469955256428143649279180800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sCG cZ 208 * ((-74324267607574564798628926638114743824004805307345973256290266258744097221283545754707587343768966279670455010631471005508320614952395374429186570856838044180471080054970715865001421 / 128141385584495525298361079196380258826834873234174173775961093995491469955256428143649279180800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-102899772639927 / 100000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (-3169676712743263 / 1000000000000000 : ℝ) ≤ cCG cZ 208 * ((341897602941619997563896845975777719816096854767973417775546926699391872015668610259686971665782249345257113247144570733035903550215871095871578971229092570464112247477929358766518509 / 41645950314961045721967350738823584118721333801106606477187355548534727735458339146686015733760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 208 * ((-74324267607574564798628926638114743824004805307345973256290266258744097221283545754707587343768966279670455010631471005508320614952395374429186570856838044180471080054970715865001421 / 128141385584495525298361079196380258826834873234174173775961093995491469955256428143649279180800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 208 * ((341897602941619997563896845975777719816096854767973417775546926699391872015668610259686971665782249345257113247144570733035903550215871095871578971229092570464112247477929358766518509 / 41645950314961045721967350738823584118721333801106606477187355548534727735458339146686015733760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 208 * ((-74324267607574564798628926638114743824004805307345973256290266258744097221283545754707587343768966279670455010631471005508320614952395374429186570856838044180471080054970715865001421 / 128141385584495525298361079196380258826834873234174173775961093995491469955256428143649279180800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-792418775241271 / 250000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (-16598713426017 / 250000000000000 : ℝ) ≤ ex (72426 / 100000) 208 * (cCG cZ 208 * ((341897602941619997563896845975777719816096854767973417775546926699391872015668610259686971665782249345257113247144570733035903550215871095871578971229092570464112247477929358766518509 / 41645950314961045721967350738823584118721333801106606477187355548534727735458339146686015733760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 208 * ((-74324267607574564798628926638114743824004805307345973256290266258744097221283545754707587343768966279670455010631471005508320614952395374429186570856838044180471080054970715865001421 / 128141385584495525298361079196380258826834873234174173775961093995491469955256428143649279180800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (72426 / 100000) 208 * (cCG cZ 208 * ((341897602941619997563896845975777719816096854767973417775546926699391872015668610259686971665782249345257113247144570733035903550215871095871578971229092570464112247477929358766518509 / 41645950314961045721967350738823584118721333801106606477187355548534727735458339146686015733760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (11628662072659997551156081585911985935860472759308441976299508897471366952350787634941732695260097776399053113850211061490476808033531657557889922530515376089626273500852013 / 22509038529204762612134080302007771425345571744379137717750529738089923870720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 208 * ((-74324267607574564798628926638114743824004805307345973256290266258744097221283545754707587343768966279670455010631471005508320614952395374429186570856838044180471080054970715865001421 / 128141385584495525298361079196380258826834873234174173775961093995491469955256428143649279180800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 208 * (12838728291740559147883431457244226461730370492501232601332759694218336395101672607652800069800703850999239191265648408930511260482295306934870126620690074174886654907284903 / 41802500125665987708249006275157289789927490382418398618679555227881287188480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-4149676240117 / 62500000000000 : ℝ) :=
    mul_bounds_of exB_208 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaBG he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem AReT_4 : (-18020206204547 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 209 * (cCG cZ 209 * ((16325175332040874435655137608160298662466362669093912995256327912512000256775997690373966537975557641764890239720364765542802933483389242989248711964541070064239538831461448048544283 / 2021868085151148351536557997311618421046061110755895069147999838411102672471286390349009191040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 209 * ((-1029175611193268216811073362133505716052701121867797123490790162117255671418866641484464776078197609793637298515666206607084565458500678009305028503328344039577908851430354506245018473 / 1860118638339056483413633357526688947362376221895423463616159851338214458673583479121088455756800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (72426 / 100000) 209 * (cCG cZ 209 * ((16325175332040874435655137608160298662466362669093912995256327912512000256775997690373966537975557641764890239720364765542802933483389242989248711964541070064239538831461448048544283 / 2021868085151148351536557997311618421046061110755895069147999838411102672471286390349009191040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 209 * ((-1029175611193268216811073362133505716052701121867797123490790162117255671418866641484464776078197609793637298515666206607084565458500678009305028503328344039577908851430354506245018473 / 1860118638339056483413633357526688947362376221895423463616159851338214458673583479121088455756800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-7208075793333 / 200000000000000 : ℝ) := by
  have hc := cCB_209
  have hs := sCB_209
  have hl := lgB_209
  have hv1 : (-1374459277202357 / 500000000000000 : ℝ) ≤ (16325175332040874435655137608160298662466362669093912995256327912512000256775997690373966537975557641764890239720364765542802933483389242989248711964541070064239538831461448048544283 / 2021868085151148351536557997311618421046061110755895069147999838411102672471286390349009191040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (16325175332040874435655137608160298662466362669093912995256327912512000256775997690373966537975557641764890239720364765542802933483389242989248711964541070064239538831461448048544283 / 2021868085151148351536557997311618421046061110755895069147999838411102672471286390349009191040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1374459276666681 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-2507102256169 / 1562500000000 : ℝ) ≤ (-1029175611193268216811073362133505716052701121867797123490790162117255671418866641484464776078197609793637298515666206607084565458500678009305028503328344039577908851430354506245018473 / 1860118638339056483413633357526688947362376221895423463616159851338214458673583479121088455756800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-1029175611193268216811073362133505716052701121867797123490790162117255671418866641484464776078197609793637298515666206607084565458500678009305028503328344039577908851430354506245018473 / 1860118638339056483413633357526688947362376221895423463616159851338214458673583479121088455756800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1604545443324857 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (-123626682501013 / 1000000000000000 : ℝ) ≤ cCG cZ 209 * ((16325175332040874435655137608160298662466362669093912995256327912512000256775997690373966537975557641764890239720364765542802933483389242989248711964541070064239538831461448048544283 / 2021868085151148351536557997311618421046061110755895069147999838411102672471286390349009191040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 209 * ((16325175332040874435655137608160298662466362669093912995256327912512000256775997690373966537975557641764890239720364765542802933483389242989248711964541070064239538831461448048544283 / 2021868085151148351536557997311618421046061110755895069147999838411102672471286390349009191040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-61812836457223 / 500000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (-801461144275481 / 500000000000000 : ℝ) ≤ sCG cZ 209 * ((-1029175611193268216811073362133505716052701121867797123490790162117255671418866641484464776078197609793637298515666206607084565458500678009305028503328344039577908851430354506245018473 / 1860118638339056483413633357526688947362376221895423463616159851338214458673583479121088455756800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sCG cZ 209 * ((-1029175611193268216811073362133505716052701121867797123490790162117255671418866641484464776078197609793637298515666206607084565458500678009305028503328344039577908851430354506245018473 / 1860118638339056483413633357526688947362376221895423463616159851338214458673583479121088455756800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-320584339732023 / 200000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (-69061958842079 / 40000000000000 : ℝ) ≤ cCG cZ 209 * ((16325175332040874435655137608160298662466362669093912995256327912512000256775997690373966537975557641764890239720364765542802933483389242989248711964541070064239538831461448048544283 / 2021868085151148351536557997311618421046061110755895069147999838411102672471286390349009191040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 209 * ((-1029175611193268216811073362133505716052701121867797123490790162117255671418866641484464776078197609793637298515666206607084565458500678009305028503328344039577908851430354506245018473 / 1860118638339056483413633357526688947362376221895423463616159851338214458673583479121088455756800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cCG cZ 209 * ((16325175332040874435655137608160298662466362669093912995256327912512000256775997690373966537975557641764890239720364765542802933483389242989248711964541070064239538831461448048544283 / 2021868085151148351536557997311618421046061110755895069147999838411102672471286390349009191040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 209 * ((-1029175611193268216811073362133505716052701121867797123490790162117255671418866641484464776078197609793637298515666206607084565458500678009305028503328344039577908851430354506245018473 / 1860118638339056483413633357526688947362376221895423463616159851338214458673583479121088455756800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-1726547371574561 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (-18020206204547 / 500000000000000 : ℝ) ≤ ex (72426 / 100000) 209 * (cCG cZ 209 * ((16325175332040874435655137608160298662466362669093912995256327912512000256775997690373966537975557641764890239720364765542802933483389242989248711964541070064239538831461448048544283 / 2021868085151148351536557997311618421046061110755895069147999838411102672471286390349009191040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 209 * ((-1029175611193268216811073362133505716052701121867797123490790162117255671418866641484464776078197609793637298515666206607084565458500678009305028503328344039577908851430354506245018473 / 1860118638339056483413633357526688947362376221895423463616159851338214458673583479121088455756800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (72426 / 100000) 209 * (cCG cZ 209 * ((16325175332040874435655137608160298662466362669093912995256327912512000256775997690373966537975557641764890239720364765542802933483389242989248711964541070064239538831461448048544283 / 2021868085151148351536557997311618421046061110755895069147999838411102672471286390349009191040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (168621425800419504631008303040667288250730249649326731048911776494158019019634500990516372731372155922651729486963043329540374847363822147884358892968093967738022921511076169 / 326744415227641507738847856046563137488030922123650286721155520682158024549120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sCG cZ 209 * ((-1029175611193268216811073362133505716052701121867797123490790162117255671418866641484464776078197609793637298515666206607084565458500678009305028503328344039577908851430354506245018473 / 1860118638339056483413633357526688947362376221895423463616159851338214458673583479121088455756800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 209 * (14014619697494028848787154158492734271227127197322336144232111348858122551388153869046788417646688844788085141029453138977542552849315820618298293620294807999296852907284903 / 46677773603948786819835408006651876784004417446235755245879360097451146364160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-7208075793333 / 200000000000000 : ℝ) :=
    mul_bounds_of exB_209 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

/-- Lower end of the enclosure of `Re fEM(c)`. -/
theorem PReG_ge : (28683661 / 50000000000000 : ℝ) ≤ PReG cZ 41 12 := by
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
theorem PReG_le : PReG cZ 41 12 ≤ (84798869 / 50000000000000 : ℝ) := by
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

/-- **The enclosure of `Re fEM(c)`**: `PReG cZ 41 12 ∈ [5.7367322000e-07, 1.6959773800e-06]` (width `1.12e-06`). -/
theorem PReG_mem : (28683661 / 50000000000000 : ℝ) ≤ PReG cZ 41 12 ∧ PReG cZ 41 12 ≤ (84798869 / 50000000000000 : ℝ) := ⟨PReG_ge, PReG_le⟩

/-- Open inequality `H1` of `DHLocate4Base`. -/
theorem H1 : |PReG cZ 41 12| ≤ (3 / 5000 : ℝ) := by
  have h := PReG_mem
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Lower end of the enclosure of `Im fEM(c)`. -/
theorem PImG_ge : (-3880512613 / 1000000000000000 : ℝ) ≤ PImG cZ 41 12 := by
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
theorem PImG_le : PImG cZ 41 12 ≤ (-689492867 / 250000000000000 : ℝ) := by
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

/-- **The enclosure of `Im fEM(c)`**: `PImG cZ 41 12 ∈ [-3.8805126130e-06, -2.7579714680e-06]` (width `1.12e-06`). -/
theorem PImG_mem : (-3880512613 / 1000000000000000 : ℝ) ≤ PImG cZ 41 12 ∧ PImG cZ 41 12 ≤ (-689492867 / 250000000000000 : ℝ) := ⟨PImG_ge, PImG_le⟩

/-- Open inequality `H2` of `DHLocate4Base`. -/
theorem H2 : |PImG cZ 41 12| ≤ (3 / 5000 : ℝ) := by
  have h := PImG_mem
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

set_option maxHeartbeats 1000000 in
/-- Lower end of the enclosure of `Re fEM′(c)`. -/
theorem AReG_ge : (1167951761012631 / 1000000000000000 : ℝ) ≤ AReG cZ 41 12 := by
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
theorem AReG_le : AReG cZ 41 12 ≤ (1167956558747993 / 1000000000000000 : ℝ) := by
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

/-- **The enclosure of `Re fEM′(c)`**: `AReG cZ 41 12 ∈ [1.1679517610e+00, 1.1679565587e+00]` (width `4.80e-06`). -/
theorem AReG_mem : (1167951761012631 / 1000000000000000 : ℝ) ≤ AReG cZ 41 12 ∧ AReG cZ 41 12 ≤ (1167956558747993 / 1000000000000000 : ℝ) := ⟨AReG_ge, AReG_le⟩

/-- Open inequality `H3` of `DHLocate4Base`. -/
theorem H3 : (11 / 10 : ℝ) ≤ AReG cZ 41 12 := by
  have h := AReG_mem
  linarith [h.1]

/-- **The located zero**: within `1 / 150` of `cZ = 72426 / 100000 + (17670246 / 100000) i` (`dh_zero_near_of_center'` with
its three open inequalities discharged). -/
theorem dh_zero_located : ∃ ρ, dh ρ = 0 ∧ ‖ρ - cZ‖ < (1 / 150 : ℝ) :=
  dh_zero_near_of_center' H1 H2 H3

/-- The located zero in coordinates: `0.71759 < Re ρ < 0.73093` (off the critical line)
and `176.69579 < Im ρ < 176.70913`. -/
theorem dh_zero_located_box : ∃ ρ : ℂ, dh ρ = 0 ∧ 107639 / 150000 < ρ.re ∧ ρ.re < 109639 / 150000 ∧
    26504369 / 150000 < ρ.im ∧ ρ.im < 26506369 / 150000 := by
  obtain ⟨ρ, h0, hρ⟩ := dh_zero_located
  have hre := abs_lt.1 ((Complex.abs_re_le_norm (ρ - cZ)).trans_lt hρ)
  have him := abs_lt.1 ((Complex.abs_im_le_norm (ρ - cZ)).trans_lt hρ)
  rw [Complex.sub_re, cZ_re] at hre
  rw [Complex.sub_im, cZ_im] at him
  exact ⟨ρ, h0, by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩

end PsiOmega.Locate.Z4

namespace PsiOmega.Locate

/-- **Zero 4** (`ρ ≈ 0.72425769462680978 + 176.70246124285583 i`): a kernel-checked zero of `dh` within `1 / 150` of
`72426 / 100000 + (17670246 / 100000) i`. -/
theorem dh_zero_located_4 : ∃ ρ, dh ρ = 0 ∧ ‖ρ - Z4.cZ‖ < (1 / 150 : ℝ) := Z4.dh_zero_located

/-- **Zero 4** in coordinates. -/
theorem dh_zero_located_box_4 : ∃ ρ : ℂ, dh ρ = 0 ∧ 107639 / 150000 < ρ.re ∧ ρ.re < 109639 / 150000 ∧
    26504369 / 150000 < ρ.im ∧ ρ.im < 26506369 / 150000 := Z4.dh_zero_located_box

end PsiOmega.Locate

#print axioms PsiOmega.Locate.Z4.PReG_mem
#print axioms PsiOmega.Locate.Z4.PImG_mem
#print axioms PsiOmega.Locate.Z4.AReG_mem
#print axioms PsiOmega.Locate.Z4.H1
#print axioms PsiOmega.Locate.Z4.H2
#print axioms PsiOmega.Locate.Z4.H3
#print axioms PsiOmega.Locate.Z4.dh_zero_located
#print axioms PsiOmega.Locate.Z4.dh_zero_located_box
#print axioms PsiOmega.Locate.dh_zero_located_4
#print axioms PsiOmega.Locate.dh_zero_located_box_4
