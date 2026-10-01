import DHLocateTrig

/-! # Generated (gen_locate.py): the interval evaluation of `PRe 20 12`, `PIm 20 12`, `ARe 20 12`

Stage 3 of the zero-location certificate: the three open inequalities of `DHLocateSkeleton`
(`H1`, `H2`, `H3`) from the atom bounds of `DHLocateExp` / `DHLocateTrig`, `κ` (`PsiOmega.kappa_bounds`)
and `log n` (`PsiOmega.Num.log_bound_n`), by interval products (`mul_bounds_of`) and block sums; then
`dh_zero_located` = `dh_zero_near_of_center' H1 H2 H3`. -/

open Real Finset

namespace PsiOmega.Locate

theorem kappaB : (284079043840412 / 1000000000000000 : ℝ) ≤ kappa ∧ kappa ≤ (284079043840413 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.kappa_bounds
  constructor <;> linarith [h.1, h.2]

theorem lgB_2 : (346573590228867 / 500000000000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (138629436131547 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_2
  constructor <;> linarith [h.1, h.2]

theorem eC_2 : (-136863429113027 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 2 * cC 2 ∧ ex (1617 / 2000) 2 * cC 2 ≤ (-547453706080817 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_2 cCB_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_2 : (-38880032079149 / 250000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 2 * cC 2) ∧ kappa * (ex (1617 / 2000) 2 * cC 2) ≤ (-19440015671291 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_2 : (32438937198569 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 2 * sC 2 ∧ ex (1617 / 2000) 2 * sC 2 ≤ (81097348150919 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_2 sCB_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_2 : (46076111312843 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 2 * sC 2) ∧ kappa * (ex (1617 / 2000) 2 * sC 2) ≤ (46076114241413 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_2 : (-189733000049689 / 500000000000000 : ℝ) ≤ Real.log 2 * (ex (1617 / 2000) 2 * cC 2) ∧ Real.log 2 * (ex (1617 / 2000) 2 * cC 2) ≤ (-75893198560211 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_2 eC_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_2 : (-53899169239089 / 500000000000000 : ℝ) ≤ kappa * (Real.log 2 * (ex (1617 / 2000) 2 * cC 2)) ∧ kappa * (Real.log 2 * (ex (1617 / 2000) 2 * cC 2)) ≤ (-26949584101219 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_3 : (1098612288561369 / 1000000000000000 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (1098612288829637 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_3
  constructor <;> linarith [h.1, h.2]

theorem eC_3 : (409431230325709 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 3 * cC 3 ∧ ex (1617 / 2000) 3 * cC 3 ≤ (409431239947441 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_3 cCB_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_3 : (11631083242933 / 100000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 3 * cC 3) ∧ kappa * (ex (1617 / 2000) 3 * cC 3) ≤ (14538854395333 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_3 : (-10009099759609 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 3 * sC 3 ∧ ex (1617 / 2000) 3 * sC 3 ≤ (-5004548687103 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_3 sCB_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_3 : (-11373501957653 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 3 * sC 3) ∧ kappa * (ex (1617 / 2000) 3 * sC 3) ≤ (-284337481177 / 25000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_3 : (28112886309789 / 62500000000000 : ℝ) ≤ Real.log 3 * (ex (1617 / 2000) 3 * cC 3) ∧ Real.log 3 * (ex (1617 / 2000) 3 * cC 3) ≤ (89961238327403 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_3 eC_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_3 : (25556101959933 / 200000000000000 : ℝ) ≤ kappa * (Real.log 3 * (ex (1617 / 2000) 3 * cC 3)) ∧ kappa * (Real.log 3 * (ex (1617 / 2000) 3 * cC 3)) ≤ (127780512833741 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_4 : (693147180505767 / 500000000000000 : ℝ) ≤ Real.log 4 ∧ Real.log 4 ≤ (693147180650437 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_4
  constructor <;> linarith [h.1, h.2]

theorem eC_4 : (273398444468657 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 4 * cC 4 ∧ ex (1617 / 2000) 4 * cC 4 ≤ (68349613216011 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_4 cCB_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_4 : (-22198521824081 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 4 * sC 4 ∧ ex (1617 / 2000) 4 * sC 4 ≤ (-177588166220543 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_4 sCB_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_4 : (1480510632329 / 3906250000000 : ℝ) ≤ Real.log 4 * (ex (1617 / 2000) 4 * cC 4) ∧ Real.log 4 * (ex (1617 / 2000) 4 * cC 4) ≤ (379010733593807 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_4 eC_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_6 : (1791759469113201 / 1000000000000000 : ℝ) ≤ Real.log 6 ∧ Real.log 6 ≤ (1791759469474139 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_6
  constructor <;> linarith [h.1, h.2]

theorem eC_6 : (-54412740629441 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 6 * cC 6 ∧ ex (1617 / 2000) 6 * cC 6 ≤ (-217650955160031 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_6 cCB_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_6 : (44162820520379 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 6 * sC 6 ∧ ex (1617 / 2000) 6 * sC 6 ≤ (44162824180373 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_6 sCB_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_6 : (-77995634626273 / 200000000000000 : ℝ) ≤ Real.log 6 * (ex (1617 / 2000) 6 * cC 6) ∧ Real.log 6 * (ex (1617 / 2000) 6 * cC 6) ≤ (-194989079934759 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_6 eC_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_7 : (972955074470179 / 500000000000000 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ (972955074651209 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_7
  constructor <;> linarith [h.1, h.2]

theorem eC_7 : (-200464444184803 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 7 * cC 7 ∧ ex (1617 / 2000) 7 * cC 7 ≤ (-25058054693889 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_7 cCB_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_7 : (-56947747628019 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 7 * cC 7) ∧ kappa * (ex (1617 / 2000) 7 * cC 7) ≤ (-2277909829741 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_7 : (-53054705232677 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 7 * sC 7 ∧ ex (1617 / 2000) 7 * sC 7 ≤ (-53054698642137 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_7 sCB_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_7 : (-7535864966867 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 7 * sC 7) ∧ kappa * (ex (1617 / 2000) 7 * sC 7) ≤ (-15071728061499 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_7 : (-390085796513477 / 1000000000000000 : ℝ) ≤ Real.log 7 * (ex (1617 / 2000) 7 * cC 7) ∧ Real.log 7 * (ex (1617 / 2000) 7 * cC 7) ≤ (-390085783532329 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_7 eC_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_7 : (-4432608003571 / 40000000000000 : ℝ) ≤ kappa * (Real.log 7 * (ex (1617 / 2000) 7 * cC 7)) ∧ kappa * (Real.log 7 * (ex (1617 / 2000) 7 * cC 7)) ≤ (-110815196401601 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_8 : (2079441541559079 / 1000000000000000 : ℝ) ≤ Real.log 8 ∧ Real.log 8 ≤ (519860385493349 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_8
  constructor <;> linarith [h.1, h.2]

theorem eC_8 : (-120869140786533 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 8 * cC 8 ∧ ex (1617 / 2000) 8 * cC 8 ≤ (-24173826792721 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_8 cCB_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_8 : (-34336389944451 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 8 * cC 8) ∧ kappa * (ex (1617 / 2000) 8 * cC 8) ≤ (-34336388006199 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_8 : (141565076093633 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 8 * sC 8 ∧ ex (1617 / 2000) 8 * sC 8 ≤ (35391270732299 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_8 sCB_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_8 : (20107835728937 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 8 * sC 8) ∧ kappa * (ex (1617 / 2000) 8 * sC 8) ≤ (8043134679943 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_8 : (-62835078123537 / 250000000000000 : ℝ) ≤ Real.log 8 * (ex (1617 / 2000) 8 * cC 8) ∧ Real.log 8 * (ex (1617 / 2000) 8 * cC 8) ≤ (-251340298256189 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_8 eC_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_8 : (-71400515651889 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 8 * (ex (1617 / 2000) 8 * cC 8)) ∧ kappa * (Real.log 8 * (ex (1617 / 2000) 8 * cC 8)) ≤ (-35700255803591 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_9 : (2197224577213583 / 1000000000000000 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ (274653072205603 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_9
  constructor <;> linarith [h.1, h.2]

theorem eC_9 : (166031020361163 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 9 * cC 9 ∧ ex (1617 / 2000) 9 * cC 9 ≤ (166031026704303 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_9 cCB_9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_9 : (-4098037920007 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 9 * sC 9 ∧ ex (1617 / 2000) 9 * sC 9 ≤ (-262274376507 / 8000000000000 : ℝ) := by
  exact mul_bounds_of exB_9 sCB_9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_9 : (91201859629349 / 250000000000000 : ℝ) ≤ Real.log 9 * (ex (1617 / 2000) 9 * cC 9) ∧ Real.log 9 * (ex (1617 / 2000) 9 * cC 9) ≤ (364807452526299 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_9 eC_9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_11 : (2397895272674763 / 1000000000000000 : ℝ) ≤ Real.log 11 ∧ Real.log 11 ≤ (2397895273114743 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_11
  constructor <;> linarith [h.1, h.2]

theorem eC_11 : (-39263223657487 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 11 * cC 11 ∧ ex (1617 / 2000) 11 * cC 11 ≤ (-3926321814377 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_11 cCB_11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_11 : (-138430692661759 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 11 * sC 11 ∧ ex (1617 / 2000) 11 * sC 11 ≤ (-27686137422553 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_11 sCB_11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_11 : (-5884318650971 / 62500000000000 : ℝ) ≤ Real.log 11 * (ex (1617 / 2000) 11 * cC 11) ∧ Real.log 11 * (ex (1617 / 2000) 11 * cC 11) ≤ (-5884317823559 / 62500000000000 : ℝ) := by
  exact mul_bounds_of lgB_11 eC_11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_12 : (248490664966427 / 100000000000000 : ℝ) ≤ Real.log 12 ∧ Real.log 12 ≤ (1242453325052681 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_12
  constructor <;> linarith [h.1, h.2]

theorem eC_12 : (10482787207357 / 100000000000000 : ℝ) ≤ ex (1617 / 2000) 12 * cC 12 ∧ ex (1617 / 2000) 12 * cC 12 ≤ (52413938640913 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_12 cCB_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_12 : (7444850416621 / 250000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 12 * cC 12) ∧ kappa * (ex (1617 / 2000) 12 * cC 12) ≤ (14889701573021 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_12 : (-16731206885089 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 12 * sC 12 ∧ ex (1617 / 2000) 12 * sC 12 ≤ (-41828014613527 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_12 sCB_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_12 : (-11882463135531 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 12 * sC 12) ∧ kappa * (ex (1617 / 2000) 12 * sC 12) ≤ (-23764924794307 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_12 : (260487476385769 / 1000000000000000 : ℝ) ≤ Real.log 12 * (ex (1617 / 2000) 12 * cC 12) ∧ Real.log 12 * (ex (1617 / 2000) 12 * cC 12) ≤ (260487489374039 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_12 eC_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_12 : (73999033224071 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 12 * (ex (1617 / 2000) 12 * cC 12)) ∧ kappa * (Real.log 12 * (ex (1617 / 2000) 12 * cC 12)) ≤ (73999036913767 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_13 : (641237339334437 / 250000000000000 : ℝ) ≤ Real.log 13 ∧ Real.log 13 ≤ (512989871555873 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_13
  constructor <;> linarith [h.1, h.2]

theorem eC_13 : (31279897508073 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 13 * cC 13 ∧ ex (1617 / 2000) 13 * cC 13 ≤ (15639949356459 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_13 cCB_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_13 : (35543853502077 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 13 * cC 13) ∧ kappa * (ex (1617 / 2000) 13 * cC 13) ≤ (35543854871163 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_13 : (-2438025713223 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 13 * sC 13 ∧ ex (1617 / 2000) 13 * sC 13 ≤ (-6095061893529 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_13 sCB_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_13 : (-1731480033677 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 13 * sC 13) ∧ kappa * (ex (1617 / 2000) 13 * sC 13) ≤ (-3462958709723 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_13 : (320925412043689 / 1000000000000000 : ℝ) ≤ Real.log 13 * (ex (1617 / 2000) 13 * cC 13) ∧ Real.log 13 * (ex (1617 / 2000) 13 * cC 13) ≤ (320925424460411 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_13 eC_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_13 : (91168184197461 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 13 * (ex (1617 / 2000) 13 * cC 13)) ∧ kappa * (Real.log 13 * (ex (1617 / 2000) 13 * cC 13)) ≤ (91168187724793 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_14 : (32988216618643 / 12500000000000 : ℝ) ≤ Real.log 14 ∧ Real.log 14 ≤ (65976433248333 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_14
  constructor <;> linarith [h.1, h.2]

theorem eC_14 : (118350190840009 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 14 * cC 14 ∧ ex (1617 / 2000) 14 * cC 14 ≤ (7396887213999 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_14 cCB_14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_14 : (-693855302631 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 14 * sC 14 ∧ ex (1617 / 2000) 14 * sC 14 ≤ (-216829498139 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_14 sCB_14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_14 : (78083234645759 / 250000000000000 : ℝ) ≤ Real.log 14 * (ex (1617 / 2000) 14 * cC 14) ∧ Real.log 14 * (ex (1617 / 2000) 14 * cC 14) ≤ (156166475366353 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_14 eC_14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_16 : (1386294361052777 / 500000000000000 : ℝ) ≤ Real.log 16 ∧ Real.log 16 ≤ (1386294361310171 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_16
  constructor <;> linarith [h.1, h.2]

theorem eC_16 : (43209151381769 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 16 * cC 16 ∧ ex (1617 / 2000) 16 * cC 16 ≤ (43209156167251 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_16 cCB_16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_16 : (-24276165710747 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 16 * sC 16 ∧ ex (1617 / 2000) 16 * sC 16 ≤ (-97104658035067 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_16 sCB_16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_16 : (29950301453211 / 250000000000000 : ℝ) ≤ Real.log 16 * (ex (1617 / 2000) 16 * cC 16) ∧ Real.log 16 * (ex (1617 / 2000) 16 * cC 16) ≤ (59900609551631 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_16 eC_16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_17 : (2833213343915281 / 1000000000000000 : ℝ) ≤ Real.log 17 ∧ Real.log 17 ≤ (2833213344477039 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_17
  constructor <;> linarith [h.1, h.2]

theorem eC_17 : (-12553411542219 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 17 * cC 17 ∧ ex (1617 / 2000) 17 * cC 17 ≤ (-62767052798141 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_17 cCB_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_17 : (-4457701434811 / 250000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 17 * cC 17) ∧ kappa * (ex (1617 / 2000) 17 * cC 17) ≤ (-2228850542947 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_17 : (-39691968767693 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 17 * sC 17 ∧ ex (1617 / 2000) 17 * sC 17 ≤ (-79383932613273 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_17 sCB_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_17 : (-1127565653567 / 50000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 17 * sC 17) ∧ kappa * (ex (1617 / 2000) 17 * sC 17) ≤ (-2255131167307 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_17 : (-35566493100127 / 200000000000000 : ℝ) ≤ Real.log 17 * (ex (1617 / 2000) 17 * cC 17) ∧ Real.log 17 * (ex (1617 / 2000) 17 * cC 17) ≤ (-22229056443241 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_17 eC_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_17 : (-12629619190801 / 250000000000000 : ℝ) ≤ kappa * (Real.log 17 * (ex (1617 / 2000) 17 * cC 17)) ∧ kappa * (Real.log 17 * (ex (1617 / 2000) 17 * cC 17)) ≤ (-50518472798963 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_18 : (1445185878875393 / 500000000000000 : ℝ) ≤ Real.log 18 ∧ Real.log 18 ≤ (578074351668731 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_18
  constructor <;> linarith [h.1, h.2]

theorem eC_18 : (-85576863283733 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 18 * cC 18 ∧ ex (1617 / 2000) 18 * cC 18 ≤ (-85576858298751 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_18 cCB_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_18 : (-4862118699301 / 200000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 18 * cC 18) ∧ kappa * (ex (1617 / 2000) 18 * cC 18) ≤ (-194484736643 / 8000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_18 : (44877234492153 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 18 * sC 18 ∧ ex (1617 / 2000) 18 * sC 18 ≤ (8975447891519 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_18 sCB_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_18 : (3187170466183 / 250000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 18 * sC 18) ∧ kappa * (ex (1617 / 2000) 18 * sC 18) ≤ (12748683275311 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_18 : (-123674474401469 / 500000000000000 : ℝ) ≤ Real.log 18 * (ex (1617 / 2000) 18 * cC 18) ∧ Real.log 18 * (ex (1617 / 2000) 18 * cC 18) ≤ (-7915165899 / 32000000000 : ℝ) := by
  exact mul_bounds_of lgB_18 eC_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_18 : (-7026665287087 / 100000000000000 : ℝ) ≤ kappa * (Real.log 18 * (ex (1617 / 2000) 18 * cC 18)) ∧ kappa * (Real.log 18 * (ex (1617 / 2000) 18 * cC 18)) ≤ (-70266648763317 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_19 : (58888779580361 / 20000000000000 : ℝ) ≤ Real.log 19 ∧ Real.log 19 ≤ (1472219489816001 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_19
  constructor <;> linarith [h.1, h.2]

theorem eC_19 : (49277969311943 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 19 * cC 19 ∧ ex (1617 / 2000) 19 * cC 19 ≤ (9855594844671 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_19 cCB_19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_19 : (78277574909439 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 19 * sC 19 ∧ ex (1617 / 2000) 19 * sC 19 ≤ (7827757983543 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_19 sCB_19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_19 : (7254798682447 / 50000000000000 : ℝ) ≤ Real.log 19 * (ex (1617 / 2000) 19 * cC 19) ∧ Real.log 19 * (ex (1617 / 2000) 19 * cC 19) ≤ (36273997035137 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_19 eC_19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_21 : (1522261218785741 / 500000000000000 : ℝ) ≤ Real.log 21 ∧ Real.log 21 ≤ (3044522438210293 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_21
  constructor <;> linarith [h.1, h.2]

theorem eC_21 : (-84200524880981 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 21 * cC 21 ∧ ex (1617 / 2000) 21 * cC 21 ≤ (-84200520097289 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_21 cCB_21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_21 : (-13696381715027 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 21 * sC 21 ∧ ex (1617 / 2000) 21 * sC 21 ≤ (-1712047120969 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_21 sCB_21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_21 : (-256350387309231 / 1000000000000000 : ℝ) ≤ Real.log 21 * (ex (1617 / 2000) 21 * cC 21) ∧ Real.log 21 * (ex (1617 / 2000) 21 * cC 21) ≤ (-32043796586423 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_21 eC_21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_22 : (3091042453205323 / 1000000000000000 : ℝ) ≤ Real.log 22 ∧ Real.log 22 ≤ (386380306731437 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_22
  constructor <;> linarith [h.1, h.2]

theorem eC_22 : (4394751625731 / 100000000000000 : ℝ) ≤ ex (1617 / 2000) 22 * cC 22 ∧ ex (1617 / 2000) 22 * cC 22 ≤ (343340006907 / 7812500000000 : ℝ) := by
  exact mul_bounds_of exB_22 cCB_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_22 : (12484568397537 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 22 * cC 22) ∧ kappa * (ex (1617 / 2000) 22 * cC 22) ≤ (12484569711911 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_22 : (69416106883733 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 22 * sC 22 ∧ ex (1617 / 2000) 22 * sC 22 ≤ (69416111523997 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_22 sCB_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_22 : (9859830635327 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 22 * sC 22) ∧ kappa * (ex (1617 / 2000) 22 * sC 22) ≤ (19719662588857 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_22 : (33960909616069 / 250000000000000 : ℝ) ≤ Real.log 22 * (ex (1617 / 2000) 22 * cC 22) ∧ Real.log 22 * (ex (1617 / 2000) 22 * cC 22) ≤ (67921826397133 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_22 eC_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_22 : (19295165463367 / 500000000000000 : ℝ) ≤ kappa * (Real.log 22 * (ex (1617 / 2000) 22 * cC 22)) ∧ kappa * (Real.log 22 * (ex (1617 / 2000) 22 * cC 22)) ≤ (7718066999517 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_23 : (97984194242981 / 31250000000000 : ℝ) ≤ Real.log 23 ∧ Real.log 23 ≤ (78387355410673 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_23
  constructor <;> linarith [h.1, h.2]

theorem eC_23 : (327503337761 / 40000000000000 : ℝ) ≤ ex (1617 / 2000) 23 * cC 23 ∧ ex (1617 / 2000) 23 * cC 23 ≤ (2046896968813 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_23 cCB_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_23 : (1162960438071 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 23 * cC 23) ∧ kappa * (ex (1617 / 2000) 23 * cC 23) ≤ (2325922134961 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_23 : (-15766791034613 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 23 * sC 23 ∧ ex (1617 / 2000) 23 * sC 23 ≤ (-39416975352309 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_23 sCB_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_23 : (-22395074607723 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 23 * sC 23) ∧ kappa * (ex (1617 / 2000) 23 * sC 23) ≤ (-2239507333833 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_23 : (12836060264959 / 500000000000000 : ℝ) ≤ Real.log 23 * (ex (1617 / 2000) 23 * cC 23) ∧ Real.log 23 * (ex (1617 / 2000) 23 * cC 23) ≤ (1283606721467 / 50000000000000 : ℝ) := by
  exact mul_bounds_of lgB_23 eC_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_23 : (3646455726747 / 500000000000000 : ℝ) ≤ kappa * (Real.log 23 * (ex (1617 / 2000) 23 * cC 23)) ∧ kappa * (Real.log 23 * (ex (1617 / 2000) 23 * cC 23)) ≤ (729291540203 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_24 : (397256728774203 / 125000000000000 : ℝ) ≤ Real.log 24 ∧ Real.log 24 ≤ (3178053830849101 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_24
  constructor <;> linarith [h.1, h.2]

theorem eC_24 : (-43819847378719 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 24 * cC 24 ∧ ex (1617 / 2000) 24 * cC 24 ≤ (-43819842979971 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_24 cCB_24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_24 : (62800327369597 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 24 * sC 24 ∧ ex (1617 / 2000) 24 * sC 24 ≤ (15700082944701 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_24 sCB_24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_24 : (-139261833829161 / 1000000000000000 : ℝ) ≤ Real.log 24 * (ex (1617 / 2000) 24 * cC 24) ∧ Real.log 24 * (ex (1617 / 2000) 24 * cC 24) ≤ (-6963090991049 / 50000000000000 : ℝ) := by
  exact mul_bounds_of lgB_24 eC_24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_26 : (162904826893321 / 50000000000000 : ℝ) ≤ Real.log 26 ∧ Real.log 26 ≤ (1629048269263539 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_26
  constructor <;> linarith [h.1, h.2]

theorem eC_26 : (-16630003429919 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 26 * cC 26 ∧ ex (1617 / 2000) 26 * cC 26 ≤ (-33260004781887 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_26 cCB_26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_26 : (26967261000527 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 26 * sC 26 ∧ ex (1617 / 2000) 26 * sC 26 ≤ (26967265135297 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_26 sCB_26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_26 : (-216728626442851 / 1000000000000000 : ℝ) ≤ Real.log 26 * (ex (1617 / 2000) 26 * cC 26) ∧ Real.log 26 * (ex (1617 / 2000) 26 * cC 26) ≤ (-216728612858573 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_26 eC_26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_27 : (51497451028891 / 15625000000000 : ℝ) ≤ Real.log 27 ∧ Real.log 27 ≤ (411979608313923 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_27
  constructor <;> linarith [h.1, h.2]

theorem eC_27 : (8333214994181 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 27 * cC 27 ∧ ex (1617 / 2000) 27 * cC 27 ≤ (6666572397513 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_27 cCB_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_27 : (4734583495327 / 250000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 27 * cC 27) ∧ kappa * (ex (1617 / 2000) 27 * cC 27) ≤ (2367291890473 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_27 : (-10035100855859 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 27 * sC 27 ∧ ex (1617 / 2000) 27 * sC 27 ≤ (-20070197714993 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_27 sCB_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_27 : (-114030474239 / 20000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 27 * sC 27) ∧ kappa * (ex (1617 / 2000) 27 * sC 27) ≤ (-5701522576563 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_27 : (10985966875547 / 50000000000000 : ℝ) ≤ Real.log 27 * (ex (1617 / 2000) 27 * cC 27) ∧ Real.log 27 * (ex (1617 / 2000) 27 * cC 27) ≤ (109859675404953 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_27 eC_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_27 : (15604414828339 / 250000000000000 : ℝ) ≤ kappa * (Real.log 27 * (ex (1617 / 2000) 27 * cC 27)) ∧ kappa * (Real.log 27 * (ex (1617 / 2000) 27 * cC 27)) ≤ (12483532618263 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_28 : (3332204510019711 / 1000000000000000 : ℝ) ≤ Real.log 28 ∧ Real.log 28 ≤ (1666102255341693 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_28
  constructor <;> linarith [h.1, h.2]

theorem eC_28 : (-64228556677421 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 28 * cC 28 ∧ ex (1617 / 2000) 28 * cC 28 ≤ (-16057138189353 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_28 cCB_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_28 : (-4561496742043 / 250000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 28 * cC 28) ∧ kappa * (ex (1617 / 2000) 28 * cC 28) ≤ (-18245985854579 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_28 : (1318439859131 / 62500000000000 : ℝ) ≤ ex (1617 / 2000) 28 * sC 28 ∧ ex (1617 / 2000) 28 * sC 28 ≤ (4219008328591 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_28 sCB_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_28 : (374541134543 / 62500000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 28 * sC 28) ∧ kappa * (ex (1617 / 2000) 28 * sC 28) ≤ (1198531851941 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_28 : (-107011343137593 / 500000000000000 : ℝ) ≤ Real.log 28 * (ex (1617 / 2000) 28 * cC 28) ∧ Real.log 28 * (ex (1617 / 2000) 28 * cC 28) ≤ (-214022673170287 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_28 eC_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_28 : (-15199840019303 / 250000000000000 : ℝ) ≤ kappa * (Real.log 28 * (ex (1617 / 2000) 28 * cC 28)) ∧ kappa * (Real.log 28 * (ex (1617 / 2000) 28 * cC 28)) ≤ (-3799959772149 / 62500000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_29 : (673459165966167 / 200000000000000 : ℝ) ≤ Real.log 29 ∧ Real.log 29 ≤ (3367295830495533 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_29
  constructor <;> linarith [h.1, h.2]

theorem eC_29 : (59124439879723 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 29 * cC 29 ∧ ex (1617 / 2000) 29 * cC 29 ≤ (3695277731359 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_29 cCB_29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_29 : (-17924509147 / 625000000000 : ℝ) ≤ ex (1617 / 2000) 29 * sC 29 ∧ ex (1617 / 2000) 29 * sC 29 ≤ (-5735842165911 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_29 sCB_29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_29 : (7963579193923 / 40000000000000 : ℝ) ≤ Real.log 29 * (ex (1617 / 2000) 29 * cC 29) ∧ Real.log 29 * (ex (1617 / 2000) 29 * cC 29) ≤ (199089492757251 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_29 eC_29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_31 : (3433987204329301 / 1000000000000000 : ℝ) ≤ Real.log 31 ∧ Real.log 31 ≤ (42924840062443 / 12500000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_31
  constructor <;> linarith [h.1, h.2]

theorem eC_31 : (32617942824261 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 31 * cC 31 ∧ ex (1617 / 2000) 31 * cC 31 ≤ (1304717856469 / 40000000000000 : ℝ) := by
  exact mul_bounds_of exB_31 cCB_31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_31 : (-53036053424549 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 31 * sC 31 ∧ ex (1617 / 2000) 31 * sC 31 ≤ (-53036049825987 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_31 sCB_31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_31 : (112009598290057 / 1000000000000000 : ℝ) ≤ Real.log 31 * (ex (1617 / 2000) 31 * cC 31) ∧ Real.log 31 * (ex (1617 / 2000) 31 * cC 31) ≤ (112009610631091 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_31 eC_31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_32 : (3465735902643809 / 1000000000000000 : ℝ) ≤ Real.log 32 ∧ Real.log 32 ≤ (433216987913807 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_32
  constructor <;> linarith [h.1, h.2]

theorem eC_32 : (-1976288308897 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 32 * cC 32 ∧ ex (1617 / 2000) 32 * cC 32 ≤ (-7905149736701 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_32 cCB_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_32 : (-1122844186289 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 32 * cC 32) ∧ kappa * (ex (1617 / 2000) 32 * cC 32) ≤ (-2245687378617 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_32 : (60168600284003 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 32 * sC 32 ∧ ex (1617 / 2000) 32 * sC 32 ≤ (60168603811069 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_32 sCB_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_32 : (3418527687579 / 200000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 32 * sC 32) ∧ kappa * (ex (1617 / 2000) 32 * sC 32) ≤ (8546319719931 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_32 : (-27397173389749 / 1000000000000000 : ℝ) ≤ Real.log 32 * (ex (1617 / 2000) 32 * cC 32) ∧ Real.log 32 * (ex (1617 / 2000) 32 * cC 32) ≤ (-27397161258259 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_32 eC_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_32 : (-778296282049 / 100000000000000 : ℝ) ≤ kappa * (Real.log 32 * (ex (1617 / 2000) 32 * cC 32)) ∧ kappa * (Real.log 32 * (ex (1617 / 2000) 32 * cC 32)) ≤ (-7782959374187 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_33 : (699301512262101 / 200000000000000 : ℝ) ≤ Real.log 33 ∧ Real.log 33 ≤ (3496507561977559 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_33
  constructor <;> linarith [h.1, h.2]

theorem eC_33 : (-270223201781 / 12500000000000 : ℝ) ≤ ex (1617 / 2000) 33 * cC 33 ∧ ex (1617 / 2000) 33 * cC 33 ≤ (-21617852720279 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_33 cCB_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_33 : (-1535294975709 / 250000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 33 * cC 33) ∧ kappa * (ex (1617 / 2000) 33 * cC 33) ≤ (-6141178930659 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_33 : (-55105892374979 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 33 * sC 33 ∧ ex (1617 / 2000) 33 * sC 33 ≤ (-13776472233677 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_33 sCB_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_33 : (-15654429215857 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 33 * sC 33) ∧ kappa * (ex (1617 / 2000) 33 * sC 33) ≤ (-15654428238547 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_33 : (-3023479899037 / 40000000000000 : ℝ) ≤ Real.log 33 * (ex (1617 / 2000) 33 * cC 33) ∧ Real.log 33 * (ex (1617 / 2000) 33 * cC 33) ≤ (-9448373186969 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_33 eC_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_33 : (-21472681969729 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 33 * (ex (1617 / 2000) 33 * cC 33)) ∧ kappa * (Real.log 33 * (ex (1617 / 2000) 33 * cC 33)) ≤ (-5368169641603 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_34 : (3526360524460139 / 1000000000000000 : ℝ) ≤ Real.log 34 ∧ Real.log 34 ≤ (3526360525127523 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_34
  constructor <;> linarith [h.1, h.2]

theorem eC_34 : (23618854196637 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 34 * cC 34 ∧ ex (1617 / 2000) 34 * cC 34 ≤ (23618855871011 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_34 cCB_34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_34 : (4159818151307 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 34 * sC 34 ∧ ex (1617 / 2000) 34 * sC 34 ≤ (33278548551341 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_34 sCB_34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_34 : (650692149 / 3906250000 : ℝ) ≤ Real.log 34 * (ex (1617 / 2000) 34 * cC 34) ∧ Real.log 34 * (ex (1617 / 2000) 34 * cC 34) ≤ (8328860099221 / 50000000000000 : ℝ) := by
  exact mul_bounds_of lgB_34 eC_34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_36 : (3583518938300017 / 1000000000000000 : ℝ) ≤ Real.log 36 ∧ Real.log 36 ≤ (3583518938967891 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_36
  constructor <;> linarith [h.1, h.2]

theorem eC_36 : (39570518922271 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 36 * cC 36 ∧ ex (1617 / 2000) 36 * cC 36 ≤ (39570522120651 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_36 cCB_36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_36 : (-1201510123593 / 31250000000000 : ℝ) ≤ ex (1617 / 2000) 36 * sC 36 ∧ ex (1617 / 2000) 36 * sC 36 ≤ (-300377505953 / 7812500000000 : ℝ) := by
  exact mul_bounds_of exB_36 sCB_36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_36 : (141801703956317 / 1000000000000000 : ℝ) ≤ Real.log 36 * (ex (1617 / 2000) 36 * cC 36) ∧ Real.log 36 * (ex (1617 / 2000) 36 * cC 36) ≤ (141801715444201 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_36 eC_36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_37 : (1805458956244053 / 500000000000000 : ℝ) ≤ Real.log 37 ∧ Real.log 37 ≤ (11284118478613 / 3125000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_37
  constructor <;> linarith [h.1, h.2]

theorem eC_37 : (-337877497259 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 37 * cC 37 ∧ ex (1617 / 2000) 37 * cC 37 ≤ (-84468594409 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_37 cCB_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_37 : (-95983916357 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 37 * cC 37) ∧ kappa * (ex (1617 / 2000) 37 * cC 37) ≤ (-95983030137 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_37 : (2158541347641 / 40000000000000 : ℝ) ≤ ex (1617 / 2000) 37 * sC 37 ∧ ex (1617 / 2000) 37 * sC 37 ≤ (53963536839629 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_37 sCB_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_37 : (3832477263299 / 250000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 37 * sC 37) ∧ kappa * (ex (1617 / 2000) 37 * sC 37) ≤ (15329909947649 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_37 : (-244009581461 / 200000000000000 : ℝ) ≤ Real.log 37 * (ex (1617 / 2000) 37 * cC 37) ∧ Real.log 37 * (ex (1617 / 2000) 37 * cC 37) ≤ (-152504580297 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_37 eC_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_37 : (-346590042947 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 37 * (ex (1617 / 2000) 37 * cC 37)) ∧ kappa * (Real.log 37 * (ex (1617 / 2000) 37 * cC 37)) ≤ (-5415419419 / 15625000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_38 : (1818793079785123 / 500000000000000 : ℝ) ≤ Real.log 38 ∧ Real.log 38 ≤ (72751723204769 / 20000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_38
  constructor <;> linarith [h.1, h.2]

theorem eC_38 : (-39673617499119 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 38 * cC 38 ∧ ex (1617 / 2000) 38 * cC 38 ≤ (-19836807220237 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_38 cCB_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_38 : (-11270443324841 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 38 * cC 38) ∧ kappa * (ex (1617 / 2000) 38 * cC 38) ≤ (-11270442455943 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_38 : (-34860726404451 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 38 * sC 38 ∧ ex (1617 / 2000) 38 * sC 38 ≤ (-34860723350459 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_38 sCB_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_38 : (-9903201824559 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 38 * sC 38) ∧ kappa * (ex (1617 / 2000) 38 * sC 38) ≤ (-9903200956983 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_38 : (-14431620194139 / 100000000000000 : ℝ) ≤ Real.log 38 * (ex (1617 / 2000) 38 * cC 38) ∧ Real.log 38 * (ex (1617 / 2000) 38 * cC 38) ≤ (-72158095394397 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_38 eC_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_38 : (-40997208658191 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 38 * (ex (1617 / 2000) 38 * cC 38)) ∧ kappa * (Real.log 38 * (ex (1617 / 2000) 38 * cC 38)) ≤ (-40997205489971 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_39 : (3663561645973489 / 1000000000000000 : ℝ) ≤ Real.log 39 ∧ Real.log 39 ≤ (3663561646641817 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_39
  constructor <;> linarith [h.1, h.2]

theorem eC_39 : (50739819096133 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 39 * cC 39 ∧ ex (1617 / 2000) 39 * cC 39 ≤ (50739822130513 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_39 cCB_39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_39 : (-2000071410669 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 39 * sC 39 ∧ ex (1617 / 2000) 39 * sC 39 ≤ (-10000354040993 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_39 sCB_39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_39 : (92944227582113 / 500000000000000 : ℝ) ≤ Real.log 39 * (ex (1617 / 2000) 39 * cC 39) ∧ Real.log 39 * (ex (1617 / 2000) 39 * cC 39) ≤ (23236058289347 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_39 eC_39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_41 : (3713572066548123 / 1000000000000000 : ℝ) ≤ Real.log 41 ∧ Real.log 41 ≤ (3713572067216643 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_41
  constructor <;> linarith [h.1, h.2]

theorem eC_41 : (-1806474807951 / 62500000000000 : ℝ) ≤ ex (1617 / 2000) 41 * cC 41 ∧ ex (1617 / 2000) 41 * cC 41 ≤ (-28903594065153 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_41 cCB_41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_41 : (-20194995702857 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 41 * sC 41 ∧ ex (1617 / 2000) 41 * sC 41 ≤ (-40389988537111 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_41 sCB_41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_41 : (-107335590190999 / 1000000000000000 : ℝ) ≤ Real.log 41 * (ex (1617 / 2000) 41 * cC 41) ∧ Real.log 41 * (ex (1617 / 2000) 41 * cC 41) ≤ (-53667789771599 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_41 eC_41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_42 : (3737669618127173 / 1000000000000000 : ℝ) ≤ Real.log 42 ∧ Real.log 42 ≤ (3737669618795767 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_42
  constructor <;> linarith [h.1, h.2]

theorem eC_42 : (9663473424573 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 42 * cC 42 ∧ ex (1617 / 2000) 42 * cC 42 ≤ (12079342491211 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_42 cCB_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_42 : (13725951453149 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 42 * cC 42) ∧ kappa * (ex (1617 / 2000) 42 * cC 42) ≤ (13725952260497 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_42 : (-1539686361933 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 42 * sC 42 ∧ ex (1617 / 2000) 42 * sC 42 ≤ (-6158742628563 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_42 sCB_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_42 : (-1749570518049 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 42 * sC 42) ∧ kappa * (ex (1617 / 2000) 42 * sC 42) ≤ (-1749569717181 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_42 : (180594355123029 / 1000000000000000 : ℝ) ≤ Real.log 42 * (ex (1617 / 2000) 42 * cC 42) ∧ Real.log 42 * (ex (1617 / 2000) 42 * cC 42) ≤ (180594365777713 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_42 eC_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_42 : (2052122869053 / 40000000000000 : ℝ) ≤ kappa * (Real.log 42 * (ex (1617 / 2000) 42 * cC 42)) ∧ kappa * (Real.log 42 * (ex (1617 / 2000) 42 * cC 42)) ≤ (51303074753099 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_43 : (1880600057768679 / 500000000000000 : ℝ) ≤ Real.log 43 ∧ Real.log 43 ≤ (1880600058103007 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_43
  constructor <;> linarith [h.1, h.2]

theorem eC_43 : (-1498653734419 / 100000000000000 : ℝ) ≤ ex (1617 / 2000) 43 * cC 43 ∧ ex (1617 / 2000) 43 * cC 43 ≤ (-14986534581419 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_43 cCB_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_43 : (-4257361199217 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 43 * cC 43) ∧ kappa * (ex (1617 / 2000) 43 * cC 43) ≤ (-425736041437 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_43 : (45379806877081 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 43 * sC 43 ∧ ex (1617 / 2000) 43 * sC 43 ≤ (45379809656299 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_43 sCB_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_43 : (12891452147303 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 43 * sC 43) ∧ kappa * (ex (1617 / 2000) 43 * sC 43) ≤ (6445726468411 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_43 : (-28183683000247 / 500000000000000 : ℝ) ≤ Real.log 43 * (ex (1617 / 2000) 43 * cC 43) ∧ Real.log 43 * (ex (1617 / 2000) 43 * cC 43) ≤ (-56367355599137 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_43 eC_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_43 : (-16012787437223 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 43 * (ex (1617 / 2000) 43 * cC 43)) ∧ kappa * (Real.log 43 * (ex (1617 / 2000) 43 * cC 43)) ≤ (-3202556896483 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_44 : (3784189633762049 / 1000000000000000 : ℝ) ≤ Real.log 44 ∧ Real.log 44 ≤ (3784189634430759 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_44
  constructor <;> linarith [h.1, h.2]

theorem eC_44 : (-17659078935949 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 44 * cC 44 ∧ ex (1617 / 2000) 44 * cC 44 ≤ (-3531815512219 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_44 cCB_44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_44 : (-30874053819141 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 44 * sC 44 ∧ ex (1617 / 2000) 44 * sC 44 ≤ (-6174810214717 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_44 sCB_44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_44 : (-66825303463013 / 500000000000000 : ℝ) ≤ Real.log 44 * (ex (1617 / 2000) 44 * cC 44) ∧ Real.log 44 * (ex (1617 / 2000) 44 * cC 44) ≤ (-133650596496991 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_44 eC_44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_46 : (3828641396332871 / 1000000000000000 : ℝ) ≤ Real.log 46 ∧ Real.log 46 ≤ (59822521828151 / 15625000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_46
  constructor <;> linarith [h.1, h.2]

theorem eC_46 : (1660824636317 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 46 * cC 46 ∧ ex (1617 / 2000) 46 * cC 46 ≤ (1660825160923 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_46 cCB_46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_46 : (22242960857931 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 46 * sC 46 ∧ ex (1617 / 2000) 46 * sC 46 ≤ (22242962179239 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_46 sCB_46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_46 : (31793509773263 / 1000000000000000 : ℝ) ≤ Real.log 46 * (ex (1617 / 2000) 46 * cC 46) ∧ Real.log 46 * (ex (1617 / 2000) 46 * cC 46) ≤ (31793519821459 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_46 eC_46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_47 : (385014760155383 / 100000000000000 : ℝ) ≤ Real.log 47 ∧ Real.log 47 ≤ (60158556284729 / 15625000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_47
  constructor <;> linarith [h.1, h.2]

theorem eC_47 : (-8860650754433 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 47 * cC 47 ∧ ex (1617 / 2000) 47 * cC 47 ≤ (-44303251161011 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_47 cCB_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_47 : (-1573203246327 / 125000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 47 * cC 47) ∧ kappa * (ex (1617 / 2000) 47 * cC 47) ≤ (-12585625228841 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_47 : (-3896538231537 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 47 * sC 47 ∧ ex (1617 / 2000) 47 * sC 47 ≤ (-3896535642259 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_47 sCB_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_47 : (-1106924855103 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 47 * sC 47) ∧ kappa * (ex (1617 / 2000) 47 * sC 47) ≤ (-1106924119543 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_47 : (-170574066281563 / 1000000000000000 : ℝ) ≤ Real.log 47 * (ex (1617 / 2000) 47 * cC 47) ∧ Real.log 47 * (ex (1617 / 2000) 47 * cC 47) ≤ (-170574056198603 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_47 eC_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_47 : (-24228258826619 / 500000000000000 : ℝ) ≤ kappa * (Real.log 47 * (ex (1617 / 2000) 47 * cC 47)) ∧ kappa * (Real.log 47 * (ex (1617 / 2000) 47 * cC 47)) ≤ (-48456514788879 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_48 : (1935600505375829 / 500000000000000 : ℝ) ≤ Real.log 48 ∧ Real.log 48 ≤ (3871201011420513 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_48
  constructor <;> linarith [h.1, h.2]

theorem eC_48 : (1725431947547 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 48 * cC 48 ∧ ex (1617 / 2000) 48 * cC 48 ≤ (1380345812501 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_48 cCB_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_48 : (1960636231483 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 48 * cC 48) ∧ kappa * (ex (1617 / 2000) 48 * cC 48) ≤ (784254637169 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_48 : (-41487621015019 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 48 * sC 48 ∧ ex (1617 / 2000) 48 * sC 48 ≤ (-8297523691079 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_48 sCB_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_48 : (-11785763709161 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 48 * sC 48) ∧ kappa * (ex (1617 / 2000) 48 * sC 48) ≤ (-1473220372753 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_48 : (53435951194617 / 1000000000000000 : ℝ) ≤ Real.log 48 * (ex (1617 / 2000) 48 * cC 48) ∧ Real.log 48 * (ex (1617 / 2000) 48 * cC 48) ≤ (667949513183 / 12500000000000 : ℝ) := by
  exact mul_bounds_of lgB_48 eC_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_48 : (15180033922069 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 48 * (ex (1617 / 2000) 48 * cC 48)) ∧ kappa * (Real.log 48 * (ex (1617 / 2000) 48 * cC 48)) ≤ (1897504590387 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_49 : (389182029795439 / 100000000000000 : ℝ) ≤ Real.log 49 ∧ Real.log 49 ≤ (389182029862327 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_49
  constructor <;> linarith [h.1, h.2]

theorem eC_49 : (1868559464419 / 50000000000000 : ℝ) ≤ ex (1617 / 2000) 49 * cC 49 ∧ ex (1617 / 2000) 49 * cC 49 ≤ (1868559590287 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_49 cCB_49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_49 : (5317790312587 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 49 * sC 49 ∧ ex (1617 / 2000) 49 * sC 49 ≤ (10635581879479 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_49 sCB_49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_49 : (36360488257803 / 250000000000000 : ℝ) ≤ Real.log 49 * (ex (1617 / 2000) 49 * cC 49) ∧ Real.log 49 * (ex (1617 / 2000) 49 * cC 49) ≤ (145441962853323 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_49 eC_49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_51 : (982956408142021 / 250000000000000 : ℝ) ≤ Real.log 51 ∧ Real.log 51 ≤ (982956408309251 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_51
  constructor <;> linarith [h.1, h.2]

theorem eC_51 : (-2887704065693 / 100000000000000 : ℝ) ≤ ex (1617 / 2000) 51 * cC 51 ∧ ex (1617 / 2000) 51 * cC 51 ≤ (-3609629780791 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_51 cCB_51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_51 : (-29989297250747 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 51 * sC 51 ∧ ex (1617 / 2000) 51 * sC 51 ≤ (-29989294836179 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_51 sCB_51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_51 : (-22707897733389 / 200000000000000 : ℝ) ≤ Real.log 51 * (ex (1617 / 2000) 51 * cC 51) ∧ Real.log 51 * (ex (1617 / 2000) 51 * cC 51) ≤ (-113539479169561 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_51 eC_51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_52 : (3951243718425183 / 1000000000000000 : ℝ) ≤ Real.log 52 ∧ Real.log 52 ≤ (3951243719094119 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_52
  constructor <;> linarith [h.1, h.2]

theorem eC_52 : (4005334892701 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 52 * cC 52 ∧ ex (1617 / 2000) 52 * cC 52 ≤ (4005335192761 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_52 cCB_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_52 : (9102653652633 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 52 * cC 52) ∧ kappa * (ex (1617 / 2000) 52 * cC 52) ≤ (56891589591 / 6250000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_52 : (-2555252219057 / 100000000000000 : ℝ) ≤ ex (1617 / 2000) 52 * sC 52 ∧ ex (1617 / 2000) 52 * sC 52 ≤ (-25552519794309 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_52 sCB_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_52 : (-7258936071609 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 52 * sC 52) ∧ kappa * (ex (1617 / 2000) 52 * sC 52) ≤ (-45368346193 / 6250000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_52 : (7913027167487 / 62500000000000 : ℝ) ≤ Real.log 52 * (ex (1617 / 2000) 52 * cC 52) ∧ Real.log 52 * (ex (1617 / 2000) 52 * cC 52) ≤ (126608444186109 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_52 eC_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_52 : (17983401532983 / 500000000000000 : ℝ) ≤ kappa * (Real.log 52 * (ex (1617 / 2000) 52 * cC 52)) ∧ kappa * (Real.log 52 * (ex (1617 / 2000) 52 * cC 52)) ≤ (35966805766513 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_52 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_53 : (31762335307167 / 8000000000000 : ℝ) ≤ Real.log 53 ∧ Real.log 53 ≤ (1985145957032413 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_53
  constructor <;> linarith [h.1, h.2]

theorem eC_53 : (1448198257369 / 62500000000000 : ℝ) ≤ ex (1617 / 2000) 53 * cC 53 ∧ ex (1617 / 2000) 53 * cC 53 ≤ (2317117445549 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_53 cCB_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_53 : (1316488883983 / 200000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 53 * cC 53) ∧ kappa * (ex (1617 / 2000) 53 * cC 53) ≤ (822805635497 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_53 : (4130327499271 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 53 * sC 53 ∧ ex (1617 / 2000) 53 * sC 53 ≤ (16521311168661 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_53 sCB_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_53 : (375468635757 / 40000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 53 * sC 53) ∧ kappa * (ex (1617 / 2000) 53 * sC 53) ≤ (9386716559567 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_53 : (45998158641809 / 500000000000000 : ℝ) ≤ Real.log 53 * (ex (1617 / 2000) 53 * cC 53) ∧ Real.log 53 * (ex (1617 / 2000) 53 * cC 53) ≤ (45998163290009 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_53 eC_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_53 : (26134225850769 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 53 * (ex (1617 / 2000) 53 * cC 53)) ∧ kappa * (Real.log 53 * (ex (1617 / 2000) 53 * cC 53)) ≤ (13067114245841 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_54 : (1994492023204013 / 500000000000000 : ℝ) ≤ Real.log 54 ∧ Real.log 54 ≤ (3988984047076989 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_54
  constructor <;> linarith [h.1, h.2]

theorem eC_54 : (-3324111821961 / 100000000000000 : ℝ) ≤ ex (1617 / 2000) 54 * cC 54 ∧ ex (1617 / 2000) 54 * cC 54 ≤ (-33241115899667 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_54 cCB_54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_54 : (10900165173071 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 54 * sC 54 ∧ ex (1617 / 2000) 54 * sC 54 ≤ (2180033265977 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_54 sCB_54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_54 : (-5303931611401 / 40000000000000 : ℝ) ≤ Real.log 54 * (ex (1617 / 2000) 54 * cC 54) ∧ Real.log 54 * (ex (1617 / 2000) 54 * cC 54) ≤ (-132598281008571 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_54 eC_54 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_56 : (2012675845289449 / 500000000000000 : ℝ) ≤ Real.log 56 ∧ Real.log 56 ≤ (2012675845623941 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_56
  constructor <;> linarith [h.1, h.2]

theorem eC_56 : (7935164019389 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 56 * cC 56 ∧ ex (1617 / 2000) 56 * cC 56 ≤ (15870329162341 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_56 cCB_56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_56 : (-10983044743023 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 56 * sC 56 ∧ ex (1617 / 2000) 56 * sC 56 ≤ (-5491521811101 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_56 sCB_56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_56 : (127767303601873 / 1000000000000000 : ℝ) ≤ Real.log 56 * (ex (1617 / 2000) 56 * cC 56) ∧ Real.log 56 * (ex (1617 / 2000) 56 * cC 56) ≤ (6388365633429 / 50000000000000 : ℝ) := by
  exact mul_bounds_of lgB_56 eC_56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_57 : (2021525633839149 / 500000000000000 : ℝ) ≤ Real.log 57 ∧ Real.log 57 ≤ (404305126834729 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_57
  constructor <;> linarith [h.1, h.2]

theorem eC_57 : (23309891723727 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 57 * cC 57 ∧ ex (1617 / 2000) 57 * cC 57 ≤ (1165494696419 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_57 cCB_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_57 : (6621851752899 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 57 * cC 57) ∧ kappa * (ex (1617 / 2000) 57 * cC 57) ≤ (1655463094799 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_57 : (7519092938229 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 57 * sC 57 ∧ ex (1617 / 2000) 57 * sC 57 ≤ (15038186980873 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_57 sCB_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_57 : (8544066929757 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 57 * sC 57) ∧ kappa * (ex (1617 / 2000) 57 * sC 57) ≤ (213601688931 / 25000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_57 : (47121543641529 / 500000000000000 : ℝ) ≤ Real.log 57 * (ex (1617 / 2000) 57 * cC 57) ∧ Real.log 57 * (ex (1617 / 2000) 57 * cC 57) ≤ (47121548106089 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_57 eC_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_57 : (26772486123939 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 57 * (ex (1617 / 2000) 57 * cC 57)) ∧ kappa * (Real.log 57 * (ex (1617 / 2000) 57 * cC 57)) ≤ (6693122165129 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_58 : (4060443010370279 / 1000000000000000 : ℝ) ≤ Real.log 58 ∧ Real.log 58 ≤ (2030221505569357 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_58
  constructor <;> linarith [h.1, h.2]

theorem eC_58 : (-27716280330529 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 58 * cC 58 ∧ ex (1617 / 2000) 58 * cC 58 ≤ (-27716277833853 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_58 cCB_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_58 : (-787361441511 / 100000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 58 * cC 58) ∧ kappa * (ex (1617 / 2000) 58 * cC 58) ≤ (-61512607077 / 7812500000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_58 : (12645105359633 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 58 * sC 58 ∧ ex (1617 / 2000) 58 * sC 58 ≤ (25290213212449 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_58 sCB_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_58 : (7184418879651 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 58 * sC 58) ∧ kappa * (ex (1617 / 2000) 58 * sC 58) ≤ (7184419587913 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_58 : (-56270188381429 / 500000000000000 : ℝ) ≤ Real.log 58 * (ex (1617 / 2000) 58 * cC 58) ∧ Real.log 58 * (ex (1617 / 2000) 58 * cC 58) ≤ (-112540366603949 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_58 eC_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_58 : (-31970362624233 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 58 * (ex (1617 / 2000) 58 * cC 58)) ∧ kappa * (Real.log 58 * (ex (1617 / 2000) 58 * cC 58)) ≤ (-31970359738299 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_59 : (2038768721855667 / 500000000000000 : ℝ) ≤ Real.log 59 ∧ Real.log 59 ≤ (4077537444570997 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_59
  constructor <;> linarith [h.1, h.2]

theorem eC_59 : (-2769073107933 / 100000000000000 : ℝ) ≤ ex (1617 / 2000) 59 * cC 59 ∧ ex (1617 / 2000) 59 * cC 59 ≤ (-5538145663169 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_59 cCB_59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_59 : (-196388151043 / 8000000000000 : ℝ) ≤ ex (1617 / 2000) 59 * sC 59 ∧ ex (1617 / 2000) 59 * sC 59 ≤ (-1534282257539 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_59 sCB_59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_59 : (-56454996421757 / 500000000000000 : ℝ) ≤ Real.log 59 * (ex (1617 / 2000) 59 * cC 59) ∧ Real.log 59 * (ex (1617 / 2000) 59 * cC 59) ≤ (-22581996310299 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_59 eC_59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_61 : (205543693197337 / 50000000000000 : ℝ) ≤ Real.log 61 ∧ Real.log 61 ≤ (2055436932483667 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_61
  constructor <;> linarith [h.1, h.2]

theorem eC_61 : (814517074319 / 25000000000000 : ℝ) ≤ ex (1617 / 2000) 61 * cC 61 ∧ ex (1617 / 2000) 61 * cC 61 ≤ (8145171541281 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_61 cCB_61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_61 : (614545865443 / 40000000000000 : ℝ) ≤ ex (1617 / 2000) 61 * sC 61 ∧ ex (1617 / 2000) 61 * sC 61 ≤ (15363649814203 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_61 sCB_61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_61 : (133935078102253 / 1000000000000000 : ℝ) ≤ Real.log 61 * (ex (1617 / 2000) 61 * cC 61) ∧ Real.log 61 * (ex (1617 / 2000) 61 * cC 61) ≤ (4185471601841 / 31250000000000 : ℝ) := by
  exact mul_bounds_of lgB_61 eC_61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_62 : (515891798100539 / 125000000000000 : ℝ) ≤ Real.log 62 ∧ Real.log 62 ≤ (82542687717919 / 20000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_62
  constructor <;> linarith [h.1, h.2]

theorem eC_62 : (-4627325440179 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 62 * cC 62 ∧ ex (1617 / 2000) 62 * cC 62 ≤ (-2313661879191 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_62 cCB_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_62 : (-2629052373169 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 62 * cC 62) ∧ kappa * (ex (1617 / 2000) 62 * cC 62) ≤ (-1314525708821 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_62 : (34325238948067 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 62 * sC 62 ∧ ex (1617 / 2000) 62 * sC 62 ≤ (17162621166913 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_62 sCB_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_62 : (243777026499 / 25000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 62 * sC 62) ∧ kappa * (ex (1617 / 2000) 62 * sC 62) ≤ (1218885252723 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_62 : (-9548796969447 / 250000000000000 : ℝ) ≤ Real.log 62 * (ex (1617 / 2000) 62 * cC 62) ∧ Real.log 62 * (ex (1617 / 2000) 62 * cC 62) ≤ (-477439674821 / 12500000000000 : ℝ) := by
  exact mul_bounds_of lgB_62 eC_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_62 : (-10850452451627 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 62 * (ex (1617 / 2000) 62 * cC 62)) ∧ kappa * (Real.log 62 * (ex (1617 / 2000) 62 * cC 62)) ≤ (-1085044850517 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_63 : (828626945227529 / 200000000000000 : ℝ) ≤ Real.log 63 ∧ Real.log 63 ≤ (517891840911853 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_63
  constructor <;> linarith [h.1, h.2]

theorem eC_63 : (-35022679306583 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 63 * cC 63 ∧ ex (1617 / 2000) 63 * cC 63 ≤ (-17511337883627 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_63 cCB_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_63 : (-310912789067 / 31250000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 63 * cC 63) ∧ kappa * (ex (1617 / 2000) 63 * cC 63) ≤ (-4974604122347 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_63 : (-2236642334043 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 63 * sC 63 ∧ ex (1617 / 2000) 63 * sC 63 ≤ (-2236638825441 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_63 sCB_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_63 : (-158845803917 / 250000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 63 * sC 63) ∧ kappa * (ex (1617 / 2000) 63 * sC 63) ≤ (-635382218947 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_63 : (-72551839439007 / 500000000000000 : ℝ) ≤ Real.log 63 * (ex (1617 / 2000) 63 * cC 63) ∧ Real.log 63 * (ex (1617 / 2000) 63 * cC 63) ≤ (-145103664173569 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_63 eC_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_63 : (-41220914353393 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 63 * (ex (1617 / 2000) 63 * cC 63)) ∧ kappa * (Real.log 63 * (ex (1617 / 2000) 63 * cC 63)) ≤ (-41220910176167 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_64 : (1039720770773419 / 250000000000000 : ℝ) ≤ Real.log 64 ∧ Real.log 64 ≤ (831776616862279 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_64
  constructor <;> linarith [h.1, h.2]

theorem eC_64 : (-5431324647631 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 64 * cC 64 ∧ ex (1617 / 2000) 64 * cC 64 ≤ (-543132100599 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_64 cCB_64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_64 : (-85554250007 / 2500000000000 : ℝ) ≤ ex (1617 / 2000) 64 * sC 64 ∧ ex (1617 / 2000) 64 * sC 64 ≤ (-6844339266553 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_64 sCB_64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_64 : (-22588244202437 / 1000000000000000 : ℝ) ≤ Real.log 64 * (ex (1617 / 2000) 64 * cC 64) ∧ Real.log 64 * (ex (1617 / 2000) 64 * cC 64) ≤ (-22588229050663 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_64 eC_64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_66 : (261853421358679 / 62500000000000 : ℝ) ≤ Real.log 66 ∧ Real.log 66 ≤ (837930948612883 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_66
  constructor <;> linarith [h.1, h.2]

theorem eC_66 : (1298290948531 / 62500000000000 : ℝ) ≤ ex (1617 / 2000) 66 * cC 66 ∧ ex (1617 / 2000) 66 * cC 66 ≤ (519316476751 / 25000000000000 : ℝ) := by
  exact mul_bounds_of exB_66 cCB_66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_66 : (26661621506489 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 66 * sC 66 ∧ ex (1617 / 2000) 66 * sC 66 ≤ (26661625406829 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_66 sCB_66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_66 : (10878781657339 / 125000000000000 : ℝ) ≤ Real.log 66 * (ex (1617 / 2000) 66 * cC 66) ∧ Real.log 66 * (ex (1617 / 2000) 66 * cC 66) ≤ (43515134799427 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_66 eC_66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_67 : (131396644346681 / 31250000000000 : ℝ) ≤ Real.log 67 ∧ Real.log 67 ≤ (840938524093481 / 200000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_67
  constructor <;> linarith [h.1, h.2]

theorem eC_67 : (-2448337697463 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 67 * cC 67 ∧ ex (1617 / 2000) 67 * cC 67 ≤ (-1958669760511 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_67 cCB_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_67 : (-22256685827 / 4000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 67 * cC 67) ∧ kappa * (ex (1617 / 2000) 67 * cC 67) ≤ (-111283406553 / 20000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_67 : (27041893200669 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 67 * sC 67 ∧ ex (1617 / 2000) 67 * sC 67 ≤ (27041897183801 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_67 sCB_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_67 : (96025439551 / 12500000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 67 * sC 67) ∧ kappa * (ex (1617 / 2000) 67 * sC 67) ≤ (1536407259121 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_67 : (-82356059591479 / 1000000000000000 : ℝ) ≤ Real.log 67 * (ex (1617 / 2000) 67 * cC 67) ∧ Real.log 67 * (ex (1617 / 2000) 67 * cC 67) ≤ (-20589010713157 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_67 eC_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_67 : (-5848907665803 / 250000000000000 : ℝ) ≤ kappa * (Real.log 67 * (ex (1617 / 2000) 67 * cC 67)) ∧ kappa * (Real.log 67 * (ex (1617 / 2000) 67 * cC 67)) ≤ (-11697812954027 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_68 : (1054876926217503 / 250000000000000 : ℝ) ≤ Real.log 68 ∧ Real.log 68 ≤ (421950770628823 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_68
  constructor <;> linarith [h.1, h.2]

theorem eC_68 : (-7814516285263 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 68 * cC 68 ∧ ex (1617 / 2000) 68 * cC 68 ≤ (-6251612217863 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_68 cCB_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_68 : (-2219940314393 / 250000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 68 * cC 68) ∧ kappa * (ex (1617 / 2000) 68 * cC 68) ≤ (-8879760106557 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_68 : (-10556760806481 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 68 * sC 68 ∧ ex (1617 / 2000) 68 * sC 68 ≤ (-10556756778523 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_68 sCB_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_68 : (-1499477257979 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 68 * sC 68) ∧ kappa * (ex (1617 / 2000) 68 * sC 68) ≤ (-1499476685849 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_68 : (-131893646746329 / 1000000000000000 : ℝ) ≤ Real.log 68 * (ex (1617 / 2000) 68 * cC 68) ∧ Real.log 68 * (ex (1617 / 2000) 68 * cC 68) ≤ (-65946814802831 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_68 eC_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_68 : (-37468221056323 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 68 * (ex (1617 / 2000) 68 * cC 68)) ∧ kappa * (Real.log 68 * (ex (1617 / 2000) 68 * cC 68)) ≤ (-37468216187017 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_68 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_69 : (1058526626070719 / 250000000000000 : ℝ) ≤ Real.log 69 ∧ Real.log 69 ≤ (4234106505742537 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_69
  constructor <;> linarith [h.1, h.2]

theorem eC_69 : (39204924353 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 69 * cC 69 ∧ ex (1617 / 2000) 69 * cC 69 ≤ (12251795481 / 62500000000000 : ℝ) := by
  exact mul_bounds_of exB_69 cCB_69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_69 : (-4075610774111 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 69 * sC 69 ∧ ex (1617 / 2000) 69 * sC 69 ≤ (-32604882048641 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_69 sCB_69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_69 : (414994563007 / 500000000000000 : ℝ) ≤ Real.log 69 * (ex (1617 / 2000) 69 * cC 69) ∧ Real.log 69 * (ex (1617 / 2000) 69 * cC 69) ≤ (830006511251 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_69 eC_69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_71 : (852535975342409 / 200000000000000 : ℝ) ≤ Real.log 71 ∧ Real.log 71 ≤ (4262679878246141 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_71
  constructor <;> linarith [h.1, h.2]

theorem eC_71 : (5050857594071 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 71 * cC 71 ∧ ex (1617 / 2000) 71 * cC 71 ≤ (5050858650209 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_71 cCB_71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_71 : (492721512467 / 20000000000000 : ℝ) ≤ ex (1617 / 2000) 71 * sC 71 ∧ ex (1617 / 2000) 71 * sC 71 ≤ (4927215970821 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_71 sCB_71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_71 : (43060378052769 / 500000000000000 : ℝ) ≤ Real.log 71 * (ex (1617 / 2000) 71 * cC 71) ∧ Real.log 71 * (ex (1617 / 2000) 71 * cC 71) ≤ (43060387072223 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_71 eC_71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_72 : (133645816208753 / 31250000000000 : ℝ) ≤ Real.log 72 ∧ Real.log 72 ≤ (106916653006191 / 25000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_72
  constructor <;> linarith [h.1, h.2]

theorem eC_72 : (-308538346423 / 20000000000000 : ℝ) ≤ ex (1617 / 2000) 72 * cC 72 ∧ ex (1617 / 2000) 72 * cC 72 ≤ (-120522758139 / 7812500000000 : ℝ) := by
  exact mul_bounds_of exB_72 cCB_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_72 : (-2191231960999 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 72 * cC 72) ∧ kappa * (ex (1617 / 2000) 72 * cC 72) ≤ (-4382462706321 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_72 : (6866700652683 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 72 * sC 72 ∧ ex (1617 / 2000) 72 * sC 72 ≤ (13733403452699 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_72 sCB_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_72 : (780274302301 / 100000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 72 * sC 72) ∧ kappa * (ex (1617 / 2000) 72 * sC 72) ≤ (1560548848607 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_72 : (-8246971830903 / 125000000000000 : ℝ) ≤ Real.log 72 * (ex (1617 / 2000) 72 * cC 72) ∧ Real.log 72 * (ex (1617 / 2000) 72 * cC 72) ≤ (-13195151264331 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_72 eC_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_72 : (-9371167489207 / 500000000000000 : ℝ) ≤ kappa * (Real.log 72 * (ex (1617 / 2000) 72 * cC 72)) ∧ kappa * (Real.log 72 * (ex (1617 / 2000) 72 * cC 72)) ≤ (-18742329772503 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_72 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_73 : (4290459440806191 / 1000000000000000 : ℝ) ≤ Real.log 73 ∧ Real.log 73 ≤ (4290459442404939 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_73
  constructor <;> linarith [h.1, h.2]

theorem eC_73 : (-30917781948971 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 73 * cC 73 ∧ ex (1617 / 2000) 73 * cC 73 ≤ (-30917777639451 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_73 cCB_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_73 : (-8783093933731 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 73 * cC 73) ∧ kappa * (ex (1617 / 2000) 73 * cC 73) ≤ (-1756618541897 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_73 : (-3823136607569 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 73 * sC 73 ∧ ex (1617 / 2000) 73 * sC 73 ≤ (-3823132333139 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_73 sCB_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_73 : (-21721459839 / 20000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 73 * sC 73) ∧ kappa * (ex (1617 / 2000) 73 * sC 73) ≤ (-1086071777673 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_73 : (-6632574475059 / 50000000000000 : ℝ) ≤ Real.log 73 * (ex (1617 / 2000) 73 * cC 73) ∧ Real.log 73 * (ex (1617 / 2000) 73 * cC 73) ≤ (-132651470961929 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_73 eC_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_73 : (-18841754150751 / 500000000000000 : ℝ) ≤ kappa * (Real.log 73 * (ex (1617 / 2000) 73 * cC 73)) ∧ kappa * (Real.log 73 * (ex (1617 / 2000) 73 * cC 73)) ≤ (-4710437879361 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_74 : (2152032546428071 / 500000000000000 : ℝ) ≤ Real.log 74 ∧ Real.log 74 ≤ (1076016273621007 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_74
  constructor <;> linarith [h.1, h.2]

theorem eC_74 : (-8567628947201 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 74 * cC 74 ∧ ex (1617 / 2000) 74 * cC 74 ≤ (-8567624627439 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_74 cCB_74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_74 : (-14798670854889 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 74 * sC 74 ∧ ex (1617 / 2000) 74 * sC 74 ≤ (-7399334340571 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_74 sCB_74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_74 : (-36875632694139 / 1000000000000000 : ℝ) ≤ Real.log 74 * (ex (1617 / 2000) 74 * cC 74) ∧ Real.log 74 * (ex (1617 / 2000) 74 * cC 74) ≤ (-18437807043827 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_74 eC_74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_76 : (4330733339927761 / 1000000000000000 : ℝ) ≤ Real.log 76 ∧ Real.log 76 ≤ (4330733341608359 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_76
  constructor <;> linarith [h.1, h.2]

theorem eC_76 : (27373690278037 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 76 * cC 76 ∧ ex (1617 / 2000) 76 * cC 76 ≤ (6843423666291 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_76 cCB_76 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_76 : (505991273903 / 40000000000000 : ℝ) ≤ ex (1617 / 2000) 76 * sC 76 ∧ ex (1617 / 2000) 76 * sC 76 ≤ (12649786214651 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_76 sCB_76 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_76 : (118548153123951 / 1000000000000000 : ℝ) ≤ Real.log 76 * (ex (1617 / 2000) 76 * cC 76) ∧ Real.log 76 * (ex (1617 / 2000) 76 * cC 76) ≤ (118548172169433 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_76 eC_76 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_77 : (4343805421490343 / 1000000000000000 : ℝ) ≤ Real.log 77 ∧ Real.log 77 ≤ (4343805423194797 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_77
  constructor <;> linarith [h.1, h.2]

theorem eC_77 : (526477575879 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 77 * cC 77 ∧ ex (1617 / 2000) 77 * cC 77 ≤ (526481960619 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_77 cCB_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_77 : (149561246359 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 77 * cC 77) ∧ kappa * (ex (1617 / 2000) 77 * cC 77) ≤ (37390622993 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_77 : (29833527123951 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 77 * sC 77 ∧ ex (1617 / 2000) 77 * sC 77 ≤ (14916765774581 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_77 sCB_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_77 : (4237539929879 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 77 * sC 77) ∧ kappa * (ex (1617 / 2000) 77 * sC 77) ≤ (8475081116869 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_77 : (571729037099 / 250000000000000 : ℝ) ≤ Real.log 77 * (ex (1617 / 2000) 77 * cC 77) ∧ Real.log 77 * (ex (1617 / 2000) 77 * cC 77) ≤ (285866899469 / 125000000000000 : ℝ) := by
  exact mul_bounds_of lgB_77 eC_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_77 : (649664952779 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 77 * (ex (1617 / 2000) 77 * cC 77)) ∧ kappa * (Real.log 77 * (ex (1617 / 2000) 77 * cC 77)) ≤ (129934072747 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_78 : (4356708826321779 / 1000000000000000 : ℝ) ≤ Real.log 78 ∧ Real.log 78 ≤ (4356708828048589 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_78
  constructor <;> linarith [h.1, h.2]

theorem eC_78 : (-26155701102839 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 78 * cC 78 ∧ ex (1617 / 2000) 78 * cC 78 ≤ (-408682760507 / 15625000000000 : ℝ) := by
  exact mul_bounds_of exB_78 cCB_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_78 : (-7430286560271 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 78 * cC 78) ∧ kappa * (ex (1617 / 2000) 78 * cC 78) ≤ (-928785662711 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_78 : (13704458375287 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 78 * sC 78 ∧ ex (1617 / 2000) 78 * sC 78 ≤ (1713057848531 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_78 sCB_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_78 : (1946574715801 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 78 * sC 78) ∧ kappa * (ex (1617 / 2000) 78 * sC 78) ≤ (3893150685233 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_78 : (-113952773898539 / 1000000000000000 : ℝ) ≤ Real.log 78 * (ex (1617 / 2000) 78 * cC 78) ∧ Real.log 78 * (ex (1617 / 2000) 78 * cC 78) ≤ (-113952754551449 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_78 eC_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_78 : (-1618579752603 / 50000000000000 : ℝ) ≤ kappa * (Real.log 78 * (ex (1617 / 2000) 78 * cC 78)) ∧ kappa * (Real.log 78 * (ex (1617 / 2000) 78 * cC 78)) ≤ (-8092897388989 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_78 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_79 : (546180981511877 / 125000000000000 : ℝ) ≤ Real.log 79 ∧ Real.log 79 ≤ (4369447853842793 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_79
  constructor <;> linarith [h.1, h.2]

theorem eC_79 : (-5992525445419 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 79 * cC 79 ∧ ex (1617 / 2000) 79 * cC 79 ≤ (-4794019471111 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_79 cCB_79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_79 : (-1045059062051 / 62500000000000 : ℝ) ≤ ex (1617 / 2000) 79 * sC 79 ∧ ex (1617 / 2000) 79 * sC 79 ≤ (-16720940577113 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_79 sCB_79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_79 : (-52368054893169 / 500000000000000 : ℝ) ≤ Real.log 79 * (ex (1617 / 2000) 79 * cC 79) ∧ Real.log 79 * (ex (1617 / 2000) 79 * cC 79) ≤ (-52368045202369 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_79 eC_79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_81 : (4394449154292799 / 1000000000000000 : ℝ) ≤ Real.log 81 ∧ Real.log 81 ≤ (4394449156078747 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_81
  constructor <;> linarith [h.1, h.2]

theorem eC_81 : (13245744257471 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 81 * cC 81 ∧ ex (1617 / 2000) 81 * cC 81 ≤ (13245746475253 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_81 cCB_81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_81 : (-10886423301741 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 81 * sC 81 ∧ ex (1617 / 2000) 81 * sC 81 ≤ (-10886418888763 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_81 sCB_81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_81 : (29103874825111 / 250000000000000 : ℝ) ≤ Real.log 81 * (ex (1617 / 2000) 81 * cC 81) ∧ Real.log 81 * (ex (1617 / 2000) 81 * cC 81) ≤ (58207759419809 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_81 eC_81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_82 : (4406719246881137 / 1000000000000000 : ℝ) ≤ Real.log 82 ∧ Real.log 82 ≤ (4406719248684467 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_82
  constructor <;> linarith [h.1, h.2]

theorem eC_82 : (5593604960403 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 82 * cC 82 ∧ ex (1617 / 2000) 82 * cC 82 ≤ (22374424272237 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_82 cCB_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_82 : (6356103795089 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 82 * cC 82) ∧ kappa * (ex (1617 / 2000) 82 * cC 82) ≤ (6356105053737 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_82 : (8711819300247 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 82 * sC 82 ∧ ex (1617 / 2000) 82 * sC 82 ≤ (17423643023489 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_82 sCB_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_82 : (4949690593849 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 82 * sC 82) ∧ kappa * (ex (1617 / 2000) 82 * sC 82) ≤ (494969185033 / 100000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_82 : (9859778655383 / 100000000000000 : ℝ) ≤ Real.log 82 * (ex (1617 / 2000) 82 * cC 82) ∧ Real.log 82 * (ex (1617 / 2000) 82 * cC 82) ≤ (985978061187 / 10000000000000 : ℝ) := by
  exact mul_bounds_of lgB_82 eC_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_82 : (28009564928993 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 82 * (ex (1617 / 2000) 82 * cC 82)) ∧ kappa * (Real.log 82 * (ex (1617 / 2000) 82 * cC 82)) ≤ (28009570486963 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_83 : (4418840607410211 / 1000000000000000 : ℝ) ≤ Real.log 83 ∧ Real.log 83 ≤ (552355076153737 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_83
  constructor <;> linarith [h.1, h.2]

theorem eC_83 : (-3630123830349 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 83 * cC 83 ∧ ex (1617 / 2000) 83 * cC 83 ≤ (-1815059721961 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_83 cCB_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_83 : (-257810526687 / 250000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 83 * cC 83) ∧ kappa * (ex (1617 / 2000) 83 * cC 83) ≤ (-206248172131 / 200000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_83 : (27846204604879 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 83 * sC 83 ∧ ex (1617 / 2000) 83 * sC 83 ≤ (27846209027021 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_83 sCB_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_83 : (3955261589369 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 83 * sC 83) ∧ kappa * (ex (1617 / 2000) 83 * sC 83) ≤ (7910524434977 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_83 : (-50127933119 / 3125000000000 : ℝ) ≤ Real.log 83 * (ex (1617 / 2000) 83 * cC 83) ∧ Real.log 83 * (ex (1617 / 2000) 83 * cC 83) ≤ (-16040919208551 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_83 eC_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_83 : (-2278447249623 / 500000000000000 : ℝ) ≤ kappa * (Real.log 83 * (ex (1617 / 2000) 83 * cC 83)) ∧ kappa * (Real.log 83 * (ex (1617 / 2000) 83 * cC 83)) ≤ (-2278444495543 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_84 : (4430816798453847 / 1000000000000000 : ℝ) ≤ Real.log 84 ∧ Real.log 84 ≤ (443081680028893 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_84
  constructor <;> linarith [h.1, h.2]

theorem eC_84 : (-3181576209463 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 84 * cC 84 ∧ ex (1617 / 2000) 84 * cC 84 ≤ (-12726302631957 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_84 cCB_84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_84 : (280211124659 / 25000000000000 : ℝ) ≤ ex (1617 / 2000) 84 * sC 84 ∧ ex (1617 / 2000) 84 * sC 84 ≤ (5604224688481 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_84 sCB_84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_84 : (-56387925281153 / 500000000000000 : ℝ) ≤ Real.log 84 * (ex (1617 / 2000) 84 * cC 84) ∧ Real.log 84 * (ex (1617 / 2000) 84 * cC 84) ≤ (-28193957741941 / 250000000000000 : ℝ) := by
  exact mul_bounds_of lgB_84 eC_84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_86 : (1113586823964601 / 250000000000000 : ℝ) ≤ Real.log 86 ∧ Real.log 86 ≤ (2227173648860837 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_86
  constructor <;> linarith [h.1, h.2]

theorem eC_86 : (844069401859 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 86 * cC 86 ∧ ex (1617 / 2000) 86 * cC 86 ≤ (844073780087 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_86 cCB_86 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_86 : (-27274083198929 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 86 * sC 86 ∧ ex (1617 / 2000) 86 * sC 86 ≤ (-27274078780781 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_86 sCB_86 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_86 : (3759778257687 / 1000000000000000 : ℝ) ≤ Real.log 86 * (ex (1617 / 2000) 86 * cC 86) ∧ Real.log 86 * (ex (1617 / 2000) 86 * cC 86) ≤ (3759797761409 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_86 eC_86 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_87 : (2232954059128449 / 500000000000000 : ℝ) ≤ Real.log 87 ∧ Real.log 87 ≤ (178636324805323 / 40000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_87
  constructor <;> linarith [h.1, h.2]

theorem eC_87 : (4611835829743 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 87 * cC 87 ∧ ex (1617 / 2000) 87 * cC 87 ≤ (23059183550551 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_87 cCB_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_87 : (6550629564311 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 87 * cC 87) ∧ kappa * (ex (1617 / 2000) 87 * cC 87) ≤ (3275315407391 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_87 : (-7054648249361 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 87 * sC 87 ∧ ex (1617 / 2000) 87 * sC 87 ≤ (-705464605527 / 50000000000000 : ℝ) := by
  exact mul_bounds_of exB_87 sCB_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_87 : (-2004077729309 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 87 * sC 87) ∧ kappa * (ex (1617 / 2000) 87 * sC 87) ≤ (-4008154212027 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_87 : (51490087680293 / 500000000000000 : ℝ) ≤ Real.log 87 * (ex (1617 / 2000) 87 * cC 87) ∧ Real.log 87 * (ex (1617 / 2000) 87 * cC 87) ≤ (20596039012409 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_87 eC_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_87 : (29254509750953 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 87 * (ex (1617 / 2000) 87 * cC 87)) ∧ kappa * (Real.log 87 * (ex (1617 / 2000) 87 * cC 87)) ≤ (1170180613909 / 40000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_88 : (1119334203519521 / 250000000000000 : ℝ) ≤ Real.log 88 ∧ Real.log 88 ≤ (4477336815966447 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_88
  constructor <;> linarith [h.1, h.2]

theorem eC_88 : (760708146963 / 31250000000000 : ℝ) ≤ ex (1617 / 2000) 88 * cC 88 ∧ ex (1617 / 2000) 88 * cC 88 ≤ (24342665091669 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_88 cCB_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_88 : (6915239776987 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 88 * cC 88) ∧ kappa * (ex (1617 / 2000) 88 * cC 88) ≤ (6915241023769 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_88 : (5586847837739 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 88 * sC 88 ∧ ex (1617 / 2000) 88 * sC 88 ≤ (1396712505521 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_88 sCB_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_88 : (3174212783653 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 88 * sC 88) ∧ kappa * (ex (1617 / 2000) 88 * sC 88) ≤ (3174214024707 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_88 : (108990290917329 / 1000000000000000 : ℝ) ≤ Real.log 88 * (ex (1617 / 2000) 88 * cC 88) ∧ Real.log 88 * (ex (1617 / 2000) 88 * cC 88) ≤ (108990310613671 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_88 eC_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_88 : (30961857631683 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 88 * (ex (1617 / 2000) 88 * cC 88)) ∧ kappa * (Real.log 88 * (ex (1617 / 2000) 88 * cC 88)) ≤ (15480931613501 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_88 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_89 : (897727273865943 / 200000000000000 : ℝ) ≤ Real.log 89 ∧ Real.log 89 ≤ (448863637122959 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_89
  constructor <;> linarith [h.1, h.2]

theorem eC_89 : (227266701561 / 50000000000000 : ℝ) ≤ ex (1617 / 2000) 89 * cC 89 ∧ ex (1617 / 2000) 89 * cC 89 ≤ (2272669186231 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_89 cCB_89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_89 : (26148946378993 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 89 * sC 89 ∧ ex (1617 / 2000) 89 * sC 89 ≤ (13074475376757 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_89 sCB_89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_89 : (10201175821643 / 500000000000000 : ℝ) ≤ Real.log 89 * (ex (1617 / 2000) 89 * cC 89) ∧ Real.log 89 * (ex (1617 / 2000) 89 * cC 89) ≤ (20402371138179 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_89 eC_89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_91 : (4510859506110189 / 1000000000000000 : ℝ) ≤ Real.log 91 ∧ Real.log 91 ≤ (1127714877007811 / 250000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_91
  constructor <;> linarith [h.1, h.2]

theorem eC_91 : (-25728774672729 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 91 * cC 91 ∧ ex (1617 / 2000) 91 * cC 91 ≤ (-3216096291057 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_91 cCB_91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_91 : (-4194498884247 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 91 * sC 91 ∧ ex (1617 / 2000) 91 * sC 91 ≤ (-4194494573521 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_91 sCB_91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_91 : (-58029443931237 / 500000000000000 : ℝ) ≤ Real.log 91 * (ex (1617 / 2000) 91 * cC 91) ∧ Real.log 91 * (ex (1617 / 2000) 91 * cC 91) ≤ (-116058868216641 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_91 eC_91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_92 : (452178857664043 / 100000000000000 : ℝ) ≤ Real.log 92 ∧ Real.log 92 ≤ (452178857857123 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_92
  constructor <;> linarith [h.1, h.2]

theorem eC_92 : (-11761505739393 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 92 * cC 92 ∧ ex (1617 / 2000) 92 * cC 92 ≤ (-2352300284167 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_92 cCB_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_92 : (-3341197304571 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 92 * cC 92) ∧ kappa * (ex (1617 / 2000) 92 * cC 92) ≤ (-1670598038879 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_92 : (-23007101295731 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 92 * sC 92 ∧ ex (1617 / 2000) 92 * sC 92 ≤ (-23007096959557 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_92 sCB_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_92 : (-6535835337631 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 92 * sC 92) ∧ kappa * (ex (1617 / 2000) 92 * sC 92) ≤ (-3267917052907 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_92 : (-13295760579797 / 250000000000000 : ℝ) ≤ Real.log 92 * (ex (1617 / 2000) 92 * cC 92) ∧ Real.log 92 * (ex (1617 / 2000) 92 * cC 92) ≤ (-53183022768871 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_92 eC_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_92 : (-11803271727 / 781250000000 : ℝ) ≤ kappa * (Real.log 92 * (ex (1617 / 2000) 92 * cC 92)) ∧ kappa * (Real.log 92 * (ex (1617 / 2000) 92 * cC 92)) ≤ (-15108182256723 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_92 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_93 : (11331498731857 / 2500000000000 : ℝ) ≤ Real.log 93 ∧ Real.log 93 ≤ (453259949468283 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_93
  constructor <;> linarith [h.1, h.2]

theorem eC_93 : (280785790583 / 25000000000000 : ℝ) ≤ ex (1617 / 2000) 93 * cC 93 ∧ ex (1617 / 2000) 93 * cC 93 ≤ (5615717955001 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_93 cCB_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_93 : (3190614356511 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 93 * cC 93) ∧ kappa * (ex (1617 / 2000) 93 * cC 93) ≤ (3190615574269 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_93 : (-4604104564733 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 93 * sC 93 ∧ ex (1617 / 2000) 93 * sC 93 ≤ (-2302051851843 / 100000000000000 : ℝ) := by
  exact mul_bounds_of exB_93 sCB_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_93 : (-3269824056227 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 93 * sC 93) ∧ kappa * (ex (1617 / 2000) 93 * sC 93) ≤ (-3269823444713 / 500000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_93 : (10181516255727 / 200000000000000 : ℝ) ≤ Real.log 93 * (ex (1617 / 2000) 93 * cC 93) ∧ Real.log 93 * (ex (1617 / 2000) 93 * cC 93) ≤ (25453800365119 / 500000000000000 : ℝ) := by
  exact mul_bounds_of lgB_93 eC_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_93 : (7230888506931 / 500000000000000 : ℝ) ≤ kappa * (Real.log 93 * (ex (1617 / 2000) 93 * cC 93)) ∧ kappa * (Real.log 93 * (ex (1617 / 2000) 93 * cC 93)) ≤ (1807722817457 / 125000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_94 : (4543294781857799 / 1000000000000000 : ℝ) ≤ Real.log 94 ∧ Real.log 94 ≤ (181731791352263 / 40000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_94
  constructor <;> linarith [h.1, h.2]

theorem eC_94 : (24885975596749 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 94 * cC 94 ∧ ex (1617 / 2000) 94 * cC 94 ≤ (6221494972261 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_94 cCB_94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_94 : (-5052580075983 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 94 * sC 94 ∧ ex (1617 / 2000) 94 * sC 94 ≤ (-2526287907519 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_94 sCB_94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_94 : (2261286461403 / 20000000000000 : ℝ) ≤ Real.log 94 * (ex (1617 / 2000) 94 * cC 94) ∧ Real.log 94 * (ex (1617 / 2000) 94 * cC 94) ≤ (113064342619809 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_94 eC_94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_96 : (4564348191052399 / 1000000000000000 : ℝ) ≤ Real.log 96 ∧ Real.log 96 ≤ (570543524127167 / 125000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_96
  constructor <;> linarith [h.1, h.2]

theorem eC_96 : (-827684945579 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 96 * cC 96 ∧ ex (1617 / 2000) 96 * cC 96 ≤ (-206920181633 / 250000000000000 : ℝ) := by
  exact mul_bounds_of exB_96 cCB_96 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_96 : (4990279330527 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 96 * sC 96 ∧ ex (1617 / 2000) 96 * sC 96 ≤ (4990280182027 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_96 sCB_96 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_96 : (-1888921142871 / 500000000000000 : ℝ) ≤ Real.log 96 * (ex (1617 / 2000) 96 * cC 96) ∧ Real.log 96 * (ex (1617 / 2000) 96 * cC 96) ≤ (-755564605383 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_96 eC_96 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_97 : (1143677744521613 / 250000000000000 : ℝ) ≤ Real.log 97 ∧ Real.log 97 ≤ (2287355490029429 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_97
  constructor <;> linarith [h.1, h.2]

theorem eC_97 : (-19715208062047 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 97 * cC 97 ∧ ex (1617 / 2000) 97 * cC 97 ≤ (-2464400479959 / 125000000000000 : ℝ) := by
  exact mul_bounds_of exB_97 cCB_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_97 : (-2800338727691 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 97 * cC 97) ∧ kappa * (ex (1617 / 2000) 97 * cC 97) ≤ (-1400169063973 / 250000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_97 : (748684302897 / 50000000000000 : ℝ) ≤ ex (1617 / 2000) 97 * sC 97 ∧ ex (1617 / 2000) 97 * sC 97 ≤ (14973690272451 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_97 sCB_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_97 : (2126855209053 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 97 * sC 97) ∧ kappa * (ex (1617 / 2000) 97 * sC 97) ≤ (4253711615361 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_97 : (-11273922349449 / 125000000000000 : ℝ) ≤ Real.log 97 * (ex (1617 / 2000) 97 * cC 97) ∧ Real.log 97 * (ex (1617 / 2000) 97 * cC 97) ≤ (-90191359440559 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_97 eC_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_97 : (-25621480650901 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 97 * (ex (1617 / 2000) 97 * cC 97)) ∧ kappa * (Real.log 97 * (ex (1617 / 2000) 97 * cC 97)) ≤ (-1281073757627 / 50000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_98 : (2292483739126111 / 500000000000000 : ℝ) ≤ Real.log 98 ∧ Real.log 98 ≤ (2292483740115861 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_98
  constructor <;> linarith [h.1, h.2]

theorem eC_98 : (-5977267125983 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 98 * cC 98 ∧ ex (1617 / 2000) 98 * cC 98 ≤ (-11954532148311 / 500000000000000 : ℝ) := by
  exact mul_bounds_of exB_98 cCB_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keC_98 : (-212252041241 / 31250000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 98 * cC 98) ∧ kappa * (ex (1617 / 2000) 98 * cC 98) ≤ (-6792064124503 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eC_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_98 : (-2791785511837 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 98 * sC 98 ∧ ex (1617 / 2000) 98 * sC 98 ≤ (-5583566845797 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_98 sCB_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keS_98 : (-1586175517621 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 98 * sC 98) ∧ kappa * (ex (1617 / 2000) 98 * sC 98) ≤ (-1586174330773 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB eS_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_98 : (-109622301573161 / 1000000000000000 : ℝ) ≤ Real.log 98 * (ex (1617 / 2000) 98 * cC 98) ∧ Real.log 98 * (ex (1617 / 2000) 98 * cC 98) ≤ (-109622282235453 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of lgB_98 eC_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem kleC_98 : (-31141398614489 / 1000000000000000 : ℝ) ≤ kappa * (Real.log 98 * (ex (1617 / 2000) 98 * cC 98)) ∧ kappa * (Real.log 98 * (ex (1617 / 2000) 98 * cC 98)) ≤ (-31141393121051 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of kappaB leC_98 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_99 : (1148779962428723 / 250000000000000 : ℝ) ≤ Real.log 99 ∧ Real.log 99 ≤ (4595119851701133 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_99
  constructor <;> linarith [h.1, h.2]

theorem eC_99 : (-11057267417511 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 99 * cC 99 ∧ ex (1617 / 2000) 99 * cC 99 ≤ (-2211452648359 / 200000000000000 : ℝ) := by
  exact mul_bounds_of exB_99 cCB_99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eS_99 : (-1356035897723 / 62500000000000 : ℝ) ≤ ex (1617 / 2000) 99 * sC 99 ∧ ex (1617 / 2000) 99 * sC 99 ≤ (-21696570170699 / 1000000000000000 : ℝ) := by
  exact mul_bounds_of exB_99 sCB_99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem leC_99 : (-50809469015773 / 1000000000000000 : ℝ) ≤ Real.log 99 * (ex (1617 / 2000) 99 * cC 99) ∧ Real.log 99 * (ex (1617 / 2000) 99 * cC 99) ≤ (-10161889961179 / 200000000000000 : ℝ) := by
  exact mul_bounds_of lgB_99 eC_99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lgB_101 : (4615120516419061 / 1000000000000000 : ℝ) ≤ Real.log 101 ∧ Real.log 101 ≤ (2307560259208903 / 500000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_101
  constructor <;> linarith [h.1, h.2]

theorem lgB_102 : (289060800803807 / 62500000000000 : ℝ) ≤ Real.log 102 ∧ Real.log 102 ≤ (4624972814865459 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_102
  constructor <;> linarith [h.1, h.2]

theorem lgB_103 : (1158682246951293 / 250000000000000 : ℝ) ≤ Real.log 103 ∧ Real.log 103 ≤ (4634728989815243 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_103
  constructor <;> linarith [h.1, h.2]

theorem lgB_104 : (290274431169741 / 62500000000000 : ℝ) ≤ Real.log 104 ∧ Real.log 104 ≤ (464439090073119 / 100000000000000 : ℝ) := by
  have h := PsiOmega.Num.log_bound_104
  constructor <;> linarith [h.1, h.2]

theorem PReB_0 : (56846322957087 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 1 * cC 1 + kappa * (ex (1617 / 2000) 2 * cC 2) - kappa * (ex (1617 / 2000) 3 * cC 3) - ex (1617 / 2000) 4 * cC 4 ∧ ex (1617 / 2000) 1 * cC 1 + kappa * (ex (1617 / 2000) 2 * cC 2) - kappa * (ex (1617 / 2000) 3 * cC 3) - ex (1617 / 2000) 4 * cC 4 ≤ (90954119546337 / 200000000000000 : ℝ) := by
  have h0 : ex (1617 / 2000) 1 * cC 1 = (1 : ℝ) := by rw [ex_one, cC_one]; norm_num
  have h1 := keC_2
  have h2 := keC_3
  have h3 := eC_4
  constructor <;> linarith [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_1 : (-406293348843887 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 6 * cC 6 + kappa * (ex (1617 / 2000) 7 * cC 7) - kappa * (ex (1617 / 2000) 8 * cC 8) - ex (1617 / 2000) 9 * cC 9 ∧ ex (1617 / 2000) 6 * cC 6 + kappa * (ex (1617 / 2000) 7 * cC 7) - kappa * (ex (1617 / 2000) 8 * cC 8) - ex (1617 / 2000) 9 * cC 9 ≤ (-101573332830067 / 250000000000000 : ℝ) := by
  have h0 := eC_6
  have h1 := keC_7
  have h2 := keC_8
  have h3 := eC_9
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_2 : (-3267557445723 / 20000000000000 : ℝ) ≤ ex (1617 / 2000) 11 * cC 11 + kappa * (ex (1617 / 2000) 12 * cC 12) - kappa * (ex (1617 / 2000) 13 * cC 13) - ex (1617 / 2000) 14 * cC 14 ∧ ex (1617 / 2000) 11 * cC 11 + kappa * (ex (1617 / 2000) 12 * cC 12) - kappa * (ex (1617 / 2000) 13 * cC 13) - ex (1617 / 2000) 14 * cC 14 ≤ (-81688929669907 / 500000000000000 : ℝ) := by
  have h0 := eC_11
  have h1 := keC_12
  have h2 := keC_13
  have h3 := eC_14
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_3 : (82192699909 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 16 * cC 16 + kappa * (ex (1617 / 2000) 17 * cC 17) - kappa * (ex (1617 / 2000) 18 * cC 18) - ex (1617 / 2000) 19 * cC 19 ∧ ex (1617 / 2000) 16 * cC 16 + kappa * (ex (1617 / 2000) 17 * cC 17) - kappa * (ex (1617 / 2000) 18 * cC 18) - ex (1617 / 2000) 19 * cC 19 ≤ (410976008237 / 1000000000000000 : ℝ) := by
  have h0 := eC_16
  have h1 := keC_17
  have h2 := keC_18
  have h3 := eC_19
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_4 : (-15111017819217 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 21 * cC 21 + kappa * (ex (1617 / 2000) 22 * cC 22) - kappa * (ex (1617 / 2000) 23 * cC 23) - ex (1617 / 2000) 24 * cC 24 ∧ ex (1617 / 2000) 21 * cC 21 + kappa * (ex (1617 / 2000) 22 * cC 22) - kappa * (ex (1617 / 2000) 23 * cC 23) - ex (1617 / 2000) 24 * cC 24 ≤ (-30222023882801 / 1000000000000000 : ℝ) := by
  have h0 := eC_21
  have h1 := keC_22
  have h2 := keC_23
  have h3 := eC_24
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_5 : (-88460137585533 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 26 * cC 26 + kappa * (ex (1617 / 2000) 27 * cC 27) - kappa * (ex (1617 / 2000) 28 * cC 28) - ex (1617 / 2000) 29 * cC 29 ∧ ex (1617 / 2000) 26 * cC 26 + kappa * (ex (1617 / 2000) 27 * cC 27) - kappa * (ex (1617 / 2000) 28 * cC 28) - ex (1617 / 2000) 29 * cC 29 ≤ (-88460127351541 / 1000000000000000 : ℝ) := by
  have h0 := eC_26
  have h1 := keC_27
  have h2 := keC_28
  have h3 := eC_29
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_6 : (-16756684937 / 1562500000000 : ℝ) ≤ ex (1617 / 2000) 31 * cC 31 + kappa * (ex (1617 / 2000) 32 * cC 32) - kappa * (ex (1617 / 2000) 33 * cC 33) - ex (1617 / 2000) 34 * cC 34 ∧ ex (1617 / 2000) 31 * cC 31 + kappa * (ex (1617 / 2000) 32 * cC 32) - kappa * (ex (1617 / 2000) 33 * cC 33) - ex (1617 / 2000) 34 * cC 34 ≤ (-1072426945733 / 100000000000000 : ℝ) := by
  have h0 := eC_31
  have h1 := keC_32
  have h2 := keC_33
  have h3 := eC_34
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_7 : (322208209 / 62500000000000 : ℝ) ≤ ex (1617 / 2000) 36 * cC 36 + kappa * (ex (1617 / 2000) 37 * cC 37) - kappa * (ex (1617 / 2000) 38 * cC 38) - ex (1617 / 2000) 39 * cC 39 ∧ ex (1617 / 2000) 36 * cC 36 + kappa * (ex (1617 / 2000) 37 * cC 37) - kappa * (ex (1617 / 2000) 38 * cC 38) - ex (1617 / 2000) 39 * cC 39 ≤ (2581659611 / 500000000000000 : ℝ) := by
  have h0 := eC_36
  have h1 := keC_37
  have h2 := keC_38
  have h3 := eC_39
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_8 : (24397870062493 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 41 * cC 41 + kappa * (ex (1617 / 2000) 42 * cC 42) - kappa * (ex (1617 / 2000) 43 * cC 43) - ex (1617 / 2000) 44 * cC 44 ∧ ex (1617 / 2000) 41 * cC 41 + kappa * (ex (1617 / 2000) 42 * cC 42) - kappa * (ex (1617 / 2000) 43 * cC 43) - ex (1617 / 2000) 44 * cC 44 ≤ (24397877266459 / 1000000000000000 : ℝ) := by
  have h0 := eC_41
  have h1 := keC_42
  have h2 := keC_43
  have h3 := eC_44
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_9 : (-5696745972577 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 46 * cC 46 + kappa * (ex (1617 / 2000) 47 * cC 47) - kappa * (ex (1617 / 2000) 48 * cC 48) - ex (1617 / 2000) 49 * cC 49 ∧ ex (1617 / 2000) 46 * cC 46 + kappa * (ex (1617 / 2000) 47 * cC 47) - kappa * (ex (1617 / 2000) 48 * cC 48) - ex (1617 / 2000) 49 * cC 49 ≤ (-11393490293893 / 250000000000000 : ℝ) := by
  have h0 := eC_46
  have h1 := keC_47
  have h2 := keC_48
  have h3 := eC_49
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_10 : (3442141905697 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 51 * cC 51 + kappa * (ex (1617 / 2000) 52 * cC 52) - kappa * (ex (1617 / 2000) 53 * cC 53) - ex (1617 / 2000) 54 * cC 54 ∧ ex (1617 / 2000) 51 * cC 51 + kappa * (ex (1617 / 2000) 52 * cC 52) - kappa * (ex (1617 / 2000) 53 * cC 53) - ex (1617 / 2000) 54 * cC 54 ≤ (6884289887927 / 1000000000000000 : ℝ) := by
  have h0 := eC_51
  have h1 := keC_52
  have h2 := keC_53
  have h3 := eC_54
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_11 : (18481712463039 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 56 * cC 56 + kappa * (ex (1617 / 2000) 57 * cC 57) - kappa * (ex (1617 / 2000) 58 * cC 58) - ex (1617 / 2000) 59 * cC 59 ∧ ex (1617 / 2000) 56 * cC 56 + kappa * (ex (1617 / 2000) 57 * cC 57) - kappa * (ex (1617 / 2000) 58 * cC 58) - ex (1617 / 2000) 59 * cC 59 ≤ (36963428099159 / 500000000000000 : ℝ) := by
  have h0 := eC_56
  have h1 := keC_57
  have h2 := keC_58
  have h3 := eC_59
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_12 : (1813286394011 / 40000000000000 : ℝ) ≤ ex (1617 / 2000) 61 * cC 61 + kappa * (ex (1617 / 2000) 62 * cC 62) - kappa * (ex (1617 / 2000) 63 * cC 63) - ex (1617 / 2000) 64 * cC 64 ∧ ex (1617 / 2000) 61 * cC 61 + kappa * (ex (1617 / 2000) 62 * cC 62) - kappa * (ex (1617 / 2000) 63 * cC 63) - ex (1617 / 2000) 64 * cC 64 ≤ (45332168645257 / 1000000000000000 : ℝ) := by
  have h0 := eC_61
  have h1 := keC_62
  have h2 := keC_63
  have h3 := eC_64
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_13 : (23892215098607 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 66 * cC 66 + kappa * (ex (1617 / 2000) 67 * cC 67) - kappa * (ex (1617 / 2000) 68 * cC 68) - ex (1617 / 2000) 69 * cC 69 ∧ ex (1617 / 2000) 66 * cC 66 + kappa * (ex (1617 / 2000) 67 * cC 67) - kappa * (ex (1617 / 2000) 68 * cC 68) - ex (1617 / 2000) 69 * cC 69 ≤ (23892225378197 / 1000000000000000 : ℝ) := by
  have h0 := eC_66
  have h1 := keC_67
  have h2 := keC_68
  have h3 := eC_69
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_14 : (3317168379121 / 100000000000000 : ℝ) ≤ ex (1617 / 2000) 71 * cC 71 + kappa * (ex (1617 / 2000) 72 * cC 72) - kappa * (ex (1617 / 2000) 73 * cC 73) - ex (1617 / 2000) 74 * cC 74 ∧ ex (1617 / 2000) 71 * cC 71 + kappa * (ex (1617 / 2000) 72 * cC 72) - kappa * (ex (1617 / 2000) 73 * cC 73) - ex (1617 / 2000) 74 * cC 74 ≤ (33171694775447 / 1000000000000000 : ℝ) := by
  have h0 := eC_71
  have h1 := keC_72
  have h2 := keC_73
  have h3 := eC_74
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_15 : (58923634181639 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 76 * cC 76 + kappa * (ex (1617 / 2000) 77 * cC 77) - kappa * (ex (1617 / 2000) 78 * cC 78) - ex (1617 / 2000) 79 * cC 79 ∧ ex (1617 / 2000) 76 * cC 76 + kappa * (ex (1617 / 2000) 77 * cC 77) - kappa * (ex (1617 / 2000) 78 * cC 78) - ex (1617 / 2000) 79 * cC 79 ≤ (58923645499083 / 1000000000000000 : ℝ) := by
  have h0 := eC_76
  have h1 := keC_77
  have h2 := keC_78
  have h3 := eC_79
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_16 : (296657192173 / 5000000000000 : ℝ) ≤ ex (1617 / 2000) 81 * cC 81 + kappa * (ex (1617 / 2000) 82 * cC 82) - kappa * (ex (1617 / 2000) 83 * cC 83) - ex (1617 / 2000) 84 * cC 84 ∧ ex (1617 / 2000) 81 * cC 81 + kappa * (ex (1617 / 2000) 82 * cC 82) - kappa * (ex (1617 / 2000) 83 * cC 83) - ex (1617 / 2000) 84 * cC 84 ≤ (11866289957339 / 200000000000000 : ℝ) := by
  have h0 := eC_81
  have h1 := keC_82
  have h2 := keC_83
  have h3 := eC_84
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_17 : (-4065880430061 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 86 * cC 86 + kappa * (ex (1617 / 2000) 87 * cC 87) - kappa * (ex (1617 / 2000) 88 * cC 88) - ex (1617 / 2000) 89 * cC 89 ∧ ex (1617 / 2000) 86 * cC 86 + kappa * (ex (1617 / 2000) 87 * cC 87) - kappa * (ex (1617 / 2000) 88 * cC 88) - ex (1617 / 2000) 89 * cC 89 ≤ (-2032934606669 / 500000000000000 : ℝ) := by
  have h0 := eC_86
  have h1 := keC_87
  have h2 := keC_88
  have h3 := eC_89
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_18 : (-57146567440613 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 91 * cC 91 + kappa * (ex (1617 / 2000) 92 * cC 92) - kappa * (ex (1617 / 2000) 93 * cC 93) - ex (1617 / 2000) 94 * cC 94 ∧ ex (1617 / 2000) 91 * cC 91 + kappa * (ex (1617 / 2000) 92 * cC 92) - kappa * (ex (1617 / 2000) 93 * cC 93) - ex (1617 / 2000) 94 * cC 94 ≤ (-28573278179737 / 500000000000000 : ℝ) := by
  have h0 := eC_91
  have h1 := keC_92
  have h2 := keC_93
  have h3 := eC_94
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReB_19 : (11420964965337 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 96 * cC 96 + kappa * (ex (1617 / 2000) 97 * cC 97) - kappa * (ex (1617 / 2000) 98 * cC 98) - ex (1617 / 2000) 99 * cC 99 ∧ ex (1617 / 2000) 96 * cC 96 + kappa * (ex (1617 / 2000) 97 * cC 97) - kappa * (ex (1617 / 2000) 98 * cC 98) - ex (1617 / 2000) 99 * cC 99 ≤ (11420975754799 / 1000000000000000 : ℝ) := by
  have h0 := eC_96
  have h1 := keC_97
  have h2 := keC_98
  have h3 := eC_99
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_0 : (117518888390233 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 1 * sC 1 + kappa * (ex (1617 / 2000) 2 * sC 2) - kappa * (ex (1617 / 2000) 3 * sC 3) - ex (1617 / 2000) 4 * sC 4 ∧ ex (1617 / 2000) 1 * sC 1 + kappa * (ex (1617 / 2000) 2 * sC 2) - kappa * (ex (1617 / 2000) 3 * sC 3) - ex (1617 / 2000) 4 * sC 4 ≤ (117518895395857 / 500000000000000 : ℝ) := by
  have h0 : ex (1617 / 2000) 1 * sC 1 = (0 : ℝ) := by rw [sC_one]; norm_num
  have h1 := keS_2
  have h2 := keS_3
  have h3 := eS_4
  constructor <;> linarith [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_1 : (16455633692671 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 6 * sC 6 + kappa * (ex (1617 / 2000) 7 * sC 7) - kappa * (ex (1617 / 2000) 8 * sC 8) - ex (1617 / 2000) 9 * sC 9 ∧ ex (1617 / 2000) 6 * sC 6 + kappa * (ex (1617 / 2000) 7 * sC 7) - kappa * (ex (1617 / 2000) 8 * sC 8) - ex (1617 / 2000) 9 * sC 9 ≤ (65822552201429 / 1000000000000000 : ℝ) := by
  have h0 := eS_6
  have h1 := keS_7
  have h2 := keS_8
  have h3 := eS_9
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_2 : (-77631694126437 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 11 * sC 11 + kappa * (ex (1617 / 2000) 12 * sC 12) - kappa * (ex (1617 / 2000) 13 * sC 13) - ex (1617 / 2000) 14 * sC 14 ∧ ex (1617 / 2000) 11 * sC 11 + kappa * (ex (1617 / 2000) 12 * sC 12) - kappa * (ex (1617 / 2000) 13 * sC 13) - ex (1617 / 2000) 14 * sC 14 ≤ (-155263375326563 / 1000000000000000 : ℝ) := by
  have h0 := eS_11
  have h1 := keS_12
  have h2 := keS_13
  have h3 := eS_14
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_3 : (-210682239025069 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 16 * sC 16 + kappa * (ex (1617 / 2000) 17 * sC 17) - kappa * (ex (1617 / 2000) 18 * sC 18) - ex (1617 / 2000) 19 * sC 19 ∧ ex (1617 / 2000) 16 * sC 16 + kappa * (ex (1617 / 2000) 17 * sC 17) - kappa * (ex (1617 / 2000) 18 * sC 18) - ex (1617 / 2000) 19 * sC 19 ≤ (-52670556620577 / 250000000000000 : ℝ) := by
  have h0 := eS_16
  have h1 := keS_17
  have h2 := keS_18
  have h3 := eS_19
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_4 : (-34381978884847 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 21 * sC 21 + kappa * (ex (1617 / 2000) 22 * sC 22) - kappa * (ex (1617 / 2000) 23 * sC 23) - ex (1617 / 2000) 24 * sC 24 ∧ ex (1617 / 2000) 21 * sC 21 + kappa * (ex (1617 / 2000) 22 * sC 22) - kappa * (ex (1617 / 2000) 23 * sC 23) - ex (1617 / 2000) 24 * sC 24 ≤ (-34381967140769 / 1000000000000000 : ℝ) := by
  have h0 := eS_21
  have h1 := keS_22
  have h2 := keS_23
  have h3 := eS_24
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_5 : (43952288858427 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 26 * sC 26 + kappa * (ex (1617 / 2000) 27 * sC 27) - kappa * (ex (1617 / 2000) 28 * sC 28) - ex (1617 / 2000) 29 * sC 29 ∧ ex (1617 / 2000) 26 * sC 26 + kappa * (ex (1617 / 2000) 27 * sC 27) - kappa * (ex (1617 / 2000) 28 * sC 28) - ex (1617 / 2000) 29 * sC 29 ≤ (21976149520623 / 500000000000000 : ℝ) := by
  have h0 := eS_26
  have h1 := keS_27
  have h2 := keS_28
  have h3 := eS_29
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_6 : (-6695941912431 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 31 * sC 31 + kappa * (ex (1617 / 2000) 32 * sC 32) - kappa * (ex (1617 / 2000) 33 * sC 33) - ex (1617 / 2000) 34 * sC 34 ∧ ex (1617 / 2000) 31 * sC 31 + kappa * (ex (1617 / 2000) 32 * sC 32) - kappa * (ex (1617 / 2000) 33 * sC 33) - ex (1617 / 2000) 34 * sC 34 ≤ (-13391881595181 / 250000000000000 : ℝ) := by
  have h0 := eS_31
  have h1 := keS_32
  have h2 := keS_33
  have h3 := eS_34
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_7 : (-803714975951 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 36 * sC 36 + kappa * (ex (1617 / 2000) 37 * sC 37) - kappa * (ex (1617 / 2000) 38 * sC 38) - ex (1617 / 2000) 39 * sC 39 ∧ ex (1617 / 2000) 36 * sC 36 + kappa * (ex (1617 / 2000) 37 * sC 37) - kappa * (ex (1617 / 2000) 38 * sC 38) - ex (1617 / 2000) 39 * sC 39 ≤ (-3214851936431 / 1000000000000000 : ℝ) := by
  have h0 := eS_36
  have h1 := keS_37
  have h2 := keS_38
  have h3 := eS_39
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_8 : (-24156963787 / 1000000000000 : ℝ) ≤ ex (1617 / 2000) 41 * sC 41 + kappa * (ex (1617 / 2000) 42 * sC 42) - kappa * (ex (1617 / 2000) 43 * sC 43) - ex (1617 / 2000) 44 * sC 44 ∧ ex (1617 / 2000) 41 * sC 41 + kappa * (ex (1617 / 2000) 42 * sC 42) - kappa * (ex (1617 / 2000) 43 * sC 43) - ex (1617 / 2000) 44 * sC 44 ≤ (-12078478291227 / 500000000000000 : ℝ) := by
  have h0 := eS_41
  have h1 := keS_42
  have h2 := keS_43
  have h3 := eS_44
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_9 : (1355743843353 / 40000000000000 : ℝ) ≤ ex (1617 / 2000) 46 * sC 46 + kappa * (ex (1617 / 2000) 47 * sC 47) - kappa * (ex (1617 / 2000) 48 * sC 48) - ex (1617 / 2000) 49 * sC 49 ∧ ex (1617 / 2000) 46 * sC 46 + kappa * (ex (1617 / 2000) 47 * sC 47) - kappa * (ex (1617 / 2000) 48 * sC 48) - ex (1617 / 2000) 49 * sC 49 ≤ (8473400674437 / 250000000000000 : ℝ) := by
  have h0 := eS_46
  have h1 := keS_47
  have h2 := keS_48
  have h3 := eS_49
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_10 : (-68435282541693 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 51 * sC 51 + kappa * (ex (1617 / 2000) 52 * sC 52) - kappa * (ex (1617 / 2000) 53 * sC 53) - ex (1617 / 2000) 54 * sC 54 ∧ ex (1617 / 2000) 51 * sC 51 + kappa * (ex (1617 / 2000) 52 * sC 52) - kappa * (ex (1617 / 2000) 53 * sC 53) - ex (1617 / 2000) 54 * sC 54 ≤ (-34217638233563 / 500000000000000 : ℝ) := by
  have h0 := eS_51
  have h1 := keS_52
  have h2 := keS_53
  have h3 := eS_54
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_11 : (1971036988211 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 56 * sC 56 + kappa * (ex (1617 / 2000) 57 * sC 57) - kappa * (ex (1617 / 2000) 58 * sC 58) - ex (1617 / 2000) 59 * sC 59 ∧ ex (1617 / 2000) 56 * sC 56 + kappa * (ex (1617 / 2000) 57 * sC 57) - kappa * (ex (1617 / 2000) 58 * sC 58) - ex (1617 / 2000) 59 * sC 59 ≤ (98552007839 / 25000000000000 : ℝ) := by
  have h0 := eS_56
  have h1 := keS_57
  have h2 := keS_58
  have h3 := eS_59
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_12 : (59971806247747 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 61 * sC 61 + kappa * (ex (1617 / 2000) 62 * sC 62) - kappa * (ex (1617 / 2000) 63 * sC 63) - ex (1617 / 2000) 64 * sC 64 ∧ ex (1617 / 2000) 61 * sC 61 + kappa * (ex (1617 / 2000) 62 * sC 62) - kappa * (ex (1617 / 2000) 63 * sC 63) - ex (1617 / 2000) 64 * sC 64 ≤ (11994363010891 / 200000000000000 : ℝ) := by
  have h0 := eS_61
  have h1 := keS_62
  have h2 := keS_63
  have h3 := eS_64
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_13 : (17486873022727 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 66 * sC 66 + kappa * (ex (1617 / 2000) 67 * sC 67) - kappa * (ex (1617 / 2000) 68 * sC 68) - ex (1617 / 2000) 69 * sC 69 ∧ ex (1617 / 2000) 66 * sC 66 + kappa * (ex (1617 / 2000) 67 * sC 67) - kappa * (ex (1617 / 2000) 68 * sC 68) - ex (1617 / 2000) 69 * sC 69 ≤ (874343780141 / 12500000000000 : ℝ) := by
  have h0 := eS_66
  have h1 := keS_67
  have h2 := keS_68
  have h3 := eS_69
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_14 : (63122227786317 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 71 * sC 71 + kappa * (ex (1617 / 2000) 72 * sC 72) - kappa * (ex (1617 / 2000) 73 * sC 73) - ex (1617 / 2000) 74 * sC 74 ∧ ex (1617 / 2000) 71 * sC 71 + kappa * (ex (1617 / 2000) 72 * sC 72) - kappa * (ex (1617 / 2000) 73 * sC 73) - ex (1617 / 2000) 74 * sC 74 ≤ (15780559699717 / 250000000000000 : ℝ) := by
  have h0 := eS_71
  have h1 := keS_72
  have h2 := keS_73
  have h3 := eS_74
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_15 : (33952651599213 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 76 * sC 76 + kappa * (ex (1617 / 2000) 77 * sC 77) - kappa * (ex (1617 / 2000) 78 * sC 78) - ex (1617 / 2000) 79 * sC 79 ∧ ex (1617 / 2000) 76 * sC 76 + kappa * (ex (1617 / 2000) 77 * sC 77) - kappa * (ex (1617 / 2000) 78 * sC 78) - ex (1617 / 2000) 79 * sC 79 ≤ (16976331446367 / 500000000000000 : ℝ) := by
  have h0 := eS_76
  have h1 := keS_77
  have h2 := keS_78
  have h3 := eS_79
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_16 : (-25055706519831 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 81 * sC 81 + kappa * (ex (1617 / 2000) 82 * sC 82) - kappa * (ex (1617 / 2000) 83 * sC 83) - ex (1617 / 2000) 84 * sC 84 ∧ ex (1617 / 2000) 81 * sC 81 + kappa * (ex (1617 / 2000) 82 * sC 82) - kappa * (ex (1617 / 2000) 83 * sC 83) - ex (1617 / 2000) 84 * sC 84 ≤ (-25055695203531 / 1000000000000000 : ℝ) := by
  have h0 := eS_81
  have h1 := keS_82
  have h2 := keS_83
  have h3 := eS_84
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_17 : (-7575675429471 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 86 * sC 86 + kappa * (ex (1617 / 2000) 87 * sC 87) - kappa * (ex (1617 / 2000) 88 * sC 88) - ex (1617 / 2000) 89 * sC 89 ∧ ex (1617 / 2000) 86 * sC 86 + kappa * (ex (1617 / 2000) 87 * sC 87) - kappa * (ex (1617 / 2000) 88 * sC 88) - ex (1617 / 2000) 89 * sC 89 ≤ (-30302696077727 / 500000000000000 : ℝ) := by
  have h0 := eS_86
  have h1 := keS_87
  have h2 := keS_88
  have h3 := eS_89
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_18 : (430944241293 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 91 * sC 91 + kappa * (ex (1617 / 2000) 92 * sC 92) - kappa * (ex (1617 / 2000) 93 * sC 93) - ex (1617 / 2000) 94 * sC 94 ∧ ex (1617 / 2000) 91 * sC 91 + kappa * (ex (1617 / 2000) 92 * sC 92) - kappa * (ex (1617 / 2000) 93 * sC 93) - ex (1617 / 2000) 94 * sC 94 ≤ (430949754551 / 500000000000000 : ℝ) := by
  have h0 := eS_91
  have h1 := keS_92
  have h2 := keS_93
  have h3 := eS_94
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PImB_19 : (52487851572213 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 96 * sC 96 + kappa * (ex (1617 / 2000) 97 * sC 97) - kappa * (ex (1617 / 2000) 98 * sC 98) - ex (1617 / 2000) 99 * sC 99 ∧ ex (1617 / 2000) 96 * sC 96 + kappa * (ex (1617 / 2000) 97 * sC 97) - kappa * (ex (1617 / 2000) 98 * sC 98) - ex (1617 / 2000) 99 * sC 99 ≤ (10497572481337 / 200000000000000 : ℝ) := by
  have h0 := eS_96
  have h1 := keS_97
  have h2 := keS_98
  have h3 := eS_99
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_0 : (-307294792452863 / 500000000000000 : ℝ) ≤ Real.log 1 * (ex (1617 / 2000) 1 * cC 1) + kappa * (Real.log 2 * (ex (1617 / 2000) 2 * cC 2)) - kappa * (Real.log 3 * (ex (1617 / 2000) 3 * cC 3)) - Real.log 4 * (ex (1617 / 2000) 4 * cC 4) ∧ Real.log 1 * (ex (1617 / 2000) 1 * cC 1) + kappa * (Real.log 2 * (ex (1617 / 2000) 2 * cC 2)) - kappa * (Real.log 3 * (ex (1617 / 2000) 3 * cC 3)) - Real.log 4 * (ex (1617 / 2000) 4 * cC 4) ≤ (-122917913616153 / 200000000000000 : ℝ) := by
  have h0 : Real.log 1 * (ex (1617 / 2000) 1 * cC 1) = (0 : ℝ) := by rw [Real.log_one]; norm_num
  have h1 := kleC_2
  have h2 := kleC_3
  have h3 := leC_4
  constructor <;> linarith [h0, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_1 : (-794200314139757 / 1000000000000000 : ℝ) ≤ Real.log 6 * (ex (1617 / 2000) 6 * cC 6) + kappa * (Real.log 7 * (ex (1617 / 2000) 7 * cC 7)) - kappa * (Real.log 8 * (ex (1617 / 2000) 8 * cC 8)) - Real.log 9 * (ex (1617 / 2000) 9 * cC 9) ∧ Real.log 6 * (ex (1617 / 2000) 6 * cC 6) + kappa * (Real.log 7 * (ex (1617 / 2000) 7 * cC 7)) - kappa * (Real.log 8 * (ex (1617 / 2000) 8 * cC 8)) - Real.log 9 * (ex (1617 / 2000) 9 * cC 9) ≤ (-397100139568313 / 500000000000000 : ℝ) := by
  have h0 := leC_6
  have h1 := kleC_7
  have h2 := kleC_8
  have h3 := leC_9
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_2 : (-105912800912241 / 250000000000000 : ℝ) ≤ Real.log 11 * (ex (1617 / 2000) 11 * cC 11) + kappa * (Real.log 12 * (ex (1617 / 2000) 12 * cC 12)) - kappa * (Real.log 13 * (ex (1617 / 2000) 13 * cC 13)) - Real.log 14 * (ex (1617 / 2000) 14 * cC 14) ∧ Real.log 11 * (ex (1617 / 2000) 11 * cC 11) + kappa * (Real.log 12 * (ex (1617 / 2000) 12 * cC 12)) - kappa * (Real.log 13 * (ex (1617 / 2000) 13 * cC 13)) - Real.log 14 * (ex (1617 / 2000) 14 * cC 14) ≤ (-211825585521837 / 500000000000000 : ℝ) := by
  have h0 := leC_11
  have h1 := kleC_12
  have h2 := kleC_13
  have h3 := leC_14
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_3 : (-5546610327591 / 1000000000000000 : ℝ) ≤ Real.log 16 * (ex (1617 / 2000) 16 * cC 16) + kappa * (Real.log 17 * (ex (1617 / 2000) 17 * cC 17)) - kappa * (Real.log 18 * (ex (1617 / 2000) 18 * cC 18)) - Real.log 19 * (ex (1617 / 2000) 19 * cC 19) ∧ Real.log 16 * (ex (1617 / 2000) 16 * cC 16) + kappa * (Real.log 17 * (ex (1617 / 2000) 17 * cC 17)) - kappa * (Real.log 18 * (ex (1617 / 2000) 18 * cC 18)) - Real.log 19 * (ex (1617 / 2000) 19 * cC 19) ≤ (-5546574473771 / 1000000000000000 : ℝ) := by
  have h0 := leC_16
  have h1 := kleC_17
  have h2 := kleC_18
  have h3 := leC_19
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_4 : (-85791151963547 / 1000000000000000 : ℝ) ≤ Real.log 21 * (ex (1617 / 2000) 21 * cC 21) + kappa * (Real.log 22 * (ex (1617 / 2000) 22 * cC 22)) - kappa * (Real.log 23 * (ex (1617 / 2000) 23 * cC 23)) - Real.log 24 * (ex (1617 / 2000) 24 * cC 24) ∧ Real.log 21 * (ex (1617 / 2000) 21 * cC 21) + kappa * (Real.log 22 * (ex (1617 / 2000) 22 * cC 22)) - kappa * (Real.log 23 * (ex (1617 / 2000) 23 * cC 23)) - Real.log 24 * (ex (1617 / 2000) 24 * cC 24) ≤ (-21447778829533 / 250000000000000 : ℝ) := by
  have h0 := leC_21
  have h1 := kleC_22
  have h2 := kleC_23
  have h3 := leC_24
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_5 : (-146300551766181 / 500000000000000 : ℝ) ≤ Real.log 26 * (ex (1617 / 2000) 26 * cC 26) + kappa * (Real.log 27 * (ex (1617 / 2000) 27 * cC 27)) - kappa * (Real.log 28 * (ex (1617 / 2000) 28 * cC 28)) - Real.log 29 * (ex (1617 / 2000) 29 * cC 29) ∧ Real.log 26 * (ex (1617 / 2000) 26 * cC 26) + kappa * (Real.log 27 * (ex (1617 / 2000) 27 * cC 27)) - kappa * (Real.log 28 * (ex (1617 / 2000) 28 * cC 28)) - Real.log 29 * (ex (1617 / 2000) 29 * cC 29) ≤ (-292601069538121 / 1000000000000000 : ℝ) := by
  have h0 := leC_26
  have h1 := kleC_27
  have h2 := kleC_28
  have h3 := leC_29
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_6 : (-40877887948441 / 1000000000000000 : ℝ) ≤ Real.log 31 * (ex (1617 / 2000) 31 * cC 31) + kappa * (Real.log 32 * (ex (1617 / 2000) 32 * cC 32)) - kappa * (Real.log 33 * (ex (1617 / 2000) 33 * cC 33)) - Real.log 34 * (ex (1617 / 2000) 34 * cC 34) ∧ Real.log 31 * (ex (1617 / 2000) 31 * cC 31) + kappa * (Real.log 32 * (ex (1617 / 2000) 32 * cC 32)) - kappa * (Real.log 33 * (ex (1617 / 2000) 33 * cC 33)) - Real.log 34 * (ex (1617 / 2000) 34 * cC 34) ≤ (-40877856917367 / 1000000000000000 : ℝ) := by
  have h0 := leC_31
  have h1 := kleC_32
  have h2 := kleC_33
  have h3 := leC_34
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_7 : (-687229382287 / 200000000000000 : ℝ) ≤ Real.log 36 * (ex (1617 / 2000) 36 * cC 36) + kappa * (Real.log 37 * (ex (1617 / 2000) 37 * cC 37)) - kappa * (Real.log 38 * (ex (1617 / 2000) 38 * cC 38)) - Real.log 39 * (ex (1617 / 2000) 39 * cC 39) ∧ Real.log 36 * (ex (1617 / 2000) 36 * cC 36) + kappa * (Real.log 37 * (ex (1617 / 2000) 37 * cC 37)) - kappa * (Real.log 38 * (ex (1617 / 2000) 38 * cC 38)) - Real.log 39 * (ex (1617 / 2000) 39 * cC 39) ≤ (-68722358093 / 20000000000000 : ℝ) := by
  have h0 := leC_36
  have h1 := kleC_37
  have h2 := kleC_38
  have h3 := leC_39
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_8 : (23407715628683 / 250000000000000 : ℝ) ≤ Real.log 41 * (ex (1617 / 2000) 41 * cC 41) + kappa * (Real.log 42 * (ex (1617 / 2000) 42 * cC 42)) - kappa * (Real.log 43 * (ex (1617 / 2000) 43 * cC 43)) - Real.log 44 * (ex (1617 / 2000) 44 * cC 44) ∧ Real.log 41 * (ex (1617 / 2000) 41 * cC 41) + kappa * (Real.log 42 * (ex (1617 / 2000) 42 * cC 42)) - kappa * (Real.log 43 * (ex (1617 / 2000) 43 * cC 43)) - Real.log 44 * (ex (1617 / 2000) 44 * cC 44) ≤ (1872617791463 / 20000000000000 : ℝ) := by
  have h0 := leC_41
  have h1 := kleC_42
  have h2 := kleC_43
  have h3 := leC_44
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_9 : (-88642503728197 / 500000000000000 : ℝ) ≤ Real.log 46 * (ex (1617 / 2000) 46 * cC 46) + kappa * (Real.log 47 * (ex (1617 / 2000) 47 * cC 47)) - kappa * (Real.log 48 * (ex (1617 / 2000) 48 * cC 48)) - Real.log 49 * (ex (1617 / 2000) 49 * cC 49) ∧ Real.log 46 * (ex (1617 / 2000) 46 * cC 46) + kappa * (Real.log 47 * (ex (1617 / 2000) 47 * cC 47)) - kappa * (Real.log 48 * (ex (1617 / 2000) 48 * cC 48)) - Real.log 49 * (ex (1617 / 2000) 49 * cC 49) ≤ (-177284981920701 / 1000000000000000 : ℝ) := by
  have h0 := leC_46
  have h1 := kleC_47
  have h2 := kleC_48
  have h3 := leC_49
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_10 : (2889136691591 / 100000000000000 : ℝ) ≤ Real.log 51 * (ex (1617 / 2000) 51 * cC 51) + kappa * (Real.log 52 * (ex (1617 / 2000) 52 * cC 52)) - kappa * (Real.log 53 * (ex (1617 / 2000) 53 * cC 53)) - Real.log 54 * (ex (1617 / 2000) 54 * cC 54) ∧ Real.log 51 * (ex (1617 / 2000) 51 * cC 51) + kappa * (Real.log 52 * (ex (1617 / 2000) 52 * cC 52)) - kappa * (Real.log 53 * (ex (1617 / 2000) 53 * cC 53)) - Real.log 54 * (ex (1617 / 2000) 54 * cC 54) ≤ (3611423878901 / 125000000000000 : ℝ) := by
  have h0 := leC_51
  have h1 := kleC_52
  have h2 := kleC_53
  have h3 := leC_54
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_11 : (149710065507803 / 500000000000000 : ℝ) ≤ Real.log 56 * (ex (1617 / 2000) 56 * cC 56) + kappa * (Real.log 57 * (ex (1617 / 2000) 57 * cC 57)) - kappa * (Real.log 58 * (ex (1617 / 2000) 58 * cC 58)) - Real.log 59 * (ex (1617 / 2000) 59 * cC 59) ∧ Real.log 56 * (ex (1617 / 2000) 56 * cC 56) + kappa * (Real.log 57 * (ex (1617 / 2000) 57 * cC 57)) - kappa * (Real.log 58 * (ex (1617 / 2000) 58 * cC 58)) - Real.log 59 * (ex (1617 / 2000) 59 * cC 59) ≤ (299420156796843 / 1000000000000000 : ℝ) := by
  have h0 := leC_56
  have h1 := kleC_57
  have h2 := kleC_58
  have h3 := leC_59
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_12 : (11680860304841 / 62500000000000 : ℝ) ≤ Real.log 61 * (ex (1617 / 2000) 61 * cC 61) + kappa * (Real.log 62 * (ex (1617 / 2000) 62 * cC 62)) - kappa * (Real.log 63 * (ex (1617 / 2000) 63 * cC 63)) - Real.log 64 * (ex (1617 / 2000) 64 * cC 64) ∧ Real.log 61 * (ex (1617 / 2000) 61 * cC 61) + kappa * (Real.log 62 * (ex (1617 / 2000) 62 * cC 62)) - kappa * (Real.log 63 * (ex (1617 / 2000) 63 * cC 63)) - Real.log 64 * (ex (1617 / 2000) 64 * cC 64) ≤ (46723450327393 / 250000000000000 : ℝ) := by
  have h0 := leC_61
  have h1 := kleC_62
  have h2 := kleC_63
  have h3 := leC_64
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_13 : (50136416135633 / 500000000000000 : ℝ) ≤ Real.log 66 * (ex (1617 / 2000) 66 * cC 66) + kappa * (Real.log 67 * (ex (1617 / 2000) 67 * cC 67)) - kappa * (Real.log 68 * (ex (1617 / 2000) 68 * cC 68)) - Real.log 69 * (ex (1617 / 2000) 69 * cC 69) ∧ Real.log 66 * (ex (1617 / 2000) 66 * cC 66) + kappa * (Real.log 67 * (ex (1617 / 2000) 67 * cC 67)) - kappa * (Real.log 68 * (ex (1617 / 2000) 68 * cC 68)) - Real.log 69 * (ex (1617 / 2000) 69 * cC 69) ≤ (100272875621109 / 1000000000000000 : ℝ) := by
  have h0 := leC_66
  have h1 := kleC_67
  have h2 := kleC_68
  have h3 := leC_69
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_14 : (70968769124833 / 500000000000000 : ℝ) ≤ Real.log 71 * (ex (1617 / 2000) 71 * cC 71) + kappa * (Real.log 72 * (ex (1617 / 2000) 72 * cC 72)) - kappa * (Real.log 73 * (ex (1617 / 2000) 73 * cC 73)) - Real.log 74 * (ex (1617 / 2000) 74 * cC 74) ∧ Real.log 71 * (ex (1617 / 2000) 71 * cC 71) + kappa * (Real.log 72 * (ex (1617 / 2000) 72 * cC 72)) - kappa * (Real.log 73 * (ex (1617 / 2000) 73 * cC 73)) - Real.log 74 * (ex (1617 / 2000) 74 * cC 74) ≤ (4435549542737 / 31250000000000 : ℝ) := by
  have h0 := leC_71
  have h1 := kleC_72
  have h2 := kleC_73
  have h3 := leC_74
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_15 : (16019093627339 / 62500000000000 : ℝ) ≤ Real.log 76 * (ex (1617 / 2000) 76 * cC 76) + kappa * (Real.log 77 * (ex (1617 / 2000) 77 * cC 77)) - kappa * (Real.log 78 * (ex (1617 / 2000) 78 * cC 78)) - Real.log 79 * (ex (1617 / 2000) 79 * cC 79) ∧ Real.log 76 * (ex (1617 / 2000) 76 * cC 76) + kappa * (Real.log 77 * (ex (1617 / 2000) 77 * cC 77)) - kappa * (Real.log 78 * (ex (1617 / 2000) 78 * cC 78)) - Real.log 79 * (ex (1617 / 2000) 79 * cC 79) ≤ (128152773685783 / 500000000000000 : ℝ) := by
  have h0 := leC_76
  have h1 := kleC_77
  have h2 := kleC_78
  have h3 := leC_79
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_16 : (261757784188287 / 1000000000000000 : ℝ) ≤ Real.log 81 * (ex (1617 / 2000) 81 * cC 81) + kappa * (Real.log 82 * (ex (1617 / 2000) 82 * cC 82)) - kappa * (Real.log 83 * (ex (1617 / 2000) 83 * cC 83)) - Real.log 84 * (ex (1617 / 2000) 84 * cC 84) ∧ Real.log 81 * (ex (1617 / 2000) 81 * cC 81) + kappa * (Real.log 82 * (ex (1617 / 2000) 82 * cC 82)) - kappa * (Real.log 83 * (ex (1617 / 2000) 83 * cC 83)) - Real.log 84 * (ex (1617 / 2000) 84 * cC 84) ≤ (261757834388133 / 1000000000000000 : ℝ) := by
  have h0 := leC_81
  have h1 := kleC_82
  have h2 := kleC_83
  have h3 := leC_84
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_17 : (-18349946356541 / 1000000000000000 : ℝ) ≤ Real.log 86 * (ex (1617 / 2000) 86 * cC 86) + kappa * (Real.log 87 * (ex (1617 / 2000) 87 * cC 87)) - kappa * (Real.log 88 * (ex (1617 / 2000) 88 * cC 88)) - Real.log 89 * (ex (1617 / 2000) 89 * cC 89) ∧ Real.log 86 * (ex (1617 / 2000) 86 * cC 86) + kappa * (Real.log 87 * (ex (1617 / 2000) 87 * cC 87)) - kappa * (Real.log 88 * (ex (1617 / 2000) 88 * cC 88)) - Real.log 89 * (ex (1617 / 2000) 89 * cC 89) ≤ (-3669979233167 / 200000000000000 : ℝ) := by
  have h0 := leC_86
  have h1 := kleC_87
  have h2 := kleC_88
  have h3 := leC_89
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_18 : (-258693200832499 / 1000000000000000 : ℝ) ≤ Real.log 91 * (ex (1617 / 2000) 91 * cC 91) + kappa * (Real.log 92 * (ex (1617 / 2000) 92 * cC 92)) - kappa * (Real.log 93 * (ex (1617 / 2000) 93 * cC 93)) - Real.log 94 * (ex (1617 / 2000) 94 * cC 94) ∧ Real.log 91 * (ex (1617 / 2000) 91 * cC 91) + kappa * (Real.log 92 * (ex (1617 / 2000) 92 * cC 92)) - kappa * (Real.log 93 * (ex (1617 / 2000) 93 * cC 93)) - Real.log 94 * (ex (1617 / 2000) 94 * cC 94) ≤ (-4042080477459 / 15625000000000 : ℝ) := by
  have h0 := leC_91
  have h1 := kleC_92
  have h2 := kleC_93
  have h3 := leC_94
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem AReB_19 : (52551519990303 / 1000000000000000 : ℝ) ≤ Real.log 96 * (ex (1617 / 2000) 96 * cC 96) + kappa * (Real.log 97 * (ex (1617 / 2000) 97 * cC 97)) - kappa * (Real.log 98 * (ex (1617 / 2000) 98 * cC 98)) - Real.log 99 * (ex (1617 / 2000) 99 * cC 99) ∧ Real.log 96 * (ex (1617 / 2000) 96 * cC 96) + kappa * (Real.log 97 * (ex (1617 / 2000) 97 * cC 97)) - kappa * (Real.log 98 * (ex (1617 / 2000) 98 * cC 98)) - Real.log 99 * (ex (1617 / 2000) 99 * cC 99) ≤ (52551569450807 / 1000000000000000 : ℝ) := by
  have h0 := leC_96
  have h1 := kleC_97
  have h2 := kleC_98
  have h3 := leC_99
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

theorem PReT_1 : (4896734990689 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 101 * (cC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (1617 / 2000) 101 * (cC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (9793473427661 / 1000000000000000 : ℝ) := by
  have hc := cCB_101
  have hs := sCB_101
  have hin : (408724270849719 / 1000000000000000 : ℝ) ≤ cC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (204362207007561 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (4896734990689 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 101 * (cC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (1617 / 2000) 101 * (cC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (9793473427661 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_101 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem PReT_2 : (2041079417681 / 500000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 102 * (cC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (1617 / 2000) 102 * (cC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (408215979481 / 100000000000000 : ℝ) := by
  have hc := cCB_102
  have hs := sCB_102
  have hin : (302255314123493 / 500000000000000 : ℝ) ≤ cC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (604510769344153 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (14369799264939 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 102 * (cC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (1617 / 2000) 102 * (cC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (2873960528467 / 200000000000000 : ℝ) :=
    mul_bounds_of exB_102 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaB he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PReT_3 : (2564195718989 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 103 * (cC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (1617 / 2000) 103 * (cC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (102567866221 / 40000000000000 : ℝ) := by
  have hc := cCB_103
  have hs := sCB_103
  have hin : (47841069844391 / 125000000000000 : ℝ) ≤ cC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (382728697916601 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (1805269184467 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 103 * (cC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (1617 / 2000) 103 * (cC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (361053968763 / 40000000000000 : ℝ) :=
    mul_bounds_of exB_103 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaB he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PReT_4 : (-1026241223521 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 104 * (cC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (1617 / 2000) 104 * (cC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-513119808531 / 250000000000000 : ℝ) := by
  have hc := cCB_104
  have hs := sCB_104
  have hin : (-87710362590963 / 1000000000000000 : ℝ) ≤ cC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-43855112717159 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-1026241223521 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 104 * (cC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (1617 / 2000) 104 * (cC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) + sC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-513119808531 / 250000000000000 : ℝ) :=
    mul_bounds_of exB_104 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem PImT_1 : (10947970136363 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 101 * (cC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (1617 / 2000) 101 * (cC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (10947973584519 / 1000000000000000 : ℝ) := by
  have hc := cCB_101
  have hs := sCB_101
  have hin : (57113325508961 / 125000000000000 : ℝ) ≤ cC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (45690674723709 / 100000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (10947970136363 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 101 * (cC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (1617 / 2000) 101 * (cC 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (10947973584519 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_101 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem PImT_2 : (-85831687751 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 102 * (cC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (1617 / 2000) 102 * (cC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-42915367403 / 500000000000000 : ℝ) := by
  have hc := cCB_102
  have hs := sCB_102
  have hin : (-12710472447 / 1000000000000 : ℝ) ≤ cC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-12710331350009 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-75535039993 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 102 * (cC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (1617 / 2000) 102 * (cC 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-75534201367 / 250000000000000 : ℝ) :=
    mul_bounds_of exB_102 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaB he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PImT_3 : (-3068416886827 / 1000000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 103 * (cC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ kappa * (ex (1617 / 2000) 103 * (cC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-767103987367 / 250000000000000 : ℝ) := by
  have hc := cCB_103
  have hs := sCB_103
  have hin : (-228993980869249 / 500000000000000 : ℝ) ≤ cC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-3578029863883 / 7812500000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-10801278564391 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 103 * (cC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (1617 / 2000) 103 * (cC 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-2160255052951 / 200000000000000 : ℝ) :=
    mul_bounds_of exB_103 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaB he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem PImT_4 : (-6822009584963 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 104 * (cC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (1617 / 2000) 104 * (cC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-13644015938011 / 1000000000000000 : ℝ) := by
  have hc := cCB_104
  have hs := sCB_104
  have hin : (-583060707932987 / 1000000000000000 : ℝ) ≤ cC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ cC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-291530285387473 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]
  have he : (-6822009584963 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 104 * (cC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ ex (1617 / 2000) 104 * (cC 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - sC 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-13644015938011 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_104 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem AReT_1 : (-44809603265461 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 101 * (cC 101 * ((4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 101 * ((-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (1617 / 2000) 101 * (cC 101 * ((4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 101 * ((-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-5601198423743 / 125000000000000 : ℝ) := by
  have hc := cCB_101
  have hs := sCB_101
  have hl := lgB_101
  have hv1 : (-1224411848392053 / 500000000000000 : ℝ) ≤ (4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-97952947828659 / 40000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-173836544712151 / 125000000000000 : ℝ) ≤ (-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1390692357095911 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (-579553275499581 / 250000000000000 : ℝ) ≤ cC 101 * ((4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cC 101 * ((4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-2318212681116653 / 1000000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (224056337598983 / 500000000000000 : ℝ) ≤ sC 101 * ((-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sC 101 * ((-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (56014114229671 / 125000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (-935050213400179 / 500000000000000 : ℝ) ≤ cC 101 * ((4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 101 * ((-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cC 101 * ((4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 101 * ((-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-374019953455857 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (-44809603265461 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 101 * (cC 101 * ((4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 101 * ((-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (1617 / 2000) 101 * (cC 101 * ((4062534435001535897631391326612736708413799470767175451491986571945897549454229338059873756702041719321122904222524872783593324766810958458884054296061946434603 / 248558471897261495483292049009435315353169293659926189786974206335064051706492101434760232960000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (1190979929041446726999457807134989214471695938821919712525122123393529666400641050533437654647067794172432490735455400515144752890792321729324555344242957 / 2229671865562985876113529655163210866911607345983263788888532707721441508264509440000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 101 * ((-1064630512486098047888168366920574934903847366924349598008270039926369535731293511372741440556389376865652085649994020977963104834581438646013109503430523988729 / 463975814208221458235478491484279255325916014831862220935685185158786229852118589344885768192000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 101 * (3353835990324371144726438027332712899319995400723845311266438266912677859536935433992851321962228199688966769098239368394800644930488755468604294323757811 / 11148359327814929380567648275816054334558036729916318944442663538607207541322547200000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-5601198423743 / 125000000000000 : ℝ) :=
    mul_bounds_of exB_101 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

theorem AReT_2 : (-939688983387 / 50000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 102 * (cC 102 * ((4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 102 * ((-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ∧ kappa * (ex (1617 / 2000) 102 * (cC 102 * ((4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 102 * ((-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ≤ (-9396887619137 / 500000000000000 : ℝ) := by
  have hc := cCB_102
  have hs := sCB_102
  have hl := lgB_102
  have hv1 : (-1222318647215903 / 500000000000000 : ℝ) ≤ (4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1222318646682693 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-665541903261583 / 500000000000000 : ℝ) ≤ (-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1331083805947157 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (-531508368599271 / 250000000000000 : ℝ) ≤ cC 102 * ((4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cC 102 * ((4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-2126033052487741 / 1000000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (-657062429950937 / 1000000000000000 : ℝ) ≤ sC 102 * ((-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sC 102 * ((-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-657062200446559 / 1000000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (-2783095904348021 / 1000000000000000 : ℝ) ≤ cC 102 * ((4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 102 * ((-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cC 102 * ((4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 102 * ((-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-27830952529343 / 10000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (-66156867517117 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 102 * (cC 102 * ((4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 102 * ((-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (1617 / 2000) 102 * (cC 102 * ((4941689565801366052991808983873389372287911332829936783595373321388329926356303061783882277836481711118720366898723279268645671514210290227931446681309126434603 / 311774738616036882473542271097453022012520645286863899951673284362507261294742118787113287680000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (87521824476252905384790759558776093854434110660856494171179368332450564125407138331543669202089432190196666264730930497241131346580176154593739250837821 / 164514577330938129616539746403249368612832104810976936616319332112204881786306560000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 102 * ((-1219659500633426508063042930171230862734953982065129831112089265997692675080233106693082972201153799186794638521276921032467747245640946349247867387708923988729 / 581979512083268847283945572715245641090038537868812613243123464143346887750185288402611470336000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 102 * (236366703060234863719383057863146618666060383785704374484884927948017375744657609556231819515512121073660152942515625086977973555158771196906779670809283 / 822572886654690648082698732016246843064160524054884683081596660561024408931532800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-16539212981187 / 250000000000000 : ℝ) :=
    mul_bounds_of exB_102 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaB he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem AReT_3 : (-2968640325263 / 250000000000000 : ℝ) ≤ kappa * (ex (1617 / 2000) 103 * (cC 103 * ((58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 103 * ((-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ∧ kappa * (ex (1617 / 2000) 103 * (cC 103 * ((58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 103 * ((-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)))) ≤ (-11874556970943 / 1000000000000000 : ℝ) := by
  have hc := cCB_103
  have hs := sCB_103
  have hl := lgB_103
  have hv1 : (-122061178827269 / 50000000000000 : ℝ) ≤ (58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-2441223575479951 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-25472304808087 / 20000000000000 : ℝ) ≤ (-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1273615239852817 / 1000000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (-4232255127057 / 8000000000000 : ℝ) ≤ cC 103 * ((58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cC 103 * ((58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-529031468333931 / 1000000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (-1243349870591281 / 1000000000000000 : ℝ) ≤ sC 103 * ((-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sC 103 * ((-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-621674824862457 / 500000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (-886190880736703 / 500000000000000 : ℝ) ≤ cC 103 * ((58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 103 * ((-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cC 103 * ((58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 103 * ((-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-354476223611769 / 200000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (-20900100796809 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 103 * (cC 103 * ((58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 103 * ((-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (1617 / 2000) 103 * (cC 103 * ((58303743459644229511923791396491964414270150893817410250254574065788964476237573824540195449669166453443933892403135429868848017013247939539233715184916761501 / 3788400775018424093219546494048327574451260174699676577504583077730172442253715191774576640000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (18012782937291409480695304145138750985231783649877274925924873825452997442471993536989268164234822562786214916734279136816266251804116795619184159847019 / 33983515263269749755509178947574203157534030780077193627236647227637390859304960000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 103 * ((-714132179625915652877586514468613301940492448299689784172039572806559058895957842262833864166220218114728761818847995952488523016508589026215368556531897797 / 372193760352687279333850181871414638893457139970494540947818688338402906607382545156800512000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 103 * (46622702772654304966126202405642008886514484613192779654207030958817270771428506540342355341421754782208326879206100685193772686036757807548119157318037 / 169917576316348748777545894737871015787670153900385968136183236138186954296524800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (-41800186351 / 1000000000000 : ℝ) :=
    mul_bounds_of exB_103 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact mul_bounds_of kappaB he (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem AReT_4 : (4649146408363 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 104 * (cC 104 * ((94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 104 * ((-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (1617 / 2000) 104 * (cC 104 * ((94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 104 * ((-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (9298307709159 / 1000000000000000 : ℝ) := by
  have hc := cCB_104
  have hs := sCB_104
  have hl := lgB_104
  have hv1 : (-1219245500974451 / 500000000000000 : ℝ) ≤ (94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-1219245500442139 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hv2 : (-609068438894627 / 500000000000000 : ℝ) ≤ (-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ∧ (-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (-152267109657679 / 125000000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hp1 : (1396089064687699 / 1000000000000000 : ℝ) ≤ cC 104 * ((94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cC 104 * ((94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (349022372141609 / 250000000000000 : ℝ) :=
    mul_bounds_of hc hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp2 : (-99873773194343 / 100000000000000 : ℝ) ≤ sC 104 * ((-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ sC 104 * ((-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (-499368760031059 / 500000000000000 : ℝ) :=
    mul_bounds_of hs hv2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hin : (397351332744269 / 1000000000000000 : ℝ) ≤ cC 104 * ((94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 104 * ((-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ∧ cC 104 * ((94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 104 * ((-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ≤ (198675984252159 / 500000000000000 : ℝ) := by
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2]
  have he : (4649146408363 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 104 * (cC 104 * ((94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 104 * ((-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ∧ ex (1617 / 2000) 104 * (cC 104 * ((94684592548188104738560433227215102180904138616576374054858832429611327250231786861744254088731142313241412752826795792200531575666175164451225688367192810839 / 6328678763930295249955812992792279180677433046090777731781789726184379527419401060713758720000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (2309218327566718778641256678297635129407951541622408380589239386384798384393088686445184825971500019944085939950566666213096323458106877448811758944242957 / 4371355840892229394578183793671620964183559340826260947296513830694144809537372160000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) + sC 104 * ((-1601663719740837563823295303084705554971846812202509248314348280101585508728605032921168927142536995260527183323546349229976259686602082762312530055702523988729 / 909642094335581103926982187497343594236036376491447785981435909976901484074415245793257586688000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) - Real.log 104 * (5724338185339266402939689475597035034726939950262251262523501481187284067122435982452135536517941295605359502424959301705678171134843979141767350723757811 / 21856779204461146972890918968358104820917796704131304736482569153470724047686860800000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))) ≤ (9298307709159 / 1000000000000000 : ℝ) :=
    mul_bounds_of exB_104 hin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact he

/-- Lower end of the enclosure of `Re fEM(c)`. -/
theorem PRe_20_ge : (-32374434339 / 1000000000000000 : ℝ) ≤ PRe 20 12 := by
  rw [PRe_20]
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
  have t1 := PReT_1
  have t2 := PReT_2
  have t3 := PReT_3
  have t4 := PReT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- Upper end of the enclosure of `Re fEM(c)`. -/
theorem PRe_20_le : PRe 20 12 ≤ (-2009868643 / 62500000000000 : ℝ) := by
  rw [PRe_20]
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
  have t1 := PReT_1
  have t2 := PReT_2
  have t3 := PReT_3
  have t4 := PReT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- **The enclosure of `Re fEM(c)`**: `PRe 20 12 ∈ [-3.2374434339e-05, -3.2157898288e-05]` (width `2.17e-07`). -/
theorem PRe_20_mem : (-32374434339 / 1000000000000000 : ℝ) ≤ PRe 20 12 ∧ PRe 20 12 ≤ (-2009868643 / 62500000000000 : ℝ) := ⟨PRe_20_ge, PRe_20_le⟩

/-- Open inequality `H1` of `DHLocateSkeleton`. -/
theorem H1 : |PRe 20 12| ≤ 1 / 1000 := by
  have h := PRe_20_mem
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Lower end of the enclosure of `Im fEM(c)`. -/
theorem PIm_20_ge : (-5446810737 / 100000000000000 : ℝ) ≤ PIm 20 12 := by
  rw [PIm_20]
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
  have t1 := PImT_1
  have t2 := PImT_2
  have t3 := PImT_3
  have t4 := PImT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- Upper end of the enclosure of `Im fEM(c)`. -/
theorem PIm_20_le : PIm 20 12 ≤ (-6781461501 / 125000000000000 : ℝ) := by
  rw [PIm_20]
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
  have t1 := PImT_1
  have t2 := PImT_2
  have t3 := PImT_3
  have t4 := PImT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- **The enclosure of `Im fEM(c)`**: `PIm 20 12 ∈ [-5.4468107370e-05, -5.4251692008e-05]` (width `2.16e-07`). -/
theorem PIm_20_mem : (-5446810737 / 100000000000000 : ℝ) ≤ PIm 20 12 ∧ PIm 20 12 ≤ (-6781461501 / 125000000000000 : ℝ) := ⟨PIm_20_ge, PIm_20_le⟩

/-- Open inequality `H2` of `DHLocateSkeleton`. -/
theorem H2 : |PIm 20 12| ≤ 1 / 1000 := by
  have h := PIm_20_mem
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Lower end of the enclosure of `Re fEM′(c)`. -/
theorem ARe_20_ge : (1232332996475629 / 1000000000000000 : ℝ) ≤ ARe 20 12 := by
  rw [ARe_20]
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
  have t1 := AReT_1
  have t2 := AReT_2
  have t3 := AReT_3
  have t4 := AReT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- Upper end of the enclosure of `Re fEM′(c)`. -/
theorem ARe_20_le : ARe 20 12 ≤ (246466753163743 / 200000000000000 : ℝ) := by
  rw [ARe_20]
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
  have t1 := AReT_1
  have t2 := AReT_2
  have t3 := AReT_3
  have t4 := AReT_4
  linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- **The enclosure of `Re fEM′(c)`**: `ARe 20 12 ∈ [1.2323329965e+00, 1.2323337658e+00]` (width `7.69e-07`). -/
theorem ARe_20_mem : (1232332996475629 / 1000000000000000 : ℝ) ≤ ARe 20 12 ∧ ARe 20 12 ≤ (246466753163743 / 200000000000000 : ℝ) := ⟨ARe_20_ge, ARe_20_le⟩

/-- Open inequality `H3` of `DHLocateSkeleton`. -/
theorem H3 : 1 ≤ ARe 20 12 := by
  have h := ARe_20_mem
  linarith [h.1]

/-- **A kernel-checked zero of the Davenport–Heilbronn function off the critical line**: within `1/100` of
`c = cLoc = 1617/2000 + (856993/10000) i` (`dh_zero_near_of_center'` with its three open inequalities
discharged). -/
theorem dh_zero_located : ∃ ρ, dh ρ = 0 ∧ ‖ρ - cLoc‖ < 1 / 100 :=
  dh_zero_near_of_center' H1 H2 H3

/-- The located zero in coordinates: `0.7985 < Re ρ < 0.8185` (so `Re ρ > 1/2`: off the critical line)
and `85.6893 < Im ρ < 85.7093`. -/
theorem dh_zero_located_box : ∃ ρ : ℂ, dh ρ = 0 ∧ 1597 / 2000 < ρ.re ∧ ρ.re < 1637 / 2000 ∧
    856893 / 10000 < ρ.im ∧ ρ.im < 857093 / 10000 := by
  obtain ⟨ρ, h0, hρ⟩ := dh_zero_located
  have hre := abs_lt.1 ((Complex.abs_re_le_norm (ρ - cLoc)).trans_lt hρ)
  have him := abs_lt.1 ((Complex.abs_im_le_norm (ρ - cLoc)).trans_lt hρ)
  rw [Complex.sub_re, cLoc_re] at hre
  rw [Complex.sub_im, cLoc_im] at him
  exact ⟨ρ, h0, by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩

end PsiOmega.Locate

#print axioms PsiOmega.Locate.PRe_20_mem
#print axioms PsiOmega.Locate.PIm_20_mem
#print axioms PsiOmega.Locate.ARe_20_mem
#print axioms PsiOmega.Locate.H1
#print axioms PsiOmega.Locate.H2
#print axioms PsiOmega.Locate.H3
#print axioms PsiOmega.Locate.dh_zero_located
#print axioms PsiOmega.Locate.dh_zero_located_box
