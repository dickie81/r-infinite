import Mathlib
import DHPacket
import DHNumerics
import DHLogBounds
import DHTrigBounds
import DHCoeffs

/-! # Generated: lower bounds for the prime terms and their partial sums (round 261, certificate stage 3) -/

open Real Finset

namespace PsiOmega

/-- The prime term of `QDHu_packet_eq` at `(a, ω) = (12/5, 169/2)`. -/
noncomputable def primeTerm (n : ℕ) : ℝ := fDH n / Real.sqrt n * ((2 * (12 / 5) - Real.log n) / 2 * Real.cos (169 / 2 * Real.log n)
    + Real.sin (169 / 2 * (2 * (12 / 5) - Real.log n)) / (2 * (169 / 2)))

theorem sqrt_bounds_2 : (1414213562373 / 1000000000000 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (707106781187 / 500000000000 : ℝ) := by
  constructor
  · calc (1414213562373 / 1000000000000 : ℝ) = Real.sqrt ((1414213562373 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 2 ≤ Real.sqrt ((707106781187 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (707106781187 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_2 : (-1239253117129 / 10000000000000 : ℝ) ≤ primeTerm 2 ∧ primeTerm 2 ≤ (-1239195721227 / 10000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_2
  have hl := PsiOmega.Num.log_bound_2
  have hc := PsiOmega.Num.theta_2_cos
  have hs := PsiOmega.Num.theta_2_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_2
  have hqpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 2)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 2) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 2) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 2) = 2028 / 5 - 169 / 2 * Real.log 2 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (3403389999917129 / 1657420000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 2) / 2 ∧ (2 * (12 / 5) - Real.log 2) / 2 ≤ (3403390000082871 / 1657420000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-563999707062178169283122370565692523983779271681594876147565615837844708569112215058081223730995215933439724050770310288018342786382316883311 / 633677839033061810596336727030575275421142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 2) / 2 * Real.cos (169 / 2 * Real.log 2) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 2) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 2)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 2) / 2 * Real.cos (169 / 2 * Real.log 2) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 2) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 2)) / (2 * (169 / 2)) ≤ (-3776608832325176223122109938481244578833656999622566546143603319064693801697721463652137313669045229049968996247141636319040622541118188779731999922489535589800539 / 4243378386382110338814754868508316576480865478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_3 : (108253175473 / 62500000000 : ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ (1732050807569 / 1000000000000 : ℝ) := by
  constructor
  · calc (108253175473 / 62500000000 : ℝ) = Real.sqrt ((108253175473 / 62500000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 3 ≤ Real.sqrt ((1732050807569 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1732050807569 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_3 : (-2534378037657 / 50000000000000 : ℝ) ≤ primeTerm 3 ∧ primeTerm 3 ≤ (-5067727941537 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_3
  have hl := PsiOmega.Num.log_bound_3
  have hc := PsiOmega.Num.theta_3_cos
  have hs := PsiOmega.Num.theta_3_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_3
  have hqpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 3)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 3) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 3) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 3) = 2028 / 5 - 169 / 2 * Real.log 3 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (3454249935525880546453 / 1866462097500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 3) / 2 ∧ (2 * (12 / 5) - Real.log 3) / 2 ≤ (3454249935776235329131 / 1866462097500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (43705222980397687508917746259670319808618551268108171868371045599814249757919527822015144148488592270675448982849859820136564528550235661646287951 / 155397157704422986040579401922911984001984819769859313964843750000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 3) / 2 * Real.cos (169 / 2 * Real.log 3) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 3) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 3)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 3) / 2 * Real.cos (169 / 2 * Real.log 3) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 3) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 3)) / (2 * (169 / 2)) ≤ (237380754449614325316948179268921092819714419369022158367428840009158525348312522532219874586216665327246897219971877630410361 / 843853656382806033287025115896540228277444839477539062500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_4 : (2 : ℝ) ≤ Real.sqrt 4 ∧ Real.sqrt 4 ≤ (2000000000001 / 1000000000000 : ℝ) := by
  constructor
  · calc (2 : ℝ) = Real.sqrt ((2 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 4 ≤ Real.sqrt ((2000000000001 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2000000000001 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_4 : (76452575448339 / 100000000000000 : ℝ) ≤ primeTerm 4 ∧ primeTerm 4 ≤ (76457349850401 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_4
  have hl := PsiOmega.Num.log_bound_4
  have hc := PsiOmega.Num.theta_4_cos
  have hs := PsiOmega.Num.theta_4_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_4
  have hqpos : (0 : ℝ) < Real.sqrt 4 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 4)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 4) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 4) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 4) = 2028 / 5 - 169 / 2 * Real.log 4 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (299967631740261484194939080599 / 175743115246791592500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 4) / 2 ∧ (2 * (12 / 5) - Real.log 4) / 2 ≤ (99989210588562047653208464291 / 58581038415597197500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-5526046587048401435025771431566933102877812754687585021701799887788887787567839753475769043778974193575325636740783373989444787263749804590470726771645135741713220536987 / 5211952181434193316372117865465771992187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 4) / 2 * Real.cos (169 / 2 * Real.log 4) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 4) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 4)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 4) / 2 * Real.cos (169 / 2 * Real.log 4) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 4) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 4)) / (2 * (169 / 2)) ≤ (-138142537814776223749914544001011354285378639627719380452641601063987344444169422627951331113117789418981491358050609908371928509206352953985848241974026237888563365400767169614473 / 130298804535854832909302946636644299804687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_5 : (2236067977499 / 1000000000000 : ℝ) ≤ Real.sqrt 5 ∧ Real.sqrt 5 ≤ (894427191 / 400000000 : ℝ) := by
  constructor
  · calc (2236067977499 / 1000000000000 : ℝ) = Real.sqrt ((2236067977499 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 5 ≤ Real.sqrt ((894427191 / 400000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (894427191 / 400000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_5 : (0 : ℝ) ≤ primeTerm 5 ∧ primeTerm 5 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_5
  have hl := PsiOmega.Num.log_bound_5
  have hc := PsiOmega.Num.theta_5_cos
  have hs := PsiOmega.Num.theta_5_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_5
  have hqpos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 5)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 5) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 5) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 5) = 2028 / 5 - 169 / 2 * Real.log 5 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (325851230076628153177917639573874978733 / 204259450941886063342316197500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 5) / 2 ∧ (2 * (12 / 5) - Real.log 5) / 2 ≤ (325851230112768621193491045391024324691 / 204259450941886063342316197500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-62616864273196028652073810651645799754329090188148870535500451266492165947687368294345296362891439604163424295876578228484315808976899223259943477604820211971856877071893079996185049 / 63662602690247740797550495564832199472032568467497262954711914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 5) / 2 * Real.cos (169 / 2 * Real.log 5) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 5) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 5)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 5) / 2 * Real.cos (169 / 2 * Real.log 5) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 5) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 5)) / (2 * (169 / 2)) ≤ (-782654054866105813126625480844063912856356965468304392284269336342516662981936308907390995459288626077606697955675843663377613113956365607877800617665552871477869240969843001882453721945665843 / 795782533628096759969381194560402493400407105843715786933898925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_6 : (2449489742783 / 1000000000000 : ℝ) ≤ Real.sqrt 6 ∧ Real.sqrt 6 ≤ (38273277231 / 15625000000 : ℝ) := by
  constructor
  · calc (2449489742783 / 1000000000000 : ℝ) = Real.sqrt ((2449489742783 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 6 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 6 ≤ Real.sqrt ((38273277231 / 15625000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (38273277231 / 15625000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_6 : (97769466110363 / 100000000000000 : ℝ) ≤ primeTerm 6 ∧ primeTerm 6 ≤ (97775327458061 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_6
  have hl := PsiOmega.Num.log_bound_6
  have hc := PsiOmega.Num.theta_6_cos
  have hs := PsiOmega.Num.theta_6_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_6
  have hqpos : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 6)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 6) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 6) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 6) = 2028 / 5 - 169 / 2 * Real.log 6 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (65857646109488083115374834480040853837604677773 / 43784827337577092567554020044274997500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 6) / 2 ∧ (2 * (12 / 5) - Real.log 6) / 2 ≤ (65857646117389855406298747948108057184543430771 / 43784827337577092567554020044274997500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (1852383736509818349843345093431531039071332148538079508233297900171855257858179065084244978138869351251528507768982645940171840091131095780384906276770121789533641652404822600196874047242471685674683650476727 / 1497743050766748678457008271835282666371531622759254402492324534082036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 6) / 2 * Real.cos (169 / 2 * Real.log 6) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 6) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 6)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 6) / 2 * Real.cos (169 / 2 * Real.log 6) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 6) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 6)) / (2 * (169 / 2)) ≤ (38531891586755930387168570246118980444165095311680830857399102094906845641276103315552021111715600627945776962765600311015205643870258132296017950536928697437188663027815832865114348230017442567772151907228143 / 31153055455948372511905772054173879460527857753392491571840350308906351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_7 : (330718913883 / 125000000000 : ℝ) ≤ Real.sqrt 7 ∧ Real.sqrt 7 ≤ (529150262213 / 200000000000 : ℝ) := by
  constructor
  · calc (330718913883 / 125000000000 : ℝ) = Real.sqrt ((330718913883 / 125000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 7 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 7 ≤ Real.sqrt ((529150262213 / 200000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (529150262213 / 200000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_7 : (1810770109353 / 12500000000000 : ℝ) ≤ primeTerm 7 ∧ primeTerm 7 ≤ (14487778266079 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_7
  have hl := PsiOmega.Num.log_bound_7
  have hc := PsiOmega.Num.theta_7_cos
  have hs := PsiOmega.Num.theta_7_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_7
  have hqpos : (0 : ℝ) < Real.sqrt 7 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 7)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 7) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 7) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 7) = 2028 / 5 - 169 / 2 * Real.log 7 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (50969233840993898947745510692877902121381109525241964333 / 35716628772942272113214581977164895632948197500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 7) / 2 ∧ (2 * (12 / 5) - Real.log 7) / 2 ≤ (50969233847459665353663887358776317631306091338641415891 / 35716628772942272113214581977164895632948197500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (998216262191567166983833018910779783826929774377658929451871450985885790375234019044784067425585209332627697382926684678264330163596117611112709538249535208540234924339162020406894423019164921484678605425396024049983564730817043001702909 / 1439740751937062409671438360323101913519171198295238965216860355496873011026941918479204177856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 7) / 2 * Real.cos (169 / 2 * Real.log 7) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 7) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 7)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 7) / 2 * Real.cos (169 / 2 * Real.log 7) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 7) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 7)) / (2 * (169 / 2)) ≤ (7986621709088586134596366050883870481568646543359352994381524786502358969297957995689627581407424874270225541701918574732203868543001542488078897252925140048471048023537998155570772775007743004849645045103848721378644730338001 / 11517926015496499277371506882584815308153369586361911721734882843974984088215535347833633422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_8 : (1414213562373 / 500000000000 : ℝ) ≤ Real.sqrt 8 ∧ Real.sqrt 8 ≤ (2828427124747 / 1000000000000 : ℝ) := by
  constructor
  · calc (1414213562373 / 500000000000 : ℝ) = Real.sqrt ((1414213562373 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 8 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 8 ≤ Real.sqrt ((2828427124747 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2828427124747 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_8 : (744651828951 / 100000000000000 : ℝ) ≤ primeTerm 8 ∧ primeTerm 8 ≤ (744695846327 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_8
  have hl := PsiOmega.Num.log_bound_8
  have hc := PsiOmega.Num.theta_8_cos
  have hs := PsiOmega.Num.theta_8_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_8
  have hqpos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 8)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 8) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 8) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 8) = 2028 / 5 - 169 / 2 * Real.log 8 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (48584588250212248680565346398053225144921526113838964333 / 35716628772942272113214581977164895632948197500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 8) / 2 ∧ (2 * (12 / 5) - Real.log 8) / 2 ≤ (48584588257611234206555374304743712820949189895569415891 / 35716628772942272113214581977164895632948197500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (7633074359990132421559387856521320004745901725809470288915726225646194022370540786455096220335708845835260740222561008365913203283431997884339923103537436287455502051798714762004671218372195162773703835893631669858805247 / 5758963007748249638685753441292407654076684793180955860867441421987492044107767673916816711425781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 8) / 2 * Real.cos (169 / 2 * Real.log 8) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 8) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 8)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 8) / 2 * Real.cos (169 / 2 * Real.log 8) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 8) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 8)) / (2 * (169 / 2)) ≤ (3053410174315094758120936903559628422923059335286761177174301586420295061697361649772802645042921499416593237740633923400336543477380367966779707595419768505533774474152449091558518106847199946906841 / 2303585203099299855474301376516963061630673917272382344346976568794996817643107069566726684570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_9 : (3 : ℝ) ≤ Real.sqrt 9 ∧ Real.sqrt 9 ≤ (3000000000001 / 1000000000000 : ℝ) := by
  constructor
  · calc (3 : ℝ) = Real.sqrt ((3 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 9 ≤ Real.sqrt ((3000000000001 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (3000000000001 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_9 : (94374597588383 / 100000000000000 : ℝ) ≤ primeTerm 9 ∧ primeTerm 9 ≤ (47190308876603 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_9
  have hl := PsiOmega.Num.log_bound_9
  have hc := PsiOmega.Num.theta_9_cos
  have hs := PsiOmega.Num.theta_9_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_9
  have hqpos : (0 : ℝ) < Real.sqrt 9 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 9)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 9) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 9) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 9) = 2028 / 5 - 169 / 2 * Real.log 9 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (19073026446891090341426616667111034353373988968101222763222550109 / 14655914054722750244541377332759559576207458439891917500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 9) / 2 ∧ (2 * (12 / 5) - Real.log 9) / 2 ≤ (19073026450051196315835843507746260853276523656534394696098052643 / 14655914054722750244541377332759559576207458439891917500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-2402199907280075571362319529744965512977660765514760540994978783298882796499927539683359759121931468078725894329881474245674140446312629941963014720652494444876972423624009824966171258905503707095728643058614464329513326232031269326501793461723452747 / 1939363348961281372156395415243118090446224050200554166000835668987687973784092213002369431231157488641738891601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 9) / 2 * Real.cos (169 / 2 * Real.log 9) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 9) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 9)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 9) / 2 * Real.cos (169 / 2 * Real.log 9) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 9) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 9)) / (2 * (169 / 2)) ≤ (-300255835120475332274415370556758987867600845648044051114104127729025270600014617371772073013480114364224131782557729155513761744370238127867157880765702496796336162870093818575330970763713490049338779617912242966222893619867671479437085585893279327 / 242420418620160171519549426905389761305778006275069270750104458623460996723011526625296178903894686080217361450195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_10 : (395284707521 / 125000000000 : ℝ) ≤ Real.sqrt 10 ∧ Real.sqrt 10 ≤ (3162277660169 / 1000000000000 : ℝ) := by
  constructor
  · calc (395284707521 / 125000000000 : ℝ) = Real.sqrt ((395284707521 / 125000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 10 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 10 ≤ Real.sqrt ((3162277660169 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (3162277660169 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_10 : (0 : ℝ) ≤ primeTerm 10 ∧ primeTerm 10 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_10
  have hl := PsiOmega.Num.log_bound_10
  have hc := PsiOmega.Num.theta_10_cos
  have hs := PsiOmega.Num.theta_10_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_10
  have hqpos : (0 : ℝ) < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 10)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 10) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 10) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 10) = 2028 / 5 - 169 / 2 * Real.log 10 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (16358701211427566598747159484367326987373754578303614412256623672446469551 / 13100507382729565923950876213888969187258663900436415267769532500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 10) / 2 ∧ (2 * (12 / 5) - Real.log 10) / 2 ≤ (16358701214293006893890854439841805478313737589583995488848406830511956177 / 13100507382729565923950876213888969187258663900436415267769532500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (7731241560078812738499789424171271495326106497030354536942185460737369271203740000800363518074281052361041841771055948613086112874508936255465690491961024669670732684936442108658873541925425052828398707774361914866730547606662424726860755843377734229251265021 / 6347015298999699018834337105334008847163417217663831992932713009438974737319802814560531137956443655369669110669287546914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 10) / 2 * Real.cos (169 / 2 * Real.log 10) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 10) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 10)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 10) / 2 * Real.cos (169 / 2 * Real.log 10) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 10) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 10)) / (2 * (169 / 2)) ≤ (773174783656019915778428439242691840121610058628550164271575942584958477836694723213993859288430336202449732567458100181907351519667501160962251592322528298650344315090331916264955990077209085198537703784289389678041893979359445274385387 / 634701529899969901883433710533400884716341721766383199293271300943897473731980281456053113795644365536966911066928754691406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_11 : (663324958071 / 200000000000 : ℝ) ≤ Real.sqrt 11 ∧ Real.sqrt 11 ≤ (829156197589 / 250000000000 : ℝ) := by
  constructor
  · calc (663324958071 / 200000000000 : ℝ) = Real.sqrt ((663324958071 / 200000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 11 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 11 ≤ Real.sqrt ((829156197589 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (829156197589 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_11 : (329296871817 / 25000000000000 : ℝ) ≤ primeTerm 11 ∧ primeTerm 11 ≤ (82683564807 / 6250000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_11
  have hl := PsiOmega.Num.log_bound_11
  have hc := PsiOmega.Num.theta_11_cos
  have hs := PsiOmega.Num.theta_11_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_11
  have hqpos : (0 : ℝ) < Real.sqrt 11 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 11)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 11) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 11) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 11) = 2028 / 5 - 169 / 2 * Real.log 11 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (15734395354324951473775432263659232162718786228323351884162961984946469551 / 13100507382729565923950876213888969187258663900436415267769532500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 11) / 2 ∧ (2 * (12 / 5) - Real.log 11) / 2 ≤ (15734395357206922816525905851128226943306561146781850095838742830511956177 / 13100507382729565923950876213888969187258663900436415267769532500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (430767960545213557341151988776490724945442166187634315295820724013241158139586031738539095390405513931347021216011758641866888088603001584305993243518870123660147892612316517483128876524239985854426131826862471087088270557975251568417349988943492886124039859134935097 / 23644474517552923481294278447829219874603365427493423197167787736054415767341117615105700261728628186023492778350738983281189575791358947753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 11) / 2 * Real.cos (169 / 2 * Real.log 11) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 11) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 11)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 11) / 2 * Real.cos (169 / 2 * Real.log 11) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 11) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 11)) / (2 * (169 / 2)) ≤ (6922372339228396498860145559940718023738241473123909070940952938111935426923567845247874055717982158218669476735120079733646209501122877412374553530535324333470534178420499551190009746292565656735193417503479731655104520712417396318260997151438881475002649 / 378311592280846775700708455165267517993653846839894771154684603776870652277457881841691204187658050976375884453611823732499033212661743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_12 : (3464101615137 / 1000000000000 : ℝ) ≤ Real.sqrt 12 ∧ Real.sqrt 12 ≤ (1732050807569 / 500000000000 : ℝ) := by
  constructor
  · calc (3464101615137 / 1000000000000 : ℝ) = Real.sqrt ((3464101615137 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 12 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 12 ≤ Real.sqrt ((1732050807569 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1732050807569 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_12 : (22123438974627 / 100000000000000 : ℝ) ≤ primeTerm 12 ∧ primeTerm 12 ≤ (2212520339879 / 10000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_12
  have hl := PsiOmega.Num.log_bound_12
  have hc := PsiOmega.Num.theta_12_cos
  have hs := PsiOmega.Num.theta_12_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_12
  have hqpos : (0 : ℝ) < Real.sqrt 12 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 12)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 12) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 12) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 12) = 2028 / 5 - 169 / 2 * Real.log 12 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (51632301031185251224185523384169257679199834716937063551045859857638223678805464297 / 44604940905328994377132010110996177121377207019426181109161023187293527500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 12) / 2 ∧ (2 * (12 / 5) - Real.log 12) / 2 ≤ (51632301041022672156519840216092554151757334818055443623859832083737060429198436119 / 44604940905328994377132010110996177121377207019426181109161023187293527500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-35249458112572503639961110596969430981994861248108715556478072902807857016205538919549687968728260585354592304986254244522963391377627592003040811760447594010515927939876098721954943238356623380077457399531038596816991309153956258759417760440852831547196358843 / 35085634951899950471241964850726889817273014847046798308614429271741909828093734412213149266765910962744438354338342515388715927349223952908068895339965820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 12) / 2 * Real.cos (169 / 2 * Real.log 12) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 12) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 12)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 12) / 2 * Real.cos (169 / 2 * Real.log 12) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 12) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 12)) / (2 * (169 / 2)) ≤ (-2202915442897453715812156008492439086893245586663242470822428558025333993979845929715229402404893538769757615453507475750697098319155594673664012686942762907497534565737440371064334538051937830675977723680865133400058534740380201415771711989475165245087574864967453213679881230117101 / 2192852184493746904452622803170430613579563427940424894288401829483869364255858400763321829172869435171527397146146407211794745459326497056754305958747863769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_13 : (3605551275463 / 1000000000000 : ℝ) ≤ Real.sqrt 13 ∧ Real.sqrt 13 ≤ (450693909433 / 125000000000 : ℝ) := by
  constructor
  · calc (3605551275463 / 1000000000000 : ℝ) = Real.sqrt ((3605551275463 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 13 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 13 ≤ Real.sqrt ((450693909433 / 125000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (450693909433 / 125000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_13 : (2816151061393 / 12500000000000 : ℝ) ≤ primeTerm 13 ∧ primeTerm 13 ≤ (22530803904119 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_13
  have hl := PsiOmega.Num.log_bound_13
  have hc := PsiOmega.Num.theta_13_cos
  have hs := PsiOmega.Num.theta_13_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_13
  have hqpos : (0 : ℝ) < Real.sqrt 13 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 13)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 13) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 13) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 13) = 2028 / 5 - 169 / 2 * Real.log 13 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (249235754541672662652878465510822582126829663091832092293563093075115796039575492109 / 223024704526644971885660050554980885606886035097130905545805115936467637500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 13) / 2 ∧ (2 * (12 / 5) - Real.log 13) / 2 ≤ (249235754590918325595943712350236735231096214988926928888386662422860980929673413491 / 223024704526644971885660050554980885606886035097130905545805115936467637500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-7823295013033411366964633133207434686813866744324663935383766412128441010743732362638338917264966974265912300136412982960715606120860086857076389110624275456359267814065768485784298190504219068515009839745363208254660394983669360843546226860343203837334615443 / 7017126990379990094248392970145377963454602969409359661722885854348381965618746882442629853353182192548887670867668503077743185469844790581613779067993164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 13) / 2 * Real.cos (169 / 2 * Real.log 13) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 13) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 13)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 13) / 2 * Real.cos (169 / 2 * Real.log 13) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 13) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 13)) / (2 * (169 / 2)) ≤ (-488921315282445230876139339887758595408356095926044508425693359057472533017218200282662356383541298922221054072669212555364298094586140568873543758796289822616472458312830805366697885571443736531454680717431187020008151421296024106154340152680964428269307737254400632300154697811789 / 438570436898749380890524560634086122715912685588084978857680365896773872851171680152664365834573887034305479429229281442358949091865299411350861191749572753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_14 : (3741657386773 / 1000000000000 : ℝ) ≤ Real.sqrt 14 ∧ Real.sqrt 14 ≤ (1870828693387 / 500000000000 : ℝ) := by
  constructor
  · calc (3741657386773 / 1000000000000 : ℝ) = Real.sqrt ((3741657386773 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 14 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 14 ≤ Real.sqrt ((1870828693387 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1870828693387 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_14 : (82069807135861 / 100000000000000 : ℝ) ≤ primeTerm 14 ∧ primeTerm 14 ≤ (16415156632279 / 20000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_14
  have hl := PsiOmega.Num.log_bound_14
  have hc := PsiOmega.Num.theta_14_cos
  have hs := PsiOmega.Num.theta_14_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_14
  have hqpos : (0 : ℝ) < Real.sqrt 14 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 14)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 14) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 14) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 14) = 2028 / 5 - 169 / 2 * Real.log 14 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (240971800245320301252568279100075298775017790812694903475032993963558971352075492109 / 223024704526644971885660050554980885606886035097130905545805115936467637500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 14) / 2 ∧ (2 * (12 / 5) - Real.log 14) / 2 ≤ (722915400883785753659130959408825610228023172638369955735554115711190782789020240473 / 669074113579934915656980151664942656820658105291392716637415347809402912500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-696348294526941294363847159517680044294480851900590695338179455784232354094160504908967951963067451145762240451313218239271845207159382432659309547907911722262196801166658634419322938197438186239130658960679265520588228258773305202597101738230858828033852410495471 / 646698423433419887085931896128598033111976209660766586424381160336746881951423712685912767285029270865305487747164329243644811972900895900001525878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 14) / 2 * Real.cos (169 / 2 * Real.log 14) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 14) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 14)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 14) / 2 * Real.cos (169 / 2 * Real.log 14) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 14) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 14)) / (2 * (169 / 2)) ≤ (-58024799398515170016349401047356355015022762093399687614546546271058719842616389708692156498360537787057138843224909683309543292288699482010157825866901140170291842172529078308853248911727102978764976107731847234652526247024473349220637164079350501033531007267662118764782820390921563779 / 53891535286118323923827658010716502759331350805063882202031763361395573495951976057159397273752439238775457312263694103637067664408407991666793823242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_15 : (3872983346207 / 1000000000000 : ℝ) ≤ Real.sqrt 15 ∧ Real.sqrt 15 ≤ (121030729569 / 31250000000 : ℝ) := by
  constructor
  · calc (3872983346207 / 1000000000000 : ℝ) = Real.sqrt ((3872983346207 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 15 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 15 ≤ Real.sqrt ((121030729569 / 31250000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (121030729569 / 31250000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_15 : (0 : ℝ) ≤ primeTerm 15 ∧ primeTerm 15 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_15
  have hl := PsiOmega.Num.log_bound_15
  have hc := PsiOmega.Num.theta_15_cos
  have hs := PsiOmega.Num.theta_15_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_15
  have hqpos : (0 : ℝ) < Real.sqrt 15 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 15)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 15) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 15) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 15) = 2028 / 5 - 169 / 2 * Real.log 15 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (4024020834853686108476774326878191481306944592864796653701823015252534127348153342123055545681 / 3847148566935898159784418362896107080578062504084940921446300383723471449256449987500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 15) / 2 ∧ (2 * (12 / 5) - Real.log 15) / 2 ≤ (12072062507111815218428295304609041416977546820117492747925317876175315671346845271456685654157 / 11541445700807694479353255088688321241734187512254822764338901151170414347769349962500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-8760684632518598488093046996139131902392827534969883172852706887327976207418823194628066790665457784587613728716005464507786649462287125970166980249153137860881983412910571614979459613774326106194307052240542917687244278396780978496161769744203690937546167200779525999661821 / 9621521997553711945262162235105082565904433536525221025274804394233976657899806497068398083840084575246010066404897702995176028431261247771802669911742682989809036254882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 15) / 2 * Real.cos (169 / 2 * Real.log 15) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 15) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 15)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 15) / 2 * Real.cos (169 / 2 * Real.log 15) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 15) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 15)) / (2 * (169 / 2)) ≤ (-7299936774365885770117397074422757319613198753513463976141051342182450503193927987978648944494320965976651389779869765929664983709064568412640393941531975832939151994361788857522534828097473759390766070111333480255019578912691174993841365174067076338101384701936436339008272583480551081200700001 / 8017934997961426621051801862587568804920361280437684187729003661861647214916505414223665069866737146038341722004081419162646690359384373143168891593118902491507530212402343750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_16 : (4 : ℝ) ≤ Real.sqrt 16 ∧ Real.sqrt 16 ≤ (4000000000001 / 1000000000000 : ℝ) := by
  constructor
  · calc (4 : ℝ) = Real.sqrt ((4 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 16 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 16 ≤ Real.sqrt ((4000000000001 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (4000000000001 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_16 : (-7955238949907 / 100000000000000 : ℝ) ≤ primeTerm 16 ∧ primeTerm 16 ≤ (-7952562314293 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_16
  have hl := PsiOmega.Num.log_bound_16
  have hc := PsiOmega.Num.theta_16_cos
  have hs := PsiOmega.Num.theta_16_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_16
  have hqpos : (0 : ℝ) < Real.sqrt 16 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 16)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 16) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 16) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 16) = 2028 / 5 - 169 / 2 * Real.log 16 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (111650144473125599957979976217524237391214655072021299456924023588273859525120927893478168228376246831 / 110140597242241435737090240758525446922038518716885890466165272076977206364951744416085612500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 16) / 2 ∧ (2 * (12 / 5) - Real.log 16) / 2 ≤ (334950433504425143399544402758784954673847869072304523368423773107543374108643303801143501052394530707 / 330421791726724307211270722275576340766115556150657671398495816230931619094855233248256837500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-2216894590818007510010508700080303837671342503231197505581856161390692672082093866810616210336304224596876740112347636342800711559248150076938264473470819820195927996143096401933445925237517926976269907080042929823983460482305649397114795377822660552296769109597381999139329993129174413691436981396763 / 9626552237552543348822790628708718061198770733721581569549101454396748041683966429405057688421282626382280335146550787904374104549284142078654058283468331279401453945299256967846304178237915039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 16) / 2 * Real.cos (169 / 2 * Real.log 16) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 16) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 16)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 16) / 2 * Real.cos (169 / 2 * Real.log 16) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 16) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 16)) / (2 * (169 / 2)) ≤ (-46169764404959494034934494954851050149045417787720363474336039937426492275377994435404023197615508001488316830756775009451887485643662059458386819856193827933193798218699436744987064328795845385132123092021532280353749752569296800586898694708288902065803821105511833530074207734636871029830057674085972394291924919473472769 / 200553171615677986433808138098098292941641056952532949365606280299932250868415967279272035175443388049630840315553141414674460511443419626638626214238923568320863623860401186830131337046623229980468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_17 : (4123105625617 / 1000000000000 : ℝ) ≤ Real.sqrt 17 ∧ Real.sqrt 17 ≤ (2061552812809 / 500000000000 : ℝ) := by
  constructor
  · calc (4123105625617 / 1000000000000 : ℝ) = Real.sqrt ((4123105625617 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 17 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 17 ≤ Real.sqrt ((2061552812809 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2061552812809 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_17 : (7684363198321 / 50000000000000 : ℝ) ≤ primeTerm 17 ∧ primeTerm 17 ≤ (768511726393 / 5000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_17
  have hl := PsiOmega.Num.log_bound_17
  have hc := PsiOmega.Num.theta_17_cos
  have hs := PsiOmega.Num.theta_17_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_17
  have hqpos : (0 : ℝ) < Real.sqrt 17 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 17)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 17) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 17) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 17) = 2028 / 5 - 169 / 2 * Real.log 17 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (108311528443684762238957504597834122986500923619077572502743421593003446975828485104313682408063746831 / 110140597242241435737090240758525446922038518716885890466165272076977206364951744416085612500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 17) / 2 ∧ (2 * (12 / 5) - Real.log 17) / 2 ≤ (324934585423862779725294944736015022123415609975385833547452063674068214398029306274921603552394530707 / 330421791726724307211270722275576340766115556150657671398495816230931619094855233248256837500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (315793650612999672110771791954952127488212022885710767055603057807554399931576696643254373771454723309378503702962208869729911545649955804596842305456186922654885841689061153940008750215298889851782103227060722302326269539752106978918683253764485557066151398459403846927672480861996064613885560398705195301466438933389 / 401106343231355972867616276196196585883282113905065898731212560599864501736831934558544070350886776099261680631106282829348921022886839253277252428477847136641727247720802373660262674093246459960937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 17) / 2 * Real.cos (169 / 2 * Real.log 17) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 17) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 17)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 17) / 2 * Real.cos (169 / 2 * Real.log 17) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 17) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 17)) / (2 * (169 / 2)) ≤ (3789895672105255812157191504489088036998502198883174586765739826640136245534370516111082535152241673388547186330859222834106933877061791672776516354344572079122680297756912464631642972301925440423912868151619260825287009528579590544268878639049318146344983573755637948531831014136550103805601698749701167843100637886777 / 4813276118776271674411395314354359030599385366860790784774550727198374020841983214702528844210641313191140167573275393952187052274642071039327029141734165639700726972649628483923152089118957519531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_18 : (4242640687119 / 1000000000000 : ℝ) ≤ Real.sqrt 18 ∧ Real.sqrt 18 ≤ (53033008589 / 12500000000 : ℝ) := by
  constructor
  · calc (4242640687119 / 1000000000000 : ℝ) = Real.sqrt ((4242640687119 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 18 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 18 ≤ Real.sqrt ((53033008589 / 12500000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (53033008589 / 12500000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_18 : (2737555224641 / 20000000000000 : ℝ) ≤ primeTerm 18 ∧ primeTerm 18 ≤ (13689367635887 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_18
  have hl := PsiOmega.Num.log_bound_18
  have hc := PsiOmega.Num.theta_18_cos
  have hs := PsiOmega.Num.theta_18_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_18
  have hqpos : (0 : ℝ) < Real.sqrt 18 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 18)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 18) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 18) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 18) = 2028 / 5 - 169 / 2 * Real.log 18 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (105163797523340631348519107929997771233287536135886146073579835117357764202386216173893554362963746831 / 110140597242241435737090240758525446922038518716885890466165272076977206364951744416085612500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 18) / 2 ∧ (2 * (12 / 5) - Real.log 18) / 2 ≤ (315491392667970196785090458406959549615057905554949204362189292373748122928173403010784103295594530707 / 330421791726724307211270722275576340766115556150657671398495816230931619094855233248256837500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (880805769445340617583219790983120147405238608414317079673438109385777789283243804257789343141656609487003987134610016202658766980592763085823455156880907901524443075188845181784960961147627002118536952792643947304956294523404289867636822673938853818663779753388706386422213171797587324902817801503399770298905051009447 / 1345889551872519425938027534171849699965274962784378815449535814219403263274240904357311702759204646832190131294217285197015597473582689141902234375819478525283954529619481823242187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 18) / 2 * Real.cos (169 / 2 * Real.log 18) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 18) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 18)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 18) / 2 * Real.cos (169 / 2 * Real.log 18) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 18) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 18)) / (2 * (169 / 2)) ≤ (264272454732479133798051721382311404148069851413690834334169934922994745532394954775330134644349902631383237405694236844715005189065188856846300993790033332233621986997014774184693550428191687596666220568462344476023115188577905386570319831855485795516138016109232663551231929286332558725422127021 / 403766865561755827781408260251554909989582488835313644634860744265820978982272271307193510827761394049657039388265185559104679242074806742570670312745843557585186358885844546972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_19 : (217944947177 / 50000000000 : ℝ) ≤ Real.sqrt 19 ∧ Real.sqrt 19 ≤ (4358898943541 / 1000000000000 : ℝ) := by
  constructor
  · calc (217944947177 / 50000000000 : ℝ) = Real.sqrt ((217944947177 / 50000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 19 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 19 ≤ Real.sqrt ((4358898943541 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (4358898943541 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_19 : (51142800134663 / 100000000000000 : ℝ) ≤ primeTerm 19 ∧ primeTerm 19 ≤ (51147899131741 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_19
  have hl := PsiOmega.Num.log_bound_19
  have hc := PsiOmega.Num.theta_19_cos
  have hs := PsiOmega.Num.theta_19_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_19
  have hqpos : (0 : ℝ) < Real.sqrt 19 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 19)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 19) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 19) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 19) = 2028 / 5 - 169 / 2 * Real.log 19 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (7086002358612616328031619818292905390750613399881063517925583445134853469363896998374895731692043265307750267 / 7637584839120308703371048960278835974767621394247430362392474581799208088151340071864030821518662500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 19) / 2 ∧ (2 * (12 / 5) - Real.log 19) / 2 ≤ (21258007082871508274949083121958032202407273634526351385474407938825802103005700130214544841532547926781387599 / 22912754517360926110113146880836507924302864182742291087177423745397624264454020215592092464555987500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-5841694002410604908155639773119176556631244281362179310415653172937103493166834754137190566701856598010442502670167303228148478979978513586943518557466967783103246118583617753138539405861631705250483108270600410117988610131400536005300224907229259331420683015724414593626903073953962252192909378227607420897410137114638431866179609437 / 7715014774959872783651818050066508408441642944823069281128644912918199302413558717979900891143583156577682106909972650696985174958706107433109554823281080557789592618701728008064532332365125184878706932067871093750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 19) / 2 * Real.cos (169 / 2 * Real.log 19) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 19) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 19)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 19) / 2 * Real.cos (169 / 2 * Real.log 19) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 19) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 19)) / (2 * (169 / 2)) ≤ (-486759303163162076568800846756295359230258023378716539924830760731745078951081332067360616220349973334388913885856416368272969420866420739295699389943698441976817957392789089510557437143313604426140457392807267484353933261203071063909031974196290843890249168091973985174354892036758222559826199165983175849936778438167472102628809687 / 642917897913322731970984837505542367370136912068589106760720409409849941867796559831658407595298596381473508909164387558082097913225508952759129568606756713149132718225144000672044361030427098739892244338989257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_20 : (4472135954999 / 1000000000000 : ℝ) ≤ Real.sqrt 20 ∧ Real.sqrt 20 ≤ (894427191 / 200000000 : ℝ) := by
  constructor
  · calc (4472135954999 / 1000000000000 : ℝ) = Real.sqrt ((4472135954999 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 20 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 20 ≤ Real.sqrt ((894427191 / 200000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (894427191 / 200000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_20 : (0 : ℝ) ≤ primeTerm 20 ∧ primeTerm 20 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_20
  have hl := PsiOmega.Num.log_bound_20
  have hc := PsiOmega.Num.theta_20_cos
  have hs := PsiOmega.Num.theta_20_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_20
  have hqpos : (0 : ℝ) < Real.sqrt 20 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 20)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 20) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 20) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 20) = 2028 / 5 - 169 / 2 * Real.log 20 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (6890123914783434150693009352698968255711596623455214691212616450361844495471653789903701364087583109057750267 / 7637584839120308703371048960278835974767621394247430362392474581799208088151340071864030821518662500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 20) / 2 ∧ (2 * (12 / 5) - Real.log 20) / 2 ≤ (20670371751551036438753238168862385966681464100539787586497924448445354492148997439391732058316895426781387599 / 22912754517360926110113146880836507924302864182742291087177423745397624264454020215592092464555987500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-19872431602900143941372846358620201832187513386690866867806553465352247786293653410054184376950736433392574905682403784281538061674381942926423463275992560208803087871970995494205561694972987676685256568114047937588814871212417665434725357862561139732300582938772946272707443428032921937504630964880757902534114254412351 / 94802101554706916765513540199217255322930908505985875326508788689938833028057809526537022150372349828026557729709743931764553829892580648138050209668477917894118514098606833763096973300102658271789550781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 20) / 2 * Real.cos (169 / 2 * Real.log 20) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 20) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 20)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 20) / 2 * Real.cos (169 / 2 * Real.log 20) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 20) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 20)) / (2 * (169 / 2)) ≤ (-1655447980169778131572338869523804366535702282818878388684575174652657187115968276303007341884258271131626868332907614248090137179188196610702345676749049841500473725456287142338599083767718241394313640584397936269190786379909846562080442044739097003908578743826596342392573959184187152288411055512835202139232537586528925096962971987085679477 / 7900175129558909730459461683268104610244242375498822943875732390828236085671484127211418512531029152335546477475811994313712819157715054011504184139039826491176542841550569480258081108341888189315795898437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_21 : (916515138991 / 200000000000 : ℝ) ≤ Real.sqrt 21 ∧ Real.sqrt 21 ≤ (1145643923739 / 250000000000 : ℝ) := by
  constructor
  · calc (916515138991 / 200000000000 : ℝ) = Real.sqrt ((916515138991 / 200000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 21 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 21 ≤ Real.sqrt ((1145643923739 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1145643923739 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_21 : (29481209378943 / 50000000000000 : ℝ) ≤ primeTerm 21 ∧ primeTerm 21 ≤ (368548157653 / 625000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_21
  have hl := PsiOmega.Num.log_bound_21
  have hc := PsiOmega.Num.theta_21_cos
  have hs := PsiOmega.Num.theta_21_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_21
  have hqpos : (0 : ℝ) < Real.sqrt 21 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 21)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 21) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 21) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 21) = 2028 / 5 - 169 / 2 * Real.log 21 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (776677310688044306102111245985665106034993872872197167419761366993398237641689780595725102341654734653536979291355667 / 884861564275675148319805625922905836738708472543830535798845376036319993901687373785233599528061287851162500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 21) / 2 ∧ (2 * (12 / 5) - Real.log 21) / 2 ≤ (2330031932912021146769564325893521473536165852778395233434917457696423837871198277374757253737540300684317724728651399 / 2654584692827025444959416877768717510216125417631491607396536128108959981705062121355700798584183863553487500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (232222482247865394143645883359084562113746437285022531422868417283253932022682874493069931313029103774507684944817672141211389944580917581869848701976539148772710049558208611491635166466406498345317224227593568843070522258101086143351433861672130048812650338139597429886055684468506191048748643812264387922507223679371472963407164210122462222362280175709 / 282776958012288934605123176912903061313974783216244331903796274598103432528829114744863975701338980021883660116462674090662441750610811934418998443424652028478798037927558406868221711815949802630109659861764907836914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 21) / 2 * Real.cos (169 / 2 * Real.log 21) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 21) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 21)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 21) / 2 * Real.cos (169 / 2 * Real.log 21) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 21) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 21)) / (2 * (169 / 2)) ≤ (2786919634293439845528533909605954666863648498963732147980397803158737347996805896488479554347585593029519366033695718769768834784780720331343989166632938731028167500398991852624351238093816118706015960268443017209007458585262256324197388246402782058985232637448184826090664665429858540135947462837319712113627722235805920127654409 / 3393323496147467215261478122954836735767697398594931982845555295177241190345949376938367708416067760262603921397552089087949301007329743213027981321095824341745576455130700882418660541791397631561315918341178894042968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_22 : (4690415759823 / 1000000000000 : ℝ) ≤ Real.sqrt 22 ∧ Real.sqrt 22 ≤ (293150984989 / 62500000000 : ℝ) := by
  constructor
  · calc (4690415759823 / 1000000000000 : ℝ) = Real.sqrt ((4690415759823 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 22 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 22 ≤ Real.sqrt ((293150984989 / 62500000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (293150984989 / 62500000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_22 : (-3369 / 100000000000000 : ℝ) ≤ primeTerm 22 ∧ primeTerm 22 ≤ (1329 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_22
  have hl := PsiOmega.Num.log_bound_22
  have hc := PsiOmega.Num.theta_22_cos
  have hs := PsiOmega.Num.theta_22_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_22
  have hqpos : (0 : ℝ) < Real.sqrt 22 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 22)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 22) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 22) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 22) = 2028 / 5 - 169 / 2 * Real.log 22 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (111152411009740827059961228549434476169820821721351009454203484895997851554220946858979134462956933910412299998470752464896481 / 130082120834711426328288691129566825094569730379576776323644019928848913753256555892926207857905824735574214864987500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 22) / 2 ∧ (2 * (12 / 5) - Real.log 22) / 2 ≤ (333457233155305673062661099644332899412337414497604329098070858633747077801655324654625646960945636774294847101014139656761757 / 390246362504134278984866073388700475283709191138730328970932059786546741259769667678778623573717474206722644594962500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-4253914712483313633649750882082433859556021322219621303599110255231228552526550823690078077601591837802962457171885629887511613170148909157089956077235091466312227550329774368763400104785066734949385421962658758066497646386864125413079743870491552137816573970890009559804419208775966236897211191219375069806126321000956820931637670628505862115797387784273183 / 5500106304018214512962041464970931498086352714533178686241846137018373132429654020650866218947715779650576079554589308765531205294883524725191386125513757915174717005952241393910911616640180681778584939720705934248831147156715393066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 22) / 2 * Real.cos (169 / 2 * Real.log 22) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 22) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 22)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 22) / 2 * Real.cos (169 / 2 * Real.log 22) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 22) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 22)) / (2 * (169 / 2)) ≤ (-1772297344886190013207698909267230053761972637529316627942826144463854625395123521689036313739122352497656014384342122295004279832572688018498900337355875074852878599861702645115908584777362132140974203338614292591629239506235489943803270029698019152588466085361355961229249057068071942691951108642079727318975394585430084215229736793574031705369787068252109 / 2291710960007589380400850610404554790869313631055491119267435890424322138512355841937860924561548241521073366481078878652304668872868135302163077552297399131322798752480100580796213173600075284074410391550294139270346311315298080444335937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_23 : (299739470207 / 62500000000 : ℝ) ≤ Real.sqrt 23 ∧ Real.sqrt 23 ≤ (4795831523313 / 1000000000000 : ℝ) := by
  constructor
  · calc (299739470207 / 62500000000 : ℝ) = Real.sqrt ((299739470207 / 62500000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 23 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 23 ≤ Real.sqrt ((4795831523313 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (4795831523313 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_23 : (-1922656225041 / 25000000000000 : ℝ) ≤ primeTerm 23 ∧ primeTerm 23 ≤ (-7689286263989 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_23
  have hl := PsiOmega.Num.log_bound_23
  have hc := PsiOmega.Num.theta_23_cos
  have hs := PsiOmega.Num.theta_23_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_23
  have hqpos : (0 : ℝ) < Real.sqrt 23 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 23)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 23) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 23) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 23) = 2028 / 5 - 169 / 2 * Real.log 23 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (108261221234414729955309621334783849192110318664680512643414545719249178497928832864971920672264802048517427038857238164896481 / 130082120834711426328288691129566825094569730379576776323644019928848913753256555892926207857905824735574214864987500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 23) / 2 ∧ (2 * (12 / 5) - Real.log 23) / 2 ≤ (324783663830372260233437982443297599579202646763097120909863508393836624545610797079195569271603634346710832883008897256761757 / 390246362504134278984866073388700475283709191138730328970932059786546741259769667678778623573717474206722644594962500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (259079635107579157500663459525155189178198866396616041217116917586156727007888765574323377273639729065186750052720434558610496252974161177187960016772911456969212240250568022480077611988734653601251941894705792668348567489120265458262614577518305989867980669497350717150936546968552491052537493492598970050720225810458696092904750525346795426013592259098478458241031 / 625789872812739073474792273347803761560047242186886108301294493811868231956440635238498556466940106484687767273766605797322661580217858813177331043614009789459878912677232798596085943937727224237918997586000319630089232743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 23) / 2 * Real.cos (169 / 2 * Real.log 23) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 23) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 23)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 23) / 2 * Real.cos (169 / 2 * Real.log 23) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 23) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 23)) / (2 * (169 / 2)) ≤ (31094968620952354790861215013380842608371903666133360803852848864324781746199014287793992114063833000165018235132422087106149213337632264488014669956913397597632940257658226428540744791406612539194319972280080472869493029451187611150230253817821482838865993451535658169245399731310683790343697421157267447133460233330274277715090295245632668872364306267843 / 75094784737528688816975072801736451387205669062426332996155339257424187834772876228619826776032812778162532072851992695678719389626143057581279725233681174735185469521267935831530313272527266908550279710320038355610707929179687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_24 : (2449489742783 / 500000000000 : ℝ) ≤ Real.sqrt 24 ∧ Real.sqrt 24 ≤ (4898979485567 / 1000000000000 : ℝ) := by
  constructor
  · calc (2449489742783 / 500000000000 : ℝ) = Real.sqrt ((2449489742783 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 24 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 24 ≤ Real.sqrt ((4898979485567 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (4898979485567 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_24 : (-309020937953 / 100000000000000 : ℝ) ≤ primeTerm 24 ∧ primeTerm 24 ≤ (-308619476999 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_24
  have hl := PsiOmega.Num.log_bound_24
  have hc := PsiOmega.Num.theta_24_cos
  have hs := PsiOmega.Num.theta_24_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_24
  have hqpos : (0 : ℝ) < Real.sqrt 24 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 24)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 24) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 24) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 24) = 2028 / 5 - 169 / 2 * Real.log 24 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (24194315478481569931509445040288416924307136213233025060778081295215758703247266287530708765050231123036762867061156145430178714220367 / 29833684913411737914241354165131341408281870475892148422983572016089993626683021084059052391654866379321041457230062242412500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 24) / 2 ∧ (2 * (12 / 5) - Real.log 24) / 2 ≤ (72582946464777639994864890464972597863785813765499759073504321253371308439772436767969336226557216333506966108644548839071805956497299 / 89501054740235213742724062495394024224845611427676445268950716048269980880049063252177157174964599137963124371690186727237500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-158014896275473980294410185407363192208287402814707619285945155129708271943924592571981310613878959459460668433992287740587131113093193114894253104862976003947972616831323893623071892253608967655079128638711988445600550524963893848825774862214010187475106884737801620900509888535694441482810371032056727567174125969487872232286747143243212806645646524892574296899638921 / 2893008187961765347534305554898287758549283725996369509968639905868896951614245022677144349079125956992081058376029039771336277784760310973670465293134628447541494221685180858490344159498288483716448095702785480537337171435001252730261889352798461914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 24) / 2 * Real.cos (169 / 2 * Real.log 24) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 24) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 24)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 24) / 2 * Real.cos (169 / 2 * Real.log 24) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 24) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 24)) / (2 * (169 / 2)) ≤ (-657540058049896404900316833170541242281634256319679947708614047698854011757067898875257104373559026893597603312321706204638072768846482486917864364185056446517324919269296663425368787585323066338116214485007114041726453651316308358123129233222032983485252704446961733902848703650612426584369992798383789671742743340931337569226375701448270078851673979494152669999563170002664557 / 12054200783174022281392939812076198993955348858318206291535999607787070631726020927821434787829691487467004409900120999047234490769834629056960272054727618531422892590354920243709767331242868682151867065428272835572238214312505219709424538969993591308593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_25 : (5 : ℝ) ≤ Real.sqrt 25 ∧ Real.sqrt 25 ≤ (5000000000001 / 1000000000000 : ℝ) := by
  constructor
  · calc (5 : ℝ) = Real.sqrt ((5 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 25 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 25 ≤ Real.sqrt ((5000000000001 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (5000000000001 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_25 : (0 : ℝ) ≤ primeTerm 25 ∧ primeTerm 25 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_25
  have hl := PsiOmega.Num.log_bound_25
  have hc := PsiOmega.Num.theta_25_cos
  have hs := PsiOmega.Num.theta_25_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_25
  have hqpos : (0 : ℝ) < Real.sqrt 25 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 25)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 25) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 25) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 25) = 2028 / 5 - 169 / 2 * Real.log 25 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (23585380217416693581710730542855906606230436907913985893041524218786658725953215468631051966642038894848782029457033945359256839220367 / 29833684913411737914241354165131341408281870475892148422983572016089993626683021084059052391654866379321041457230062242412500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 25) / 2 ∧ (2 * (12 / 5) - Real.log 25) / 2 ≤ (70756140681715029967573457719891017474861401009803717534847088335338420270600554519876691465034705402284721094341693427294305956497299 / 89501054740235213742724062495394024224845611427676445268950716048269980880049063252177157174964599137963124371690186727237500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-31595326400072289862283275184492170959410687748350102973243258239992476824095358073074198451023403217561985271857126143323363538778997243834905647923190425301185831346741116840873915605723396761759458152600400656142973912607744433776889392381017455442452687174864547705901160410097082667496943767418101527618355938433091625742532328153671668726844726528078753 / 168395239624763218891708270815334268761174970189829444860145444159215371567653784451374338769768711470072219286581329056721662507902383278919760213066743945676221874407794143683879179850819548808297147957071748127773006646602953128182672042911782739338377723470330238342285156250000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 25) / 2 * Real.cos (169 / 2 * Real.log 25) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 25) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 25)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 25) / 2 * Real.cos (169 / 2 * Real.log 25) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 25) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 25)) / (2 * (169 / 2)) ≤ (-41124384519883432681249062738401434877730465708293993129340128659661476853198653054727053990947047586021028982787072056292811743834727645141358633204303897462976984616172018560358205396308774198623814445687625307590907070766229140729748022538896676332756060948547101957190266861715188631209997302031024412386996713681477351811606609503670798827112265481461762837407934031879674779 / 219264634928077107931911810957466495782779909101340422994981047082311681728715865171060336939803009726656535529402772209272998057164561561093437777430656179265913898968481957921717682097421287510803578069103838708037769071097595218987854222541383775180179327435325831174850463867187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_26 : (637377439199 / 125000000000 : ℝ) ≤ Real.sqrt 26 ∧ Real.sqrt 26 ≤ (5099019513593 / 1000000000000 : ℝ) := by
  constructor
  · calc (637377439199 / 125000000000 : ℝ) = Real.sqrt ((637377439199 / 125000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 26 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 26 ≤ Real.sqrt ((5099019513593 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (5099019513593 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_26 : (4257840882699 / 20000000000000 : ℝ) ≤ primeTerm 26 ∧ primeTerm 26 ≤ (10647005288019 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_26
  have hl := PsiOmega.Num.log_bound_26
  have hc := PsiOmega.Num.theta_26_cos
  have hs := PsiOmega.Num.theta_26_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_26
  have hqpos : (0 : ℝ) < Real.sqrt 26 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 26)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 26) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 26) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 26) = 2028 / 5 - 169 / 2 * Real.log 26 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (23000331018241038442180815943690607541504523433993895494220464377276211180614974847241871300905484210009402548252939295982319339220367 / 29833684913411737914241354165131341408281870475892148422983572016089993626683021084059052391654866379321041457230062242412500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 26) / 2 ∧ (2 * (12 / 5) - Real.log 26) / 2 ≤ (69000993084287835457033566074033195451922687050603211957290714389764711572256304981716528097954277395138311660720448260321805956497299 / 89501054740235213742724062495394024224845611427676445268950716048269980880049063252177157174964599137963124371690186727237500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (4536543928858440214264445080526282732795945875700141453368621269205343753785873548155601901959162856006534150603022657152924484971783148456832343848024232261924783431670937766754163676642490807913411585487722586036645677935425250333194968616344345801235040725793995771750958578994103831528680272845498129120551116653694508283308246627841887090322711999311201611810577467661486905523193779 / 14714600565397976417715990981538328850043150461814216664472655771224451454743677890407024887487416366536870617553858641415081165490520787423047207098056174965115835681585596000622274574271079934267415851352872113735642351455694848278106126672355458140373229980468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 26) / 2 * Real.cos (169 / 2 * Real.log 26) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 26) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 26)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 26) / 2 * Real.cos (169 / 2 * Real.log 26) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 26) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 26)) / (2 * (169 / 2)) ≤ (217803267806029736503474878291195152740167117250050807767791769800338103561067108915436459787607219551017446574502658527366225925121591660540609423478289631917316551192536942681330305279210816052180591243662222204312311120315071864219895601971679193103250363792854211345704325649218896285555013744988653137661624342885758823620299052417878456938825288775994339329753 / 706300827139102868050367567113839784802071222167082399894687477018773669827696538739537194599395985593769789642585214787923895943544997796306265940706696398325560112716108608029869179565011836844835960864937861459310832869873352717349094080273061990737915039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_27 : (2598076211353 / 500000000000 : ℝ) ≤ Real.sqrt 27 ∧ Real.sqrt 27 ≤ (5196152422707 / 1000000000000 : ℝ) := by
  constructor
  · calc (2598076211353 / 500000000000 : ℝ) = Real.sqrt ((2598076211353 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 27 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 27 ≤ Real.sqrt ((5196152422707 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (5196152422707 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_27 : (32270143277 / 20000000000000 : ℝ) ≤ primeTerm 27 ∧ primeTerm 27 ≤ (80691933923 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_27
  have hl := PsiOmega.Num.log_bound_27
  have hc := PsiOmega.Num.theta_27_cos
  have hs := PsiOmega.Num.theta_27_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_27
  have hqpos : (0 : ℝ) < Real.sqrt 27 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 27)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 27) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 27) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 27) = 2028 / 5 - 169 / 2 * Real.log 27 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (9383204705116238995433188913938364676682755781623075022894558822421740846961306348762444717406207666392351971547168564666434610867758113205931 / 12476312570370884049032954826074704729987751106627861624578787430169758817077563956977469856040935931349287937479764293886380946862500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 27) / 2 ∧ (2 * (12 / 5) - Real.log 27) / 2 ≤ (28149614127744423291670285526007005181705661175364973239740280518990641936512046642912159614535669888035328296189100005565674022230224508473407 / 37428937711112652147098864478224114189963253319883584873736362290509276451232691870932409568122807794047863812439292881659142840587500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-84228354594283235016559550628060349884121330455790692098433031760587292106637765125910321853717537513042345301340195964229533379606035975926271288198585414084681853438441451323659103458976236904797151718447010455962559917515152172986865760480740394548366202453062643114008735794385195031652358427509049296474946610511307032127197723271221674521628078040620763849978015898608477479130141 / 252975441869674920963907692151458154446582572329201402119284397498861502967870623513713286053521171037352768564762221957153871490178660520008585643506787014561438227896584261908918341593587686522433769404281909777239028616677953204534553735294229084941875271797180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 27) / 2 * Real.cos (169 / 2 * Real.log 27) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 27) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 27)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 27) / 2 * Real.cos (169 / 2 * Real.log 27) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 27) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 27)) / (2 * (169 / 2)) ≤ (-7017587810615680367528407210149447179814424123740043628560795784284324717075603372560044890959368092800797069535293295599821939623747745078573522462457543249666156481110353742173856173325876783919572090437652550364572524193702093568107368788213937302660875185147088190551272338655893948358815513012854145079350752084208632304988724063654394064551136472979337722245986835040937574797090599315840924146904617767 / 21081286822472910080325641012621512870548547694100116843273699791571791913989218626142773837793430919779397380396851829762822624181555043334048803625565584546786518991382021825743195132798973876869480783690159148103252384723162767044546144607852423745156272649765014648437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_28 : (5291502622129 / 1000000000000 : ℝ) ≤ Real.sqrt 28 ∧ Real.sqrt 28 ≤ (529150262213 / 100000000000 : ℝ) := by
  constructor
  · calc (5291502622129 / 1000000000000 : ℝ) = Real.sqrt ((5291502622129 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 28 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 28 ≤ Real.sqrt ((529150262213 / 100000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (529150262213 / 100000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_28 : (1078817106871 / 20000000000000 : ℝ) ≤ primeTerm 28 ∧ primeTerm 28 ≤ (674424932197 / 12500000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_28
  have hl := PsiOmega.Num.log_bound_28
  have hc := PsiOmega.Num.theta_28_cos
  have hs := PsiOmega.Num.theta_28_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_28
  have hqpos : (0 : ℝ) < Real.sqrt 28 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 28)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 28) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 28) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 28) = 2028 / 5 - 169 / 2 * Real.log 28 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (9156337657047281678199459253863748573239676372621380987404509541049778271213685987317592765789859460399033173601393447268340577099396163205931 / 12476312570370884049032954826074704729987751106627861624578787430169758817077563956977469856040935931349287937479764293886380946862500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 28) / 2 ∧ (2 * (12 / 5) - Real.log 28) / 2 ≤ (27469012983562144382851935461246557757650099057327813945666497430127928546197002388003671523012661240039524484071376415994510052377506908473407 / 37428937711112652147098864478224114189963253319883584873736362290509276451232691870932409568122807794047863812439292881659142840587500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (53143068731360107440917766642659136921545741024910641698522424361726070762573239001497330067733067790893570421378179918194559920226632486822113854056116847316263456724199165600239967096103758245035927450671394437907922811654920195699206451649239486029748950862132006620323453526334463831753415025789525883230744187920754407646761376193188509884094516186547473235400546394946205246138508631 / 190469808097626381226193648123566128211176574520632259338576823562490969823045734393638304263834461506779395551826796530658511265100365570804362284346087652207139458172560683613138689685558457163712408498090961471619560723839274700818765117571517177367886250549075968948364357725966389267568956711329519748687744140625000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 28) / 2 * Real.cos (169 / 2 * Real.log 28) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 28) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 28)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 28) / 2 * Real.cos (169 / 2 * Real.log 28) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 28) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 28)) / (2 * (169 / 2)) ≤ (653181095168153285903389769109180639452691568179657372189990139286836449726909117733714912655596030829801212602990161164287156303820610967860427713460701513505657041241952083896073354106531093526121486386883675908513656774284284672568695133087280511955907201895414588595655286616735865201451361359263513685006186746962245728862380096684251479550542760070906692102858973 / 2340493001903632972507467548142380583458937747709529202752432007935889037185585984229027482793997862995305212540847675768731786425553292134044003750044725070321329662024425680238248218856142321627698075624541734563261162174537007523660985764718803075496586246747045506437501227736674991319887340068817138671875000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_29 : (2692582403567 / 500000000000 : ℝ) ≤ Real.sqrt 29 ∧ Real.sqrt 29 ≤ (1077032961427 / 200000000000 : ℝ) := by
  constructor
  · calc (2692582403567 / 500000000000 : ℝ) = Real.sqrt ((2692582403567 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 29 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 29 ≤ Real.sqrt ((1077032961427 / 200000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1077032961427 / 200000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_29 : (2377299810251 / 25000000000000 : ℝ) ≤ primeTerm 29 ∧ primeTerm 29 ≤ (9513391791189 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_29
  have hl := PsiOmega.Num.log_bound_29
  have hc := PsiOmega.Num.theta_29_cos
  have hs := PsiOmega.Num.theta_29_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_29
  have hqpos : (0 : ℝ) < Real.sqrt 29 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 29)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 29) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 29) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 29) = 2028 / 5 - 169 / 2 * Real.log 29 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (8937432519805682563365666390919503018498283531685412248794964339203451188070680300094790172328223827120913629460617714351921613576427413205931 / 12476312570370884049032954826074704729987751106627861624578787430169758817077563956977469856040935931349287937479764293886380946862500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 29) / 2 ∧ (2 * (12 / 5) - Real.log 29) / 2 ≤ (26812297571856499173707628113308605769738354262259095696474317807749082198260684654837902009921751153749022635053192314654218956150006908473407 / 37428937711112652147098864478224114189963253319883584873736362290509276451232691870932409568122807794047863812439292881659142840587500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-1493552044258901026115327048543216264987256709103840630441332904125508025841263439459094112264577338159393887491062597592702549789581839584903760268194765120607882634618248055058191708721234343540805586728635421655710674740847865685352226560420820083246777336299162670020803558400734508758654952822819096231212152211978902755015214855995492362512451578669926288217506335116829 / 9816739159856415391119961167043779450724156430969069173221336580613531132223652035995746887192796412752660634180927569867494806731843875410989301104827590541349034286747696728326005457341193164172340549384317895445624545553309268804521367236903134614767633681076119955832837149500846862792968750000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 29) / 2 * Real.cos (169 / 2 * Real.log 29) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 29) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 29)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 29) / 2 * Real.cos (169 / 2 * Real.log 29) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 29) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 29)) / (2 * (169 / 2)) ≤ (-1943872182833213093583456347658339128215151502460334420973524329202642493353154122754162465591100730145331019764861737970955885152491408458175222322925703506353394160410290124879292966159028966187981853068450249944687370803267423916131919020266748028008535552135362882815619640955097508759896909670406533885297137574526945006046631017086406644703585229844669015490279845498213382091518697700512527 / 12782212447729707540520782769588254493130412019490975485965282006007201995082880255202795426032286995771693534089749439931633862932088379441392319146910925184048221727536063448341152939246345265849401757010830593028156960355871443755887196923050956529645356355567864525824006705079227685928344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_30 : (5477225575051 / 1000000000000 : ℝ) ≤ Real.sqrt 30 ∧ Real.sqrt 30 ≤ (1369306393763 / 250000000000 : ℝ) := by
  constructor
  · calc (5477225575051 / 1000000000000 : ℝ) = Real.sqrt ((5477225575051 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 30 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 30 ≤ Real.sqrt ((1369306393763 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1369306393763 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_30 : (0 : ℝ) ≤ primeTerm 30 ∧ primeTerm 30 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_30
  have hl := PsiOmega.Num.log_bound_30
  have hc := PsiOmega.Num.theta_30_cos
  have hs := PsiOmega.Num.theta_30_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_30
  have hqpos : (0 : ℝ) < Real.sqrt 30 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 30)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 30) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 30) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 30) = 2028 / 5 - 169 / 2 * Real.log 30 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (6238393216537659168539143278692941937416490884838772302452299301226710562468078738064651131346326730222926717899378145404022607774256086717196062817369 / 8919619018477292448765166856930125200718477238492398225820990773784126273298246640569783795623697036023801802851876314491950884082629061887500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 30) / 2 ∧ (2 * (12 / 5) - Real.log 30) / 2 ≤ (18715179658516999079353278103151606858360553091793515435723583376001024702844216036471518026978150041949831026525490011287195207044186641818007659616693 / 26758857055431877346295500570790375602155431715477194677462972321352378819894739921709351386871091108071405408555628943475852652247887185662500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-15404872570786346492642674358152249957308116994970290790895162988937597917982790022917008331077034313541171666682334726640087366569742405002506482601596876893272404582778721077260193132929404484618737425689486935989317106565192673486356326103794379213136039829015464759379137734155842913540138868467230256556704987421711994984645522070888469939538099050981024146820746647895869809286109424869291447060974483 / 353075163172108659455036777696816756378831203153193729888231158244653582950772775790293996832200649902254092638104498930605166751774283782164070578231635236830066079386103417917642888840007758008104235193468574065720290961586193923508354522347699288534473828935927374593069804687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 30) / 2 * Real.cos (169 / 2 * Real.log 30) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 30) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 30)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 30) / 2 * Real.cos (169 / 2 * Real.log 30) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 30) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 30)) / (2 * (169 / 2)) ≤ (-128181053202065752897871309181976659893599299423224212707122205341412048669704812261707060990584297314163736383959725214816596439962494562798849443510145303587599456116112045407948005000757873799450680182862119924556213795986131787520324195279394031806427937181930179549624326329789386489786864610909352789919818127377684396244736779251925816453592162132598009189706315239756606096031299701577420465454083033342996857 / 2942293026434238828791973147473472969823593359609947749068592985372113191256439798252449973601672082518784105317537491088376389598119031518033921485263626973583883994884195149313690740333397983400868626612238117214335758013218282695902954352897494071120615241132728121608915039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_31 : (556776436283 / 100000000000 : ℝ) ≤ Real.sqrt 31 ∧ Real.sqrt 31 ≤ (5567764362831 / 1000000000000 : ℝ) := by
  constructor
  · calc (556776436283 / 100000000000 : ℝ) = Real.sqrt ((556776436283 / 100000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 31 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 31 ≤ Real.sqrt ((5567764362831 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (5567764362831 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_31 : (8823244092771 / 50000000000000 : ℝ) ≤ primeTerm 31 ∧ primeTerm 31 ≤ (17650531790041 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_31
  have hl := PsiOmega.Num.log_bound_31
  have hc := PsiOmega.Num.theta_31_cos
  have hs := PsiOmega.Num.theta_31_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_31
  have hqpos : (0 : ℝ) < Real.sqrt 31 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 31)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 31) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 31) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 31) = 2028 / 5 - 169 / 2 * Real.log 31 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (5145413143073675505512289298651252565583666060640054125246606937302502953566211319383887470210669725134105101101342164678388900353230493796023993798875995952069 / 7533477229335171854722291945010979959993708417983374358147371495693200822944614182410915926153514504570366750645825986129414410969868284025282578137500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 31) / 2 ∧ (2 * (12 / 5) - Real.log 31) / 2 ≤ (15436239436748523442882297393782596058705883706939171342859105964287447979115480131201687545417443325124062350464270974196356664127586440762164009319425985652593 / 22600431688005515564166875835032939879981125253950123074442114487079602468833842547232747778460543513711100251937477958388243232909604852075847734412500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (2199156050607735392885576423980901713275609608786861016039138192281877549848887317879007816814517435057529051831092400036740658873255907152556792536256076717924646727237279790481782600218375645834929882119137184462531131912279536494049950263513176392679004993932551265303762223121915373016768629148911513143272350742033105335870486832340740199321333224845836970181351997436968926803098548271213777481451223541420187620913196039281657524252792691 / 7686269071442851796142285383559727849706358341177812607164519659068144119724816375493657160094198770513327858435843551031370196633067427019160967539008924126473818837426919640800587570429006021225062628568366556250677620079061772518890632980259260731194031241944944939217665262430973023019775152206420898437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 31) / 2 * Real.cos (169 / 2 * Real.log 31) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 31) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 31)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 31) / 2 * Real.cos (169 / 2 * Real.log 31) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 31) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 31)) / (2 * (169 / 2)) ≤ (52791839418941875594116760829163141457379969140936302989499975836624844044267854854995623203136778858039298030610640827004076022941872922988952651039401312090136349130982714067186294834528485932336232975525106545117697231494786189455883885546035848290913894431124552144659850629965753252622341812835031128325856564939590222114743547726853551172031590459480315318255913212906894247328076158764307469896256330420089872953551641610873569 / 184470457714628443107414849205433468392952600188267502571948471817635458873395593011847771842260770492319868602460245224752884719193618248459863220936214179035371652098246071379214101690296144509401503085640797350016262881897482540453375191526222257548656749806678678541223966298343352552474603652954101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_32 : (1414213562373 / 250000000000 : ℝ) ≤ Real.sqrt 32 ∧ Real.sqrt 32 ≤ (5656854249493 / 1000000000000 : ℝ) := by
  constructor
  · calc (1414213562373 / 250000000000 : ℝ) = Real.sqrt ((1414213562373 / 250000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 32 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 32 ≤ Real.sqrt ((5656854249493 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (5656854249493 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_32 : (-11743925879 / 100000000000000 : ℝ) ≤ primeTerm 32 ∧ primeTerm 32 ≤ (-5871231881 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_32
  have hl := PsiOmega.Num.log_bound_32
  have hc := PsiOmega.Num.theta_32_cos
  have hs := PsiOmega.Num.theta_32_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_32
  have hqpos : (0 : ℝ) < Real.sqrt 32 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 32)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 32) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 32) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 32) = 2028 / 5 - 169 / 2 * Real.log 32 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (5025824095165074429116187860429680251151779387896349610810767857909073455255375207339298350271897417799251317995663841832697585281363295943035605436551777202069 / 7533477229335171854722291945010979959993708417983374358147371495693200822944614182410915926153514504570366750645825986129414410969868284025282578137500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 32) / 2 ∧ (2 * (12 / 5) - Real.log 32) / 2 ≤ (15077472293028459294291783130412488322527192292221155047947503915310509727339487237248812785092554682846939681006386422692408106048357482191558588591925985652593 / 22600431688005515564166875835032939879981125253950123074442114487079602468833842547232747778460543513711100251937477958388243232909604852075847734412500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-31854611907446667778921917368561956590474595053192026428641779098423709244546134371250969446330776013390065072263718099986094529305353771093203242167357679344372779130742967117974408169183654446309405220567323537128863738878887571852005347957742936971359476560900735400563309993377782850911085504790005768267310218818285603871217735945238494114055884197406824468395987824057794863975944750041181872938736954988763297200246454655093124762531 / 61490152571542814369138283068477822797650866729422500857316157272545152957798531003949257280753590164106622867486748408250961573064539416153287740312071393011790550699415357126404700563432048169800501028546932450005420960632494180151125063842074085849552249935559559513741322099447784184158201217651367187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 32) / 2 * Real.cos (169 / 2 * Real.log 32) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 32) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 32)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 32) / 2 * Real.cos (169 / 2 * Real.log 32) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 32) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 32)) / (2 * (169 / 2)) ≤ (-1327110826794050399805011324655197362165282708844117404137442993747245233929939425494155076130244299556927391495006020342123883033557059704686362459363358426108416820876641136736378151161003579987143805862627388701134914283802023489281852666283521544581181702389292552883853456713924488996745778449591296412742039020403465627641436759359741714702168392681670214221571980884707554699150868059219845304989047251040844428090608326360015814743 / 2562089690480950598714095127853242616568786113725937535721506553022714706574938791831219053364732923504442619478614517010456732211022475673053655846336308042157939612475639880266862523476335340408354209522788852083559206693020590839630210993419753577064677080648314979739221754143657674339925050735473632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_33 : (2872281323269 / 500000000000 : ℝ) ≤ Real.sqrt 33 ∧ Real.sqrt 33 ≤ (5744562646539 / 1000000000000 : ℝ) := by
  constructor
  · calc (2872281323269 / 500000000000 : ℝ) = Real.sqrt ((2872281323269 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 33 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 33 ≤ Real.sqrt ((5744562646539 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (5744562646539 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_33 : (-2361 / 100000000000000 : ℝ) ≤ primeTerm 33 ∧ primeTerm 33 ≤ (2019 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_33
  have hl := PsiOmega.Num.log_bound_33
  have hc := PsiOmega.Num.theta_33_cos
  have hs := PsiOmega.Num.theta_33_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_33
  have hqpos : (0 : ℝ) < Real.sqrt 33 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 33)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 33) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 33) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 33) = 2028 / 5 - 169 / 2 * Real.log 33 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (4909915300226325292893947740637843935976172165317330988675997861419691579814758032273209531230847589050221665284189633519584473577533264374141453289979958452069 / 7533477229335171854722291945010979959993708417983374358147371495693200822944614182410915926153514504570366750645825986129414410969868284025282578137500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 33) / 2 ∧ (2 * (12 / 5) - Real.log 33) / 2 ≤ (14729745908216823213917699566245469640598251408638143725889807329639210754282952763067927488463341813139981804417076764620111673580852188517391905828149185652593 / 22600431688005515564166875835032939879981125253950123074442114487079602468833842547232747778460543513711100251937477958388243232909604852075847734412500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (1208003607787481182095393711913267880774141727826731397928655828599988331258211158934949379600046739608984297359606014962225359305724825425584927585190723829845442141628969096105053791564826089530545614796395049561417528679576304309934675881096501372260058266705281037812621081368807413305370492596862957777831945171805315580729376779615165863472365186400766874447392893540031103843265946631739096584342077978051845848120775071779439749 / 1876530535020227489292550142470636682057216391889114406046025307389683622979691497923256142601122746707355434188438366951018114412369977299599845590578350616814897177106181552929830949811769048150650055802823866272138090839614690556369783442446108576951667783677965073051187808210686773198187293019145727157592773437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 33) / 2 * Real.cos (169 / 2 * Real.log 33) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 33) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 33)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 33) / 2 * Real.cos (169 / 2 * Real.log 33) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 33) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 33)) / (2 * (169 / 2)) ≤ (14497460514862297180552852867382669616261657039724418465910568295122274323388204456319779266474611764338489495372084283796896037372429475188549148654170858980002341229219445232270139542134568300908106984864419964471722082635109519951275699503000797955001239527717585028047559729033257252180361299765991248500346289437230438004553132248785877599842449030644131306279544708499777895940507380330098004579232680789467494115563644260322781321 / 22518366420242729871510601709647640184686596702669372872552303688676203475756297975079073711213472960488265210261260403412217372948439727595198147086940207401778766125274178635157971397741228577807800669633886395265657090075376286676437401309353302923420013404135580876614253698528241278378247516229748725891113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_34 : (1166190378969 / 200000000000 : ℝ) ≤ Real.sqrt 34 ∧ Real.sqrt 34 ≤ (2915475947423 / 500000000000 : ℝ) := by
  constructor
  · calc (1166190378969 / 200000000000 : ℝ) = Real.sqrt ((1166190378969 / 200000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 34 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 34 ≤ Real.sqrt ((2915475947423 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2915475947423 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_34 : (36753640565091 / 100000000000000 : ℝ) ≤ primeTerm 34 ∧ primeTerm 34 ≤ (18378862211069 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_34
  have hl := PsiOmega.Num.log_bound_34
  have hc := PsiOmega.Num.theta_34_cos
  have hs := PsiOmega.Num.theta_34_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_34
  have hqpos : (0 : ℝ) < Real.sqrt 34 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 34)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 34) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 34) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 34) = 2028 / 5 - 169 / 2 * Real.log 34 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (6477180634778458572685406912078269488137544175573085353461622023702872120721452183626702108606698360291250830847676899089066866155462664058068450458748931613267712996383 / 10171136750338212439220322867543187434661361297156604029514776262391532800250585278101255382766017868909118398244938128626356147458035390745541031513128048212500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 34) / 2 ∧ (2 * (12 / 5) - Real.log 34) / 2 ≤ (19431541914517448404902249075725377154975112206638656486002861396174462620846038125308962580935428966153914680328172537185280306662565014416212449434778885358669988952451 / 30513410251014637317660968602629562303984083891469812088544328787174598400751755834303766148298053606727355194734814385879068442374106172236623094539384144637500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-756468231163130262591085149509190151866110729475504537797312894776145265497749796877773406766325567746373733193432197609054178236466863751872746903647601941307459523380004328730319932436632342358410285224491364144180693565653933077501437506933777182922345273904877077425258314366756664513830140428921150823885305646817153071533263469892837532669747187371648953349502968465950151819668879335469718136369579725927573811750637245929278299 / 1345038896580767427824702552432739072940878383987450996084044217551696095554987765323035993430684232154702201246304145897492418777220136313716529488459166509248289490534083784079064108294898853588220972690197849758495205741140207233796169737929975203932307229153926492810680462995012589932206783169569873808940467834472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 34) / 2 * Real.cos (169 / 2 * Real.log 34) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 34) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 34)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 34) / 2 * Real.cos (169 / 2 * Real.log 34) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 34) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 34)) / (2 * (169 / 2)) ≤ (-63032015513947177983628137926096079355524512780482136241409894151053089197021156444361418713546931509950551223576463072020818567308730091800625541924714751824305393527925295417481321482014131760073402416752474106896581732457680231718649154432014020403711548234424645353236832818440581377986838827004262778981209164313013206196545799975798384903576700099025917499423372093641036703423848362062882263714680848610317353551209024360879365578663675139201403741351 / 112086574715063952318725212702728256078406531998954249673670351462641341296248980443586332785890352679558516770525345491457701564768344692809710790704930542437357457544506982006588675691241571132351747724183154146541267145095017269483014144827497933661025602429493874400890038582917715827683898597464156150745038986206054687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_35 : (5916079783099 / 1000000000000 : ℝ) ≤ Real.sqrt 35 ∧ Real.sqrt 35 ≤ (59160797831 / 10000000000 : ℝ) := by
  constructor
  · calc (5916079783099 / 1000000000000 : ℝ) = Real.sqrt ((5916079783099 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 35 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 35 ≤ Real.sqrt ((59160797831 / 10000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (59160797831 / 10000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_35 : (0 : ℝ) ≤ primeTerm 35 ∧ primeTerm 35 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_35
  have hl := PsiOmega.Num.log_bound_35
  have hc := PsiOmega.Num.theta_35_cos
  have hs := PsiOmega.Num.theta_35_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_35
  have hqpos : (0 : ℝ) < Real.sqrt 35 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 35)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 35) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 35) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 35) = 2028 / 5 - 169 / 2 * Real.log 35 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (6329762533980627325039973216102265526794565507729075315221327304673816102561074657729171039917150014739561651112811525203321829313482896052026595386179849972330212996383 / 10171136750338212439220322867543187434661361297156604029514776262391532800250585278101255382766017868909118398244938128626356147458035390745541031513128048212500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 35) / 2 ∧ (2 * (12 / 5) - Real.log 35) / 2 ≤ (18989287612128053288447401594415479637976726968274710087033307268623966269766295021230375710502561124808069654131579540573513029990154065155724864231335298511169988952451 / 30513410251014637317660968602629562303984083891469812088544328787174598400751755834303766148298053606727355194734814385879068442374106172236623094539384144637500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (1117016041948851156979127487381744789871920062941100723031376668560661528506885357888922695069878653671618795954991582788781434091287260546895238050373725352793983880055953778155578377608562611151284345855960711806699346727353195139734645742492593524016379720432883940076272013424302263296807264433663331242159134413431917247020722037756575792736753201248451044459631908145953980669291255258243064210422897266454863138382689505383593943610828899641025202531289033 / 4670273946460998013280217195947010669933605499956427069736264644276722554010374185149430532745431361648271532105222728810737565198681028867071282946038772601556560731021124250274528153801732130514656155174298089439219464378959052895125589367812413902542733434562244766703751607621571492820162441561006506281043291091918945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 35) / 2 * Real.cos (169 / 2 * Real.log 35) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 35) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 35)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 35) / 2 * Real.cos (169 / 2 * Real.log 35) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 35) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 35)) / (2 * (169 / 2)) ≤ (13407654728892668594936064613350456617600701795108503461491166514824375114250066522189223436087385635976466777186073660274550302984460126355401315967886361925035249266529746191757702936375049774172378699946055633282216097296398691196928319559870671078644481458754361615883838043804717119046239608067656168570515817704427138627076214157512587456953538950891949842896260307882247014621658609336601222894348457096592431779315321395438602870411 / 56043287357531976159362606351364128039203265999477124836835175731320670648124490221793166392945176339779258385262672745728850782384172346404855395352465271218678728772253491003294337845620785566175873862091577073270633572547508634741507072413748966830512801214746937200445019291458857913841949298732078075372519493103027343750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_36 : (6 : ℝ) ≤ Real.sqrt 36 ∧ Real.sqrt 36 ≤ (6000000000001 / 1000000000000 : ℝ) := by
  constructor
  · calc (6 : ℝ) = Real.sqrt ((6 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 36 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 36 ≤ Real.sqrt ((6000000000001 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (6000000000001 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_36 : (-173784402719 / 2000000000000 : ℝ) ≤ primeTerm 36 ∧ primeTerm 36 ≤ (-1737358780561 / 20000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_36
  have hl := PsiOmega.Num.log_bound_36
  have hc := PsiOmega.Num.theta_36_cos
  have hs := PsiOmega.Num.theta_36_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_36
  have hqpos : (0 : ℝ) < Real.sqrt 36 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 36)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 36) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 36) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 36) = 2028 / 5 - 169 / 2 * Real.log 36 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (11161860573224646470881534497790538275903925494217850645207903502151809253058541546325754616440091109891292195500213730293527228566741290811196951602850128903468270772312115437433 / 18351063457994962059714610073317904029710422797945377833535429620804880932091326113678782511533189004476301765647624258846685073423071492779858901430801566406335585087500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 36) / 2 ∧ (2 * (12 / 5) - Real.log 36) / 2 ≤ (33485581738058182918529941402867798847408225893428092539382350049458199066931553865027057751897913157719550615243003648645588507417248512225691080411333051089845616640857837589301 / 55053190373984886179143830219953712089131268393836133500606288862414642796273978341036347534599567013428905296942872776540055220269214478339576704292404699219006755262500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (402164689148651619160677632022968960753120822566234486598664193105851188651968945056816383661639539123684416916909362857334167630367622656608279521351101636183601829812090592511423838728324455614196254692188064723030112578525922994805715554756430083104158817230878637064921567418142860296840398542437228735684094068855345236567361731462068010534001812973577174482531658567148784734256697559502443617475984728584423882433180081473517330165881096063856470047428524704060187278497 / 1855820208211258663494175261598587929256148400841070387251047082669557519689674261289303415094083557476596597204414795372446901562450664278022143829163980607335225603914261920157201466820551949262109202812910484315649999676384958720772252038216784082370824329447881707159694437959838980417145809389685898996352810782428667748073494294658303260803222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 36) / 2 * Real.cos (169 / 2 * Real.log 36) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 36) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 36)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 36) / 2 * Real.cos (169 / 2 * Real.log 36) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 36) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 36)) / (2 * (169 / 2)) ≤ (19309296668980894870851894848104621963604583976277687574695463597370213678143162551338228277034809632803901561058344299177489966726014129517952596939998812535785356560079020543083754664184744587691975441381286648634844027470434994047634513415811345852336084229314525957595400421613028081465923916533988396110909666390947828286633588605450107117670331616201310343788030274921173105355623214022489997106531286573545977927428822383411072289587520246433918139993692536627 / 89079369994140415847720412556732220604295123240371378588050259968138760945104364541886563924516010758876636665811910177877451274997631885345062903799871069152090828987884572167545670407386493564581241735019703247151199984466478018597068097834405635953799567813498321943665333022072271060022998850704923151824934917556576051907527726143598556518554687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_37 : (3041381265149 / 500000000000 : ℝ) ≤ Real.sqrt 37 ∧ Real.sqrt 37 ≤ (6082762530299 / 1000000000000 : ℝ) := by
  constructor
  · calc (3041381265149 / 500000000000 : ℝ) = Real.sqrt ((3041381265149 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 37 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 37 ≤ Real.sqrt ((6082762530299 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (6082762530299 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_37 : (-1857290897233 / 20000000000000 : ℝ) ≤ primeTerm 37 ∧ primeTerm 37 ≤ (-928544941391 / 10000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_37
  have hl := PsiOmega.Num.log_bound_37
  have hc := PsiOmega.Num.theta_37_cos
  have hs := PsiOmega.Num.theta_37_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_37
  have hqpos : (0 : ℝ) < Real.sqrt 37 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 37)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 37) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 37) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 37) = 2028 / 5 - 169 / 2 * Real.log 37 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (22618165555412897184910940032724681902113959932783462446349280773827267468401585606992643836522106696884772180847795299756120361941927494901529487911096553252248048212147107935735371140769 / 38043068356109704583107127830066994102292905518440141552354181905941360456065890247966572751484649001879771032059833098952741767930488782490030091104381782536877396669930669387500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 37) / 2 ∧ (2 * (12 / 5) - Real.log 37) / 2 ≤ (67854496704360877331579565723004627245147054789039638668224691005457763616843991980047763752343417793422206495299293196083748875902687135678188884971730794758394453791023690655287503826493 / 114129205068329113749321383490200982306878716555320424657062545717824081368197670743899718254453947005639313096179499296858225303791466347470090273313145347610632190009792008162500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-863494686214573626014732647388774200777054992349817507620324559482432088134188198454537489694941339388719101068504508003587248506313071554635916709583354049585074150273631097004718878849690304914995445254459180441643700873044905171096203296477647760756283520686535209244652234909604252147251074098572811524010819397378578093850231934597651355920529588581191879312394500567857478860722689853794585282157514438595500156026730254211570157809749505931879018862275659026924376855481696519817897131061 / 1568070866454683246294805506146520410412111094691698476570637504493713147866150869860983170198684823964921129992256138485350175527180026402579641478434316959794876956377563596779667078174615196061025639202667964839785722293579362000828719083517428265547761638884690082944346390444747617714402432327300348117297506358717432134265853325222420037259931564331054687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 37) / 2 * Real.cos (169 / 2 * Real.log 37) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 37) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 37)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 37) / 2 * Real.cos (169 / 2 * Real.log 37) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 37) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 37)) / (2 * (169 / 2)) ≤ (-35975051267124583492846551879742188719079748978584714080536171693475981866039912205770576518296303551556371122651702181602435225656378982117177103920476796783198015726095346872534174773008500631137675901110464027806382212846920117910808870149099607281766723431803902981114153758661130918231973680156912611372110109032654238241130028726532607380792735144592380062510911313027570435597475034246423547030958869322641809765453784912519595311066468770090226438120321453410416669773623794472290518703 / 65336286102278468595616896089438350433837962278820769857109896020571381161089619577540965424945200998538380416344005770222923980299167766774151728268096539991453206515731816532486128257275633169209401633444498534991071762232473416701196628479892844397823401620195420122681099601864484071433434680304181171554062764946559672261077221884267501552497148513793945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_38 : (770551750371 / 125000000000 : ℝ) ≤ Real.sqrt 38 ∧ Real.sqrt 38 ≤ (6164414002969 / 1000000000000 : ℝ) := by
  constructor
  · calc (770551750371 / 125000000000 : ℝ) = Real.sqrt ((770551750371 / 125000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 38 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 38 ≤ Real.sqrt ((6164414002969 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (6164414002969 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_38 : (-889 / 50000000000000 : ℝ) ≤ primeTerm 38 ∧ primeTerm 38 ≤ (1677 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_38
  have hl := PsiOmega.Num.log_bound_38
  have hc := PsiOmega.Num.theta_38_cos
  have hs := PsiOmega.Num.theta_38_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_38
  have hqpos : (0 : ℝ) < Real.sqrt 38 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 38)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 38) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 38) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 38) = 2028 / 5 - 169 / 2 * Real.log 38 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (22110894582068310633830813789285571196840176506448928760551077874013687700637729659913286901162810883861811101452809096762431394958708845672126146637653633146227509430729786863620979108769 / 38043068356109704583107127830066994102292905518440141552354181905941360456065890247966572751484649001879771032059833098952741767930488782490030091104381782536877396669930669387500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 38) / 2 ∧ (2 * (12 / 5) - Real.log 38) / 2 ≤ (66332683784335669234719395345226918458553614130612918863848645321872706900145965915917285510675097327136966611121395350835017220087052842883987084399489988801117061790702887207087472850493 / 114129205068329113749321383490200982306878716555320424657062545717824081368197670743899718254453947005639313096179499296858225303791466347470090273313145347610632190009792008162500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (96785713535439524811648423960869475435807544893420800315527531240264842232486233250275761418058981853991531561329160455400631894377728810346519662952534019846775382468076033780496980810561807153301662430839243088034953131617115618363500487923407859963035347793799331008543089776288425314019929974111250277964891974098281428347187627147480452621951327538089590452160977949613649027890513294587219852443568310496396035138408042265233388011943516273534289030161578842077727266227446543706013749 / 191414900690268950963721375262026417286634655113732724190751648497767718245379744856077047143394143550405411376007829404949972598532718066721147641410439082006210565964058056247517953878737206550418168847981929301731655553415449462991786997499686067571748246934166269890667283989837355678027640664953655776037293256679374039827374673489064945954581489786505699157714843750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 38) / 2 * Real.cos (169 / 2 * Real.log 38) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 38) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 38)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 38) / 2 * Real.cos (169 / 2 * Real.log 38) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 38) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 38)) / (2 * (169 / 2)) ≤ (4646259538891568144252964483658583371861479764132554836133978429127046469645901497888425267797787022737021936008395785141274417727287042849217330798450797941617651446273417764039144688766290558416897034523973070762578145247801799744040646374433340137769339002857104451174905198393200065496379496603119700059226937722875228836095857219421037324111135108141762425081519338745461044195608551352063679038303978940369092512339189849183701955476176791645609394926947828986961 / 9187915233132909646258626012577268029758463445459170761156079127892850475778227753091698262882918890419459746048375811437598684729570467202615086787701075936298107166274786699880861786179385914420072104703132606483119466563941574223605775879984931243443915852839980954752029631512193072545326751917775477249790076320609953911713984327475117405819911509752273559570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_39 : (3122498999199 / 500000000000 : ℝ) ≤ Real.sqrt 39 ∧ Real.sqrt 39 ≤ (6244997998399 / 1000000000000 : ℝ) := by
  constructor
  · calc (3122498999199 / 500000000000 : ℝ) = Real.sqrt ((3122498999199 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 39 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 39 ≤ Real.sqrt ((6244997998399 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (6244997998399 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_39 : (4090357669899 / 100000000000000 : ℝ) ≤ primeTerm 39 ∧ primeTerm 39 ≤ (511752446307 / 12500000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_39
  have hl := PsiOmega.Num.log_bound_39
  have hc := PsiOmega.Num.theta_39_cos
  have hs := PsiOmega.Num.theta_39_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_39
  have hqpos : (0 : ℝ) < Real.sqrt 39 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 39)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 39) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 39) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 39) = 2028 / 5 - 169 / 2 * Real.log 39 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (21616800979655056706717457122641295467336570175528696837287303747466504043033571192734253390244284326475627332098462724536553405947535665112995567856281887751247420297188102757683479108769 / 38043068356109704583107127830066994102292905518440141552354181905941360456065890247966572751484649001879771032059833098952741767930488782490030091104381782536877396669930669387500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 39) / 2 ∧ (2 * (12 / 5) - Real.log 39) / 2 ≤ (64850402977103020161242549844378607044958248144026379300779051277200576128170803544643061432128794813413561678848420404451705757743139769437909210620244864903440304375152038434587472850493 / 114129205068329113749321383490200982306878716555320424657062545717824081368197670743899718254453947005639313096179499296858225303791466347470090273313145347610632190009792008162500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-74165203457576045313040523597099984960019295571077491744543253562802431185887270241920767486952595394168156121220668189538372962864728109689999793656182522142453622755092229050640876646203382427051636662816020587626856029634540521440347329486282807987567243258486166147384471880973066182215933279602520377559250485314678941508386467219517388895963044076277746636331253014209589831144617114564513351172189605598250929957529227847948459667252342581298161075252536202937763371 / 1148489404141613705782328251572158503719807930682396345144509890986606309472278469136462282860364861302432468256046976429699835591196308400326885848462634492037263395784348337485107723272423239302509013087891575810389933320492696777950721984998116405430489481604997619344003703939024134068165843989721934656223759540076244238964248040934389675727488938719034194946289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 39) / 2 * Real.cos (169 / 2 * Real.log 39) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 39) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 39)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 39) / 2 * Real.cos (169 / 2 * Real.log 39) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 39) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 39)) / (2 * (169 / 2)) ≤ (-1543726381643091106037158935542398775415954011670283257142148785130571002581700245041646931883832386195942027923586137273286221694102518359378184990332710739139809944510447854739277248661012043811086900022935512738106687653585036309255461830686538274025237284768525767680135746138106492184865186478154068420744104740251145873697315078482901199681244394940159302017943546335415025358085709612942437666564918731042067552566468756033583377084579479690717930443103434357904720003613160000433153278097 / 23926862586283618870465171907753302160829331889216590523843956062220964780672468107009630892924267943800676422000978675618746574816589758340143455176304885250776320745507257030939744234842150818802271105997741162716456944176931182873973374687460758446468530866770783736333410498729669459753455083119206972004661657084921754978421834186133118244322686223313212394714355468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_40 : (395284707521 / 62500000000 : ℝ) ≤ Real.sqrt 40 ∧ Real.sqrt 40 ≤ (6324555320337 / 1000000000000 : ℝ) := by
  constructor
  · calc (395284707521 / 62500000000 : ℝ) = Real.sqrt ((395284707521 / 62500000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 40 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 40 ≤ Real.sqrt ((6324555320337 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (6324555320337 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_40 : (0 : ℝ) ≤ primeTerm 40 ∧ primeTerm 40 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_40
  have hl := PsiOmega.Num.log_bound_40
  have hc := PsiOmega.Num.theta_40_cos
  have hs := PsiOmega.Num.theta_40_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_40
  have hqpos : (0 : ℝ) < Real.sqrt 40 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 40)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 40) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 40) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 40) = 2028 / 5 - 169 / 2 * Real.log 40 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (823218430842027055738828597223910151884347445555079393559264435589209572909464409107178225138566688862939292399970059618272006259034245368497431618721284320370922006374885665597879961851485360289 / 1481780593959009838398093860658463655710830955668590507115661125925150371013963366495408093962719948879786233960184096050690307032975740447578053740953049884735760087362929837027345387500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 40) / 2 ∧ (2 * (12 / 5) - Real.log 40) / 2 ≤ (2469655294011785033668999902358192302191295903810144159935807960329391396772624082679354662792827427336046103324332771693087948655654760628085876186397309287778232193114195340667003051612003239933 / 4445341781877029515194281581975390967132492867005771521346983377775451113041890099486224281888159846639358701880552288152070921098927221342734161222859149654207280262088789511082036162500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-226946088556067130970611984277604210789881316184841348445538739573059050136961345358494423558580632339883078482689633268810843831758586035971143090419935758657639439842239689544966726916845388764600092462320327725976315859312950983295566809320234452601326895501936832433400160295836546404556045626236038828930397667732674839061701190626325452164455637822891055789457588671825825756681538034426854977399772188121776984823182488574862131462677049912442953852473327068993165308827191477308926196821 / 528229488162826764657296095331252535352507482674827064903942981695448956815526680459837065937648013049862353529550763388513342700613901183959610092020994930524801942657323363912781874650852946870061327536816702168776208789399788305961961358075736134356668855722168798112193164756609153150771534272491816779513028170558247541514969207880683472565078224821232061882651510854522203253225143271265551447868347167968750000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 40) / 2 * Real.cos (169 / 2 * Real.log 40) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 40) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 40)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 40) / 2 * Real.cos (169 / 2 * Real.log 40) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 40) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 40)) / (2 * (169 / 2)) ≤ (-151277214713292152393260854663886159667389446528507138325640095683275504102760733437465569708140174060633817301567448400420540500199133200334299122565577216696196152187777951491964395851301831254762343543133926671660679510656235054071105185328423444163271729635386004914375418752584559431952010527312442377530443308450008639509165085770898574690810248127607952432751294466119086223018177395185161974916790463030155758132224701356686412462370607620662008972000568122311277089867212070883708921583 / 352152992108551176438197396887501690235004988449884709935961987796965971210351120306558043958432008699908235686367175592342228467075934122639740061347329953683201295104882242608521249767235297913374218357877801445850805859599858870641307572050490756237779237148112532074795443171072768767181022848327877853008685447038831694343312805253788981710052149880821374588434340569681468835483428847510367631912231445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_41 : (800390529679 / 125000000000 : ℝ) ≤ Real.sqrt 41 ∧ Real.sqrt 41 ≤ (6403124237433 / 1000000000000 : ℝ) := by
  constructor
  · calc (800390529679 / 125000000000 : ℝ) = Real.sqrt ((800390529679 / 125000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 41 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 41 ≤ Real.sqrt ((6403124237433 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (6403124237433 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_41 : (7309022394839 / 25000000000000 : ℝ) ≤ primeTerm 41 ∧ primeTerm 41 ≤ (29239365317691 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_41
  have hl := PsiOmega.Num.log_bound_41
  have hc := PsiOmega.Num.theta_41_cos
  have hs := PsiOmega.Num.theta_41_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_41
  have hqpos : (0 : ℝ) < Real.sqrt 41 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 41)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 41) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 41) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 41) = 2028 / 5 - 169 / 2 * Real.log 41 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (268307971255563774760417638026983862425074685120507610576644836724848404710956013276728959272390757379452713488070192299576130038049009426692103549955096913861070297796409771638196272101536786763 / 493926864653003279466031286886154551903610318556196835705220375308383457004654455498469364654239982959928744653394698683563435677658580149192684580317683294911920029120976612342448462500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 41) / 2 ∧ (2 * (12 / 5) - Real.log 41) / 2 ≤ (2414771742785972185572491186507880288476629780790257944982926327377293847458467864608310431264038298769302859119906533405015932951384331585844545004221109321752850472997244456122853269112003239933 / 4445341781877029515194281581975390967132492867005771521346983377775451113041890099486224281888159846639358701880552288152070921098927221342734161222859149654207280262088789511082036162500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (199871338960179141337714942494369109171556668556293341113288874931022609548872768010855585746338135376809286323071518905512207702868126931363495351298388620922214912017870803998704919229590275087713614032865771876935068988882174582501822762016063430102063965739716923067891097900741265195985036267571311837738496412158240461295662730101343858430576928312242581287772357693054442757109210157367677226428984286832269989846593396292925997444678565780233685579046023679935604267793372962142273084229347 / 396489021009369074170431690460142488965367458637837124015332521905257168076363687105299295273535631735047677666658125667893064317233096243383667721090581357655633246830018985180459564707695353364416904260917128376958510972856319736707785836103996921293457279737914099863125348662531607780710870219593352128431390510018179149136605136778176929865352121730365679593086242675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 41) / 2 * Real.cos (169 / 2 * Real.log 41) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 41) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 41)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 41) / 2 * Real.cos (169 / 2 * Real.log 41) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 41) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 41)) / (2 * (169 / 2)) ≤ (719617440154460179960846747226936884204443562462850077115540529786270675036295994535424425197316115729860600474529610325080943424904883376784798366583249424894946777060378996159863680667888517180693103665327174110033994959900490801036756993735768081767298453300733246034808469591311529987351700501943061978479584413678115391977753110557743993680223095974153132194236853410106840141041484983074339760986925184307636326484140855606546695067134797651352675852349427161537776695381 / 1427360475633728667013554085656512960275322851096213646455197078858925805074909273579077462984728274246171639599969252404415031542039146476181203795926092887560279688588068346649654432947703272111900855339301662157050639502282751052148029009974388916656446207056490759507251255185113788010559132790536067662353005836065444936891778492401436947515267638229316446535110473632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_42 : (6480740698407 / 1000000000000 : ℝ) ≤ Real.sqrt 42 ∧ Real.sqrt 42 ≤ (810092587301 / 125000000000 : ℝ) := by
  constructor
  · calc (6480740698407 / 1000000000000 : ℝ) = Real.sqrt ((6480740698407 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 42 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 42 ≤ Real.sqrt ((810092587301 / 125000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (810092587301 / 125000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_42 : (432432736117 / 25000000000000 : ℝ) ≤ primeTerm 42 ∧ primeTerm 42 ≤ (86584889577 / 5000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_42
  have hl := PsiOmega.Num.log_bound_42
  have hc := PsiOmega.Num.theta_42_cos
  have hs := PsiOmega.Num.theta_42_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_42
  have hqpos : (0 : ℝ) < Real.sqrt 42 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 42)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 42) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 42) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 42) = 2028 / 5 - 169 / 2 * Real.log 42 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (1033433929603735052651349319504716783365690688864053877218775749743167863374797444954544106787235882021598346781390006276344465245700127176558385714097748741036512251851796990842101129319232919256581408609 / 1945597994537740009828984576954155693927774063227036415350856625611436095770176940379505651663438935154786765573690666035294969203013394285342988200150752350260208099873270439869359927920361387500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 42) / 2 ∧ (2 * (12 / 5) - Real.log 42) / 2 ≤ (9300905372287274299984833786224595384918132580843484315707503431030859261734201728611407090498457781504379584166186999210841310533847930014247389776730300444721748031530048140914579715025282398743767596919 / 17510381950839660088460861192587401245349966569043327738157709630502924861931592463415550864970950416393080890163215994317654722827120548568086893801356771152341872898859433958824239351283252487500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-2707545286351356158421047212281046785730468322003980927263340857697464757922357651490083968839401525227960486530397636481187073360381471722815407289258930693103556373152454748213265273202173303952247125232292673244762494609695316329059546339927173683152689847410864116203181966631374839976954028863110558703350333540603388270169433383984027270800742513415936392292446863331104551714725518329481564784910707846694867202196890086861357062766228918174526933015863136157108485153339719933921490053472381957850441903 / 55367459822306677501600992467833734161779097098792485591592408589352121741943151926377471486157123813001516716714588578245352652373959739402815048419920243004340844908426637781718828625848131867058365248744884387160005743421424999134992376542316257190632532594748859150012422653227175138607142754990970788903672229932088868437911628199400555395088265185740848896957116484783682138104438781738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 42) / 2 * Real.cos (169 / 2 * Real.log 42) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 42) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 42)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 42) / 2 * Real.cos (169 / 2 * Real.log 42) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 42) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 42)) / (2 * (169 / 2)) ≤ (-75124168926013981471460127161391190971188602449225363857969452826047754133859670399971028654730660420805358643201881763719655365215641582990603207584990586673346243574580755447872417660007481735329901564369448138233024199958692318805150208545652368784959237879158241799006372261316119644517449385962829048372932855421507832799850628324681941783613082348070539417655342412112545373032725669838308388054520050552979723496435454484610872851182117398249072670919238151239844443126010863140842675821653744993350196618164227781867453597783 / 1537984995064074375044472012995381504493863808299791266433122460815336715053976442399374207948808994805597686575405238284593129232609992761189306900553340083453912358567406605047745239606892551862732368020691232976666826206150694420416454903953229366406459238743023865278122851478532642739087298749749188580657561942558024123275323005538904316530229588492801358248808791243991170502901077270507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_43 : (3278719262151 / 500000000000 : ℝ) ≤ Real.sqrt 43 ∧ Real.sqrt 43 ≤ (6557438524303 / 1000000000000 : ℝ) := by
  constructor
  · calc (3278719262151 / 500000000000 : ℝ) = Real.sqrt ((3278719262151 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 43 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 43 ≤ Real.sqrt ((6557438524303 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (6557438524303 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_43 : (3679752410397 / 50000000000000 : ℝ) ≤ primeTerm 43 ∧ primeTerm 43 ≤ (7360394595537 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_43
  have hl := PsiOmega.Num.log_bound_43
  have hc := PsiOmega.Num.theta_43_cos
  have hs := PsiOmega.Num.theta_43_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_43
  have hqpos : (0 : ℝ) < Real.sqrt 43 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 43)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 43) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 43) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 43) = 2028 / 5 - 169 / 2 * Real.log 43 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (1010543485317808444678101596275550676666669461659614195036477557286160801512672205511934294852250537223165979978442821380914771097789427425403667664965226691996784820443333510545015677090054471537681408609 / 1945597994537740009828984576954155693927774063227036415350856625611436095770176940379505651663438935154786765573690666035294969203013394285342988200150752350260208099873270439869359927920361387500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 43) / 2 ∧ (2 * (12 / 5) - Real.log 43) / 2 ≤ (9094891373714481118229125755745653253258351578738403340407114827112650868387811803472279393365265535442904124274361562775209826191914142717900282047740450603795454840152051382603167674082485285858167596919 / 17510381950839660088460861192587401245349966569043327738157709630502924861931592463415550864970950416393080890163215994317654722827120548568086893801356771152341872898859433958824239351283252487500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-5557913361424193670368912615095678045442324379964491285551399116827647035742507770343499377866206487490313610406289683418965706985668489439639845578936161548989606563635643233267316801586020051770635577084630081300201742336923800339486685117293131790791155088055829770652710565261870431194119188456829752615174962725247518404256806875155299922309997026030957020454150078685056930090524589382180286489748288508737952810052836925220273869403315280444405037276859762212337150558443660889400259319769916062396195999687912321206623771 / 12303879960512595000355776103963052035950910466398330131464979686522693720431811539194993663590471958444781492603241906276745033860879942089514455204426720667631298868539252840381961916855140414901858944165529863813334609649205555363331639231625834931251673909944190922224982811828261141912698389997993508645260495540464192986202584044311234532241836707942410865990470329951929364023208618164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 43) / 2 * Real.cos (169 / 2 * Real.log 43) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 43) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 43)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 43) / 2 * Real.cos (169 / 2 * Real.log 43) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 43) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 43)) / (2 * (169 / 2)) ≤ (-77183909498712979840086896474516978521122182274803289487940058453623401582390360459813943577266819730880954793849298126848921313936004573897719168187318094449428567960779732199170181305231196804018129118320807313137077645797280646877136600155100675613818928919262717537423901566804430121597188547497641309668854476810526231287303823437751768392659920813183016564065211187810223533805142669031450857790285630289713605116834474676362147075478505377853534679317937661087941027067672509036687649989804477677881242208751026181375903 / 170887221673786041671608001443931278277095978699976807381458051201704079450441826933263800883200999422844187397267248698288125470289999195687700766728148898161545817618600733894193915511876950206970263113410136997407425134016743824490717211550358818489606582082558207253124761275392515859898588749972132064517506882506447124808369222837656035170025509832533484249867643471554574500322341918945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_44 : (663324958071 / 100000000000 : ℝ) ≤ Real.sqrt 44 ∧ Real.sqrt 44 ≤ (6633249580711 / 1000000000000 : ℝ) := by
  constructor
  · calc (663324958071 / 100000000000 : ℝ) = Real.sqrt ((663324958071 / 100000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 44 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 44 ≤ Real.sqrt ((6633249580711 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (6633249580711 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_44 : (-1181 / 25000000000000 : ℝ) ≤ primeTerm 44 ∧ primeTerm 44 ≤ (4117 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_44
  have hl := PsiOmega.Num.log_bound_44
  have hc := PsiOmega.Num.theta_44_cos
  have hs := PsiOmega.Num.theta_44_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_44
  have hqpos : (0 : ℝ) < Real.sqrt 44 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 44)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 44) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 44) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 44) = 2028 / 5 - 169 / 2 * Real.log 44 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (988179305041082887388252487236182577910198013405527483914198425529810897140131543727801515032908103575134899715436556298151809631680192777771435325563194680594673594290557645293479222466983200756431408609 / 1945597994537740009828984576954155693927774063227036415350856625611436095770176940379505651663438935154786765573690666035294969203013394285342988200150752350260208099873270439869359927920361387500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 44) / 2 ∧ (2 * (12 / 5) - Real.log 44) / 2 ≤ (8893613751224415316619306451059619369952292308595465848159054244335461965345638486373677548329295014633242466492182526097299235538474178086772241725503119910935890031422759103877177708075317293358167596919 / 17510381950839660088460861192587401245349966569043327738157709630502924861931592463415550864970950416393080890163215994317654722827120548568086893801356771152341872898859433958824239351283252487500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (533705555165042948322927658630000868602159054642732145154798381587196567527700463994247187730364532924634118591705335512963487931170493742171051802117527137475623551989737458008589100058222642212486282655446349958387062547106613247411256515829667269011182850738354726744309165858798979890387872966388895180194896766937820411599565770284791847592978631725726326450344177607073469802019236007189884617591773460771973755141020076646181741967738025302033093038499658122357875249980157567825534274322540298665351274001208011800076417 / 1367097773390288333372864011551450226216767829599814459051664409613632635603534615466110407065607995382753499178137989586305003762319993565501606133825191185292366540948805871153551324095015601655762104907281095979259401072133950595925737692402870547916852656660465658024998090203140126879188709999777056516140055060051576998466953782701248281360204078660267873998941147772436596002578735351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 44) / 2 * Real.cos (169 / 2 * Real.log 44) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 44) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 44)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 44) / 2 * Real.cos (169 / 2 * Real.log 44) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 44) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 44)) / (2 * (169 / 2)) ≤ (19216046268990038327305079580708831772722034199447813411185239234841625736629824466408198826467223748661250704245601134134918703788259918358276173091254598685825294416146420104930977520942530319791344477576954444171335123390857232366816442923450993983786415849553436356425473570154223796390628817108241762084021136749459710607503250042057065585191416097365879327032209046920523342768841138130478679619985047523829530796439925452087098781337915815378711314847486745143928466215686421506942521325755055884351 / 49215519842050380001423104415852208143803641865593320525859918746090774881727246156779974654361887833779125970412967625106980135443519768358057820817706882670525195474157011361527847667420561659607435776662119455253338438596822221453326556926503339725006695639776763688899931247313044567650793559991974034581041982161856771944810336177244938128967346831769643463961881319807717456092834472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_45 : (6708203932499 / 1000000000000 : ℝ) ≤ Real.sqrt 45 ∧ Real.sqrt 45 ≤ (2683281573 / 400000000 : ℝ) := by
  constructor
  · calc (6708203932499 / 1000000000000 : ℝ) = Real.sqrt ((6708203932499 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 45 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 45 ≤ Real.sqrt ((2683281573 / 400000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2683281573 / 400000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_45 : (0 : ℝ) ≤ primeTerm 45 ∧ primeTerm 45 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_45
  have hl := PsiOmega.Num.log_bound_45
  have hc := PsiOmega.Num.theta_45_cos
  have hs := PsiOmega.Num.theta_45_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_45
  have hqpos : (0 : ℝ) < Real.sqrt 45 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 45)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 45) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 45) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 45) = 2028 / 5 - 169 / 2 * Real.log 45 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (5395975669941905163521012792902050064565413449828516047454016517929550488157950947091590459449509020463425989222767158847534513814266850354610710857294861482498812214702981853621972940567282099232188066482216396441 / 10864334865353917488990894201016120742494538681300056127407039590489795133045125476328088180120128753685585315881915269477492240280250943632632115464947311885929472648803671502284885631085652925364125487500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 45) / 2 ∧ (2 * (12 / 5) - Real.log 45) / 2 ≤ (48563781062172178972156286668000583062506841758440617601704886664302419319819690681818636952233677509653359666104096186591839770836801822620925653199335649412420060195586105788790642806845426607010904563401165237631 / 97779013788185257400918047809145086682450848131700505146663356314408156197406129286952793621081158783170267842937237425297430162522258492693689039184525806973365253839233043520563970679770876328277129387500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (932392814161951337806158621606805640742933625972619244708418705432501970855137101932778221435130516901859025365581558773241721349393205463671804362568890923985429467549685193267087306671324822995328754054510624392522002980833739423018931614486696417633282959453286693484812078192776663986464802996235677923080639906355069861290156769649280803681234248438531990237277581621489663839386800375855184071387407124532150592089558330160713997369190155464230161561923020286480178293923442227752836400370450282936853706843766294060073029285162800606360854926121 / 5328557485842043383675267537145902994254879185317123995087167710605979013500946107559938798401396010836296218056341327515820638067668748931993759795252347021291128573174426442955841094362370764745980358053662680077511407188003830411932080293544085704126663715983673042957100884160202669437372490405947658564051621335389032909904239890510627734167167289843452692745763622814853923850547125796673369418382644653320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 45) / 2 * Real.cos (169 / 2 * Real.log 45) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 45) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 45)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 45) / 2 * Real.cos (169 / 2 * Real.log 45) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 45) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 45)) / (2 * (169 / 2)) ≤ (67152557916932734061665170933762213961602581429624168331239943119477815789164257955805515813404543754273900715838642778346821877721387356219155568023074286597782666212921596969540635916412731157042897873363868562760143461191349068706479637455839043068699183245971541768021967276228665476109427635582710913102628443929818176095881224479822107997228575156251152091145722634927364858418285118195957541506057361092515181072075987252025588840578579352852887279970037523979546622771166840786228337608105772794518206600223281228420573524263547471929 / 383656138980627123624619262674505015586351301342832927646276075163630488972068119744315593484900512780213327700056575581139085940872149923103550705258168985532961257268558703892820558794090695061710585779863712965580821317536275789659109781135174170697119787550824459092911263659534592199490819309228231416611716736148010369513105272116765196860036044868728593877694980842669482517239393057360482598123550415039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_46 : (10851727973 / 1600000000 : ℝ) ≤ Real.sqrt 46 ∧ Real.sqrt 46 ≤ (3391164991563 / 500000000000 : ℝ) := by
  constructor
  · calc (10851727973 / 1600000000 : ℝ) = Real.sqrt ((10851727973 / 1600000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 46 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 46 ≤ Real.sqrt ((3391164991563 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (3391164991563 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_46 : (-14715239658361 / 50000000000000 : ℝ) ≤ primeTerm 46 ∧ primeTerm 46 ≤ (-29427299640341 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_46
  have hl := PsiOmega.Num.log_bound_46
  have hc := PsiOmega.Num.theta_46_cos
  have hs := PsiOmega.Num.theta_46_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_46
  have hqpos : (0 : ℝ) < Real.sqrt 46 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 46)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 46) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 46) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 46) = 2028 / 5 - 169 / 2 * Real.log 46 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (5276582568658149265904648848251776441245512135263582418891297783441705537296485380757371318573849448128824958941914005151268027635297889966532687798639329787125410303860841805883361939753219116691021060544716396441 / 10864334865353917488990894201016120742494538681300056127407039590489795133045125476328088180120128753685585315881915269477492240280250943632632115464947311885929472648803671502284885631085652925364125487500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 46) / 2 ∧ (2 * (12 / 5) - Real.log 46) / 2 ≤ (47489243150620268273629652871731983570466458176706614045523784874165348887327133000506463165708668785392759370095557891038577766098065671808006116175538726977299434890903773130733519115430485981065699960901165237631 / 97779013788185257400918047809145086682450848131700505146663356314408156197406129286952793621081158783170267842937237425297430162522258492693689039184525806973365253839233043520563970679770876328277129387500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-6663013581046299243442320023139617357830981066655219838333928801637700371231172920062905135328323719038529209176800886359691255099672619095054866125607837799923716520323937095802826994043703309011102746545947877412662365735569272285759483118688346240885579225232592122664937881636176991496610014625493817841544848399564922561427302208982239258689118179559301337797265020588693744310639055174982895886563538553060675158556026182328066584862684890198468219971850721764496586654858067241867508969687021049959254350055154533706537 / 13811621003302576450486293456282180561108646848341985395265938705890697602994452310795361365456418460087679797202036720921007093871397397231727825389294083479186605261668113340141540116587265022221581088075093666760909567431305928427727952120866270145096312351829680527344805491743245319181669495132216330998021802501328373302471789796203547086961297615274229379597019310336101370620618150064977373532447814941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 46) / 2 * Real.cos (169 / 2 * Real.log 46) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 46) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 46)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 46) / 2 * Real.cos (169 / 2 * Real.log 46) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 46) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 46)) / (2 * (169 / 2)) ≤ (-185063714127038034630283831657757469154605270158412077306459028808025559439923840235323197240246568649454448542256713689141736702539637485169091327984535063223917383208538290378971116608033690330561937464853306152909149173668768458479390543779637732251367017063883960531862533751546830680374679998768151782544306472288863935485168620704599755060123419500225743407465078255049766988846422504199057522694081416515004125884805339503637448857421575583748089403546288226524698091181344368795633009933008370860803632516737575253420636313776759261042511959 / 383656138980627123624619262674505015586351301342832927646276075163630488972068119744315593484900512780213327700056575581139085940872149923103550705258168985532961257268558703892820558794090695061710585779863712965580821317536275789659109781135174170697119787550824459092911263659534592199490819309228231416611716736148010369513105272116765196860036044868728593877694980842669482517239393057360482598123550415039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_47 : (6855654600401 / 1000000000000 : ℝ) ≤ Real.sqrt 47 ∧ Real.sqrt 47 ≤ (3427827300201 / 500000000000 : ℝ) := by
  constructor
  · calc (6855654600401 / 1000000000000 : ℝ) = Real.sqrt ((6855654600401 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 47 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 47 ≤ Real.sqrt ((3427827300201 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (3427827300201 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_47 : (320628748087 / 25000000000000 : ℝ) ≤ primeTerm 47 ∧ primeTerm 47 ≤ (641666193297 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_47
  have hl := PsiOmega.Num.log_bound_47
  have hc := PsiOmega.Num.theta_47_cos
  have hs := PsiOmega.Num.theta_47_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_47
  have hqpos : (0 : ℝ) < Real.sqrt 47 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 47)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 47) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 47) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 47) = 2028 / 5 - 169 / 2 * Real.log 47 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (5159757261056208908835018241282072480118811320785216917437761341427880319677887622596374942004965598324398116991744413760479287094323588994583844540357570870904735056140734759278304398543968814567467785857216396441 / 10864334865353917488990894201016120742494538681300056127407039590489795133045125476328088180120128753685585315881915269477492240280250943632632115464947311885929472648803671502284885631085652925364125487500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 47) / 2 ∧ (2 * (12 / 5) - Real.log 47) / 2 ≤ (46437815382204430291494430983122187722531605874239400141191213806669877532178475128399868132162653425655312780627183227982809849921464902855694902877821589778476287184938564495024246815813987138288001343401165237631 / 97779013788185257400918047809145086682450848131700505146663356314408156197406129286952793621081158783170267842937237425297430162522258492693689039184525806973365253839233043520563970679770876328277129387500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (3855200483134279272704536465187392819652657139015086383570477047583939277714229474861650206032896130392091958268852841725002053969328633742753142055971743060233741796945577939311391806255760396225491865585548282661695723224481750605409494665447194945552613079042324733083147366926640795340124246253160996753412307864211155052719303072490630442582642927952908636835174281016112949703885624276946665555182832902929903632700459988911171333761943223079715347615061552444921335167672320491186185711731789069467275275958153908202866147660168863080114649935211 / 47957017372578390453077407834313126948293912667854115955784509395453811121508514968039449185612564097526665962507071947642385742609018740387943838157271123191620157158569837986602569849261336882713823222482964120697602664692034473707388722641896771337139973443853057386613907957441824024936352413653528927076464592018501296189138159014595649607504505608591074234711872605333685314654924132170060324765443801879882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 47) / 2 * Real.cos (169 / 2 * Real.log 47) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 47) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 47)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 47) / 2 * Real.cos (169 / 2 * Real.log 47) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 47) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 47)) / (2 * (169 / 2)) ≤ (138875671596064609869849141218901874902008964720835773913172309249783519760982514176804987109442131642797005229878133814394877838509173472458338011329950499323065353954755199048435690222789713626098735216010255017671068354630427294269251415189989381764316783736691251398878905027608606642632448146318884743268246247431649139197999873253178224949389724213076520024584306335154467040487137728544955050042161923301533305116238956273566011211996127733281117426189559763827622314124084484094971940150949763346432656075872224722022147819 / 1726452625412822056310786682035272570138580856042748174408242338236337200374306538849420170682052307510959974650254590115125886733924674653965978173661760434898325657708514167517692514573408127777697636009386708345113695928913241053465994015108283768137039043978710065918100686467905664897708686891527041374752725312666046662808973724525443385870162201909278672449627413792012671327577268758122171691555976867675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_48 : (277128129211 / 40000000000 : ℝ) ≤ Real.sqrt 48 ∧ Real.sqrt 48 ≤ (1732050807569 / 250000000000 : ℝ) := by
  constructor
  · calc (277128129211 / 40000000000 : ℝ) = Real.sqrt ((277128129211 / 40000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 48 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 48 ≤ Real.sqrt ((1732050807569 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1732050807569 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_48 : (-594903514619 / 100000000000000 : ℝ) ≤ primeTerm 48 ∧ primeTerm 48 ≤ (-29741678149 / 5000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_48
  have hl := PsiOmega.Num.log_bound_48
  have hc := PsiOmega.Num.theta_48_cos
  have hs := PsiOmega.Num.theta_48_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_48
  have hqpos : (0 : ℝ) < Real.sqrt 48 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 48)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 48) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 48) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 48) = 2028 / 5 - 169 / 2 * Real.log 48 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (5045391617264789160107126149416287941028856438708246533956498887984861309479993604711557210899603768276989835976665114833698610924611470520724512013864280840610294798598177585364298473602317013849175080813353896441 / 10864334865353917488990894201016120742494538681300056127407039590489795133045125476328088180120128753685585315881915269477492240280250943632632115464947311885929472648803671502284885631085652925364125487500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 48) / 2 ∧ (2 * (12 / 5) - Real.log 48) / 2 ≤ (45408524588083052876966987099629148053372927680744609597534121244689333187034122041321316675044196170391681322779189796959932643697554643895585865835216344855137188874102469745319370707808254764744874757761965237631 / 97779013788185257400918047809145086682450848131700505146663356314408156197406129286952793621081158783170267842937237425297430162522258492693689039184525806973365253839233043520563970679770876328277129387500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (9378143218851080957828974074383403014436288379323298752442074853563838653692125424777432996244792787685567379564598913312058843970443365539590265105359006604071883068429613023028041658016657043524483429332321535609054192321424800351534734848000517984065224232363068880029992143115037786592314354597998931840059178888410601626457768627600330522178902491152737558288029994219380693237786904701878551107401649077307056558355004560770617699816173570136346005505663997359285181091236347471879175545049992594995394027401870230081011753376101983 / 21825771462009009699533895832149618664467985143058939883877038942642090039299875256565509318252118060385469309158774077504801333525171195625446440121353613399208462635722450710347125122508270652399535546587802337597486723842063689367273800882356575044102814580669124783952285221520190134015477720702761609478355440989753478798967766591531531199148717219198782229486647799049641672091841027263174121137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 48) / 2 * Real.cos (169 / 2 * Real.log 48) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 48) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 48)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 48) / 2 * Real.cos (169 / 2 * Real.log 48) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 48) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 48)) / (2 * (169 / 2)) ≤ (135061141720835762835915306224326659832557353455875924164576545607940901761538167253386251068094986278773285598579723872799256376601321139929754318376803924701892205748825309486206931436392956154232632493994292338781050640108527775717381347591567227378361818638458661062572326157189074930677396060080724743844474072752692104628543047645284456280615035115006957514179395412366916114882240846905638716066668095478904837533576866950098070321546631947248570443937582773115496190172770059999441345168862491823026063718827968821285018394832376489 / 314291109052929739673288099982954508768338986060048734327829360774046096565918203694543334182830500069550758051886346716069139202762465217006428737747492032948601861954403290228998601764119097394553311870864353661403808823325717126888742732705934680635080529961635396888912907189890737929822879178119767176488318350252450094705135838918054049267741527956462464104607728306314840078122510792589707344382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_49 : (7 : ℝ) ≤ Real.sqrt 49 ∧ Real.sqrt 49 ≤ (7000000000001 / 1000000000000 : ℝ) := by
  constructor
  · calc (7 : ℝ) = Real.sqrt ((7 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 49 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 49 ≤ Real.sqrt ((7000000000001 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (7000000000001 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_49 : (6835037393807 / 50000000000000 : ℝ) ≤ primeTerm 49 ∧ primeTerm 49 ≤ (3418232566609 / 25000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_49
  have hl := PsiOmega.Num.log_bound_49
  have hc := PsiOmega.Num.theta_49_cos
  have hs := PsiOmega.Num.theta_49_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_49
  have hqpos : (0 : ℝ) < Real.sqrt 49 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 49)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 49) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 49) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 49) = 2028 / 5 - 169 / 2 * Real.log 49 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (42364648716745641581799008835698553026274920945437673433847227925278791972305477973166119488743750890049847388570323596695669212700331329043346749067411419900352494932777364487318746065533046637704237643648796905556545825337 / 93295740154782370205867860078813583957996082620571665079241992100605812093681077000488492168991448742547463903680832451847072470363715890318739584003214323741976752339852191180974665862462677981109171182408500287500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 49) / 2 ∧ (2 * (12 / 5) - Real.log 49) / 2 ≤ (381281838731526768194669059642023591456793261874034664021658011464239102308483316243084540485301092623398255728653328140480054077563687211979710149564906313556939837677725343703706228662703710661444133589507540381043257611167 / 839661661393041331852810740709322255621964743585144985713177928905452308843129693004396429520923038682927175133127492066623652233273443012868656256028928913677790771058669720628771992762164101829982540641676502587500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-30095336822258807147335066430492749247101219094097842011959898087333485182822290554226326029874992427539425456571157883719716354330699833858616374632562749577359140709318959739425608826833968749494528765888217938804032872687422883962925597022843206897462324670704817696364171665623497911029752435253144372962628480809060976546311385927837751367840855708383768720295241345211524936838062206748163991367782654877654019038105606362049009988923719923508037584503882859882071786298608968655363622531440562731365213165364621570759758665507757431792816742381 / 127312781992050693894759506436841792838350190066478707488664540227241879230352533750717344267452744614616086315142011851690178287210695640869519044721056543492270409663374069360696773549516677483363911172941071600847800580202817140261660141941883406238804983684205867253413739418473444413303940673391527423773922738711455085814814065799794428603945661128394546067042569376721683850816726171865217195663910549254734183930020332336425781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 49) / 2 * Real.cos (169 / 2 * Real.log 49) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 49) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 49)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 49) / 2 * Real.cos (169 / 2 * Real.log 49) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 49) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 49)) / (2 * (169 / 2)) ≤ (-835806990676128497829437227415451799797441326127813581538194042011744829015208936655120795654235012077415064413760660622172865512008592140658733639311759169182550981391468701680801862081778585849019089669373082957265928655665296174757539034570447969307340878059201257563815522977579565670470607177260718511891034453018160077785595772454488524664856913778169973513456574931865774097665477262057691502546475441143186258285460226053731990589469270851859918557549594894868667794339666179890416811093016642870012889011199711977621155515307685886962684646418444921807338919190589 / 3536466166445852608187764067690049801065283057402186319129570561867829978620903715297704007429242905961557953198389218102504952422519323357486640131140459541451955823982613037797132598597685485648997532581696433356883349450078253896157226165052316839966805102339051868150381650513151233702887240927542428438164520519762641272633724049994289683442935031344292946306738038242268995856020171440700477657330848590409282886945009231567382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_50 : (1414213562373 / 200000000000 : ℝ) ≤ Real.sqrt 50 ∧ Real.sqrt 50 ≤ (3535533905933 / 500000000000 : ℝ) := by
  constructor
  · calc (1414213562373 / 200000000000 : ℝ) = Real.sqrt ((1414213562373 / 200000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 50 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 50 ≤ Real.sqrt ((3535533905933 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (3535533905933 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_50 : (0 : ℝ) ≤ primeTerm 50 ∧ primeTerm 50 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_50
  have hl := PsiOmega.Num.log_bound_50
  have hc := PsiOmega.Num.theta_50_cos
  have hs := PsiOmega.Num.theta_50_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_50
  have hqpos : (0 : ℝ) < Real.sqrt 50 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 50)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 50) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 50) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 50) = 2028 / 5 - 169 / 2 * Real.log 50 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (41422235450585576114403725525292392932234193897397100965199642490608207713434967667790501643389356873144169299320406178946683326507084299712727580102040531394309435304547331416078442356038486277230447329109772127244045825337 / 93295740154782370205867860078813583957996082620571665079241992100605812093681077000488492168991448742547463903680832451847072470363715890318739584003214323741976752339852191180974665862462677981109171182408500287500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 50) / 2 ∧ (2 * (12 / 5) - Real.log 50) / 2 ≤ (372800119336095188521005744273164862206997405709413127297369736196597583801173509933134441371270497022385171478610435686007422531317728702008825476291521683833928180318071893996241256260939034315710582754175870598543257611167 / 839661661393041331852810740709322255621964743585144985713177928905452308843129693004396429520923038682927175133127492066623652233273443012868656256028928913677790771058669720628771992762164101829982540641676502587500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-9677915893713442886328571076013556265590879189048637040580945948611289634554714244899766010975103959792116615538323293684284508999069803085239479102404766606252038339065296840396593819679999218424379875155052740995002625468462658938303332688215452358548509543315082050683328571115690880489948099640224358581580482311587843153884818584308744030487032173536975472514395684996490164748294642831662917093162232740464746279023538553759908464938468246442066716768600326867349227614140206854957865945317496247101947473650683540829454755627048045872588059077133599269039570847 / 28291729331566820865502112541520398408522264459217490553036564494942639828967229722381632059433943247692463625587113744820039619380154586859893121049123676331615646591860904302377060788781483885191980260653571466855066795600626031169257809320418534719734440818712414945203053204105209869623097927420339427505316164158101130181069792399954317467543480250754343570453904305938151966848161371525603821258646788723274263095560073852539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 50) / 2 * Real.cos (169 / 2 * Real.log 50) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 50) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 50)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 50) / 2 * Real.cos (169 / 2 * Real.log 50) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 50) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 50)) / (2 * (169 / 2)) ≤ (-134396265247098268107421707890188960690293104823570130515354584582728934547190935482531328699355870458714889555548950425814907516445924616336483123363302677102270857519374816297817289420369839803664294962000805578657684230587277930935831722243602827520383041335023490368940068423506578593400229807431774258958934373638187311702093179763714736587797071009168654019744869608478891589501584813124123724159453126120171770456096333195888174979534114953496695943447224057473712402495149120462625671194219730499996928519775455931349292190698933204324759232473302075970043647 / 392940685160650289798640451965561089007253673044687368792174506874203330957878190588633778603249211773506439244265468678056105824724369261942960014571162171272439535998068115310792510955298387294333059175744048150764816605564250432906358462783590759996311678037672429794486850057016803744765248991949158715351613391084737919181524894443809964826992781260476994034082004249140999539557796826744497517481205398934364765216112136840820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_51 : (3570714214271 / 500000000000 : ℝ) ≤ Real.sqrt 51 ∧ Real.sqrt 51 ≤ (7141428428543 / 1000000000000 : ℝ) := by
  constructor
  · calc (3570714214271 / 500000000000 : ℝ) = Real.sqrt ((3570714214271 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 51 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 51 ≤ Real.sqrt ((7141428428543 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (7141428428543 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_51 : (4558668543257 / 25000000000000 : ℝ) ≤ primeTerm 51 ∧ primeTerm 51 ≤ (18237526711867 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_51
  have hl := PsiOmega.Num.log_bound_51
  have hc := PsiOmega.Num.theta_51_cos
  have hs := PsiOmega.Num.theta_51_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_51
  have hqpos : (0 : ℝ) < Real.sqrt 51 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 51)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 51) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 51) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 51) = 2028 / 5 - 169 / 2 * Real.log 51 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (425643148174357567768214224162562700649812282226281539548215063140510639707917224259589953302024810097120591935386860203526165527623913649326464157064061906426394441668670949419403882453452478353536413905634046769065202709828862193837 / 980547605341944006646659269354136548242540190906507650055745465876815188089309346317053678790051602093763920390355332896254974746152998031060645951520714449570926059497433436797109617349376588943057168579926341258312394037500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 51) / 2 ∧ (2 * (12 / 5) - Real.log 51) / 2 ≤ (3830788336520799439572650686709264660705138926148361418695914456930527401038753304496494996987424554916515009357540696307616691979358627611143195787498336159383791617878411376080385478347111049730006094723531919872658275221798349894667 / 8824928448077496059819933424187228934182861718158568850501709192891336692803784116853483109110464418843875283513197996066294772715376982279545813563686430046138334535476900931173986556144389300487514517219337071324811546337500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (957759710450905671702278365133944603663635306361424099523688805588591325398654505316320882414746409095419416484664886325300122146860184972336631924198105803919893170146785559601293452618173042746168823114159163663030387870773851248249900964881784672213759296232250544525698086602856799586521522260686964360267784796277105738879602557248314833672281282344918390659263939207495295239604871026280679239992939693764063456086143135714627504408325760548330547382085247162017690994160636866616901887634299958051889600706525201350247561511105223712997777214130379107609157534180286957754692398201 / 3125167018579385794106776214717565352112425308474918181699084090598629498174006918522673836879909602861909234771076952574911711295275810988167558345394156009921599868738224604336888104749243904982889545445228134042045488815795887525127804680057117256846805211040342097483193701345277814250408272659673307325533300764437795633827964826228041462535813474510899672265643076973974317760747247945024294579444207587397472769104063368320224183931055068969726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 51) / 2 * Real.cos (169 / 2 * Real.log 51) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 51) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 51)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 51) / 2 * Real.cos (169 / 2 * Real.log 51) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 51) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 51)) / (2 * (169 / 2)) ≤ (34484743342736079680774410674186485535918163786542420561977649879292007625594368924394170151510666230930869404213623626323800408335662985064904811704211932178871733520276482446944048905852756344054928647998652252578433040686350616495285070443716698582723200814125945734319826475047841426863305587705577385551848642413853387036712807030508881548789291686071893705365161911725721429896291025301750438707086711421919820391355967327573639632986498506917514188824023499756191376693359185053675792569840640657125302687450077581136147149852761101839929625672521766759078103 / 112506012668857888587843943729832352676047311105097054541167027261550661934264249066816258127676745703028732451758770292696821606629929195574032100434189616357177595274576085756127971770972780579384023636028212825513637597368651950904600968482056221246484987597452315509394973248430001313014697815748239063719198827519760642817806733744209492651289285082392388201563150771063075439386900926020874604859991473146309019687746281259528070621517982482910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_52 : (7211102550927 / 1000000000000 : ℝ) ≤ Real.sqrt 52 ∧ Real.sqrt 52 ≤ (450693909433 / 62500000000 : ℝ) := by
  constructor
  · calc (7211102550927 / 1000000000000 : ℝ) = Real.sqrt ((7211102550927 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 52 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 52 ≤ Real.sqrt ((450693909433 / 62500000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (450693909433 / 62500000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_52 : (-4647590412503 / 100000000000000 : ℝ) ≤ primeTerm 52 ∧ primeTerm 52 ≤ (-232339888187 / 5000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_52
  have hl := PsiOmega.Num.log_bound_52
  have hc := PsiOmega.Num.theta_52_cos
  have hs := PsiOmega.Num.theta_52_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_52
  have hqpos : (0 : ℝ) < Real.sqrt 52 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 52)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 52) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 52) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 52) = 2028 / 5 - 169 / 2 * Real.log 52 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (4824005701236601292824154589942769690131505760236699541496131590349913941950063133613007505764059087079305524488471982075546529914974462349838547706607692379300448128514467164361422850948563930603538432521066936468753730490219695587920303400891 / 11367234174898638732677389716680310058396680716936869338642426683507671650044144781780405177827466150664801106132680731913743237856163942786275529826092189208009693398176338706688368085683257648290542145174731548244159977780396519862500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 52) / 2 ∧ (2 * (12 / 5) - Real.log 52) / 2 ≤ (43416051345347160684591273160879249283294196334992228534331592696524240540481905035467414124184645526964860625943583754239381986940841435359036485993415412567644810159468933292739054698961302893736123164748472453995678939607063803436575889317581 / 102305107574087748594096507450122790525570126452431824047781840151569044850397303036023646600447195355983209955194126587223689140705475485076479768434829702872087240583587048360195312771149318834614879306572583934197439800023568678762500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (14502150426341697782035000873106661587371055843457841616276887334902350373899360771031951912925777089531317860418259539394424715981921055459951369919430764128836069343822448423550480656867307358497464071492499568604905785111145513915136982540617816178234185255439799398534529592372160286801798549946713280355218755264760753383371123372697776398678435198854458891725750464873865821808598675367842439333412796267326558832422252239507417146375582453377313104144815551455917191989489239328889435790511800387643805810844568799888392722533718600811221543544424238803081762477954759720117450025849388968805541845938174673 / 52499539305685904459319549760490056135475647667244761632679583454196571075992550331694300765728178071031207223183000477153991996428696704907866179978797628954326103520480581878908351522251961116612138466623074596235843058441715589813669093010407847702485457628236382318937762074000807511025647288710910438226440331251420991893290096585734622210784466915790870022958002859638081593214697122103226254231999418547067190367336047080200345258823341067763598132261611223220825195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 52) / 2 * Real.cos (169 / 2 * Real.log 52) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 52) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 52)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 52) / 2 * Real.cos (169 / 2 * Real.log 52) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 52) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 52)) / (2 * (169 / 2)) ≤ (1044332941608518498138470756088598521906338595178599735715124404128057982163064124749003021849289747042952473722244511950625224209831464576525427693302259040357493574997868949052365336511506773304274714691147508935622269292957846357687096186861210570842856664215377279610346753289495489210790393044237093485460367034948905024191022981844196461762284258470939509854989355990391686461396962440659817314834911516041766933896686979463332953303266775784405431141627003447846773614055122292916333277328314699109064113057252503315853055632942292931995388478421101668055404957204338448645150096877063269743989961 / 3779966830009385121071007582755284041754246632041622837552930008702153117471463623881989655132428821114246920069176034355087423742866162753366364958473429284711479453474601895281401309602141200396073969596861370928980700207803522466584174696749365034578952949233019526963518869328058140793846604787185551552303703850102311416316886954172892799176481617936942641652976205893941874711458192791432290304703958135388837706448195389774424858635280556878979065522836008071899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_53 : (5687585851 / 781250000 : ℝ) ≤ Real.sqrt 53 ∧ Real.sqrt 53 ≤ (7280109889281 / 1000000000000 : ℝ) := by
  constructor
  · calc (5687585851 / 781250000 : ℝ) = Real.sqrt ((5687585851 / 781250000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 53 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 53 ≤ Real.sqrt ((7280109889281 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (7280109889281 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_53 : (4997257865427 / 100000000000000 : ℝ) ≤ primeTerm 53 ∧ primeTerm 53 ≤ (78093404787 / 1562500000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_53
  have hl := PsiOmega.Num.log_bound_53
  have hc := PsiOmega.Num.theta_53_cos
  have hs := PsiOmega.Num.theta_53_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_53
  have hqpos : (0 : ℝ) < Real.sqrt 53 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 53)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 53) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 53) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 53) = 2028 / 5 - 169 / 2 * Real.log 53 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (4715743054816026712733506926951664766238758629610396242269896806133813810464748787985067257815271082044455153004777145519592445474020152351415725100255247704375466254490472254676129837519187372591793979337338567269548560368789270599768853400891 / 11367234174898638732677389716680310058396680716936869338642426683507671650044144781780405177827466150664801106132680731913743237856163942786275529826092189208009693398176338706688368085683257648290542145174731548244159977780396519862500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 53) / 2 ∧ (2 * (12 / 5) - Real.log 53) / 2 ≤ (42441687527562716593027509399748855126526232610142065703562214333597976988917635073484696086355945965338996507965831849478147939546946453279270913752646340591116081245664933772123312921431928124550088543910808217924954330708430369307215089317581 / 102305107574087748594096507450122790525570126452431824047781840151569044850397303036023646600447195355983209955194126587223689140705475485076479768434829702872087240583587048360195312771149318834614879306572583934197439800023568678762500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-541971064835408606785765465227593971753820305228703310450272119124393160768126886853888731461896237261586242937985530637843847846952106886479800406185467987586677473877601547219557635790320822148582253767190214340134577513597895757451241346493458349419234601234352013352997539123108119319957547528049465588053256021771144388302407052849850468145263655915352260385262553491526004129752822149835036542347431917848006595241059091959315995764945500970057578830329455213586216092539775844697056697790921151151363553741024643840138645629039066669533538369815816882830278403588273067489392631 / 1679985257781948942698225592335681796335220725351832372245746670534290274431761610614217624503301698272998631141856015268927743885718294557051717759321524126538435312655378620125067248712062755731588430931938387079546977870134898874037410976333051126479534644103564234206008386368025840352820713238749134023246090600045471740585283090743507910745102941305307840734656091508418610982870307907303240135423981393506150091754753506566411048282346914168435140232371559143066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 53) / 2 * Real.cos (169 / 2 * Real.log 53) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 53) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 53)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 53) / 2 * Real.cos (169 / 2 * Real.log 53) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 53) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 53)) / (2 * (169 / 2)) ≤ (-15052582918859416060546529942316862689602590802607281688544439447571942004994886865558725841624135528403455626878924260659914089705497512310959473313204890231581444658806522550744343546807856075566781215704944049525051399753188246376871804284837192310649583212829926633194289621952305984661833027484060121019315919233760460176184644709554760866813808622054487618323080442922535969125442839742293726617308172332363150764099928511828389029554623090970535547659036283852514265188199610291282032813919688632480478046393452903209364218252319158673519519375388027166268613446285228926582898959439554120416199076457 / 46666257160609692852728488675991161009311686815328677006826296403730285400882266961506045125091713840916628642829333757470215107936619293251436604425597892403845425351538295003474090242001743214766345303664955196654082718614858302056594749342584753513320406780654562061278010732445162232022797589965253722867946961112374215016257863631764108631808415036258551131518224764122739193968619664091756670428443927597393058104298708515733640230065192060234309450899209976196289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_54 : (7348469228349 / 1000000000000 : ℝ) ≤ Real.sqrt 54 ∧ Real.sqrt 54 ≤ (146969384567 / 20000000000 : ℝ) := by
  constructor
  · calc (7348469228349 / 1000000000000 : ℝ) = Real.sqrt ((7348469228349 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 54 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 54 ≤ Real.sqrt ((146969384567 / 20000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (146969384567 / 20000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_54 : (-147561721243 / 12500000000000 : ℝ) ≤ primeTerm 54 ∧ primeTerm 54 ≤ (-295069389647 / 25000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_54
  have hl := PsiOmega.Num.log_bound_54
  have hc := PsiOmega.Num.theta_54_cos
  have hs := PsiOmega.Num.theta_54_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_54
  have hqpos : (0 : ℝ) < Real.sqrt 54 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 54)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 54) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 54) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 54) = 2028 / 5 - 169 / 2 * Real.log 54 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (64650679927138825328427111771312038704020237737487175547629085810686806428884765748231154571401924049829898738122530838876757924246430109787328801942086762219659710729749866796920646162050071023009993274799448660964965770978685003563157878621555029720537 / 159431339652762722515907275918883515310168826066751228935526999334015460194967399950874811095091539156105837469776657443761633013705844956178265245646450699914458577779885880768551703241336989066239117821561103868977371230035686834654063010287500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 54) / 2 ∧ (2 * (12 / 5) - Real.log 54) / 2 ≤ (581856119824190194320378826472103225938796903934244407357019980984022781446998881710911473117087489750318269565741029648686885615326652160567536705427516804580104790340847454616679245340190080591913905490660742967411659599324837759230479708392783134874367 / 1434882056874864502643165483269951637791519434600761060419742994006139141754706599557873299855823852404952537227989916993854697123352604605604387210818056299230127200018972926916965329172032901596152060394049934820796341070321181511886567092587500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-5029648991842587782229497397085836010110456791249211795376115174572333616766643005970564721854686571195396324584529736839429160676252951338803191223869832932574470171479317588554958548838394906367301954705703877327497258613213936182056639630286350456666800806943419829860865038524441141577550821675700043078288471182449192989799608642273298102757463716585026248694453169774052866412151146900984373846162723798478021563064172612155793727923072964591247455458913652891529089543342124561193645514890627691065293006594433068578601028546467716411188533593385175076333237159034772431379569910913721562585881149704010128343161 / 20170808594190802891123080707692819028176758108277661395151274169931166922390428467647506444160730713845667090088074002812524568592728407546424219837254809212736328584266143277690870583433575770341791984190666947428478605700587805317327700214382551300605108123544571896118110163778900395235708905711248835367026501626427486434517921383129912384530956629285885861762924888855945417333292331506543552355468802030116763830147740568603101766160720209649514510802211178323510023538616413716226816177368164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 54) / 2 * Real.cos (169 / 2 * Real.log 54) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 54) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 54)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 54) / 2 * Real.cos (169 / 2 * Real.log 54) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 54) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 54)) / (2 * (169 / 2)) ≤ (-34921720973648307026750497542255920372850376267962425919149173184116234414871248791877942106378335001619246514578295685768459475076274763388195252969059123744629520663886388517541512801817516069695569015954658602851048220777448067503411000294209586948389041983362397453588030359521554423903037352190994645965156143558741417692579480573923378874618520497202446455361010715943634381235377442328223920281489765119259165080621164013985565267781695540269589326059010576512716205510432868065177169535651993413545108709758388484615886620647653495389927231088975641426471568864971426696709779859003051095700992253829979107865399753569319 / 140075059681880575632799171581200132140116375751928204132994959513410881405489086580885461417782852179483799236722736130642531726338391719072390415536491730644002281835181550539519934607177609516262444334657409357142212539587415314703664584822101050698646584191281749278597987248464586078025756289661450245604350705739079766906374454049513280448131643258929762928909200617055176509258974524350996891357422236320255304376025976170854873376116112567010517436126466516135486274573725095251575112342834472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_55 : (1483239697419 / 200000000000 : ℝ) ≤ Real.sqrt 55 ∧ Real.sqrt 55 ≤ (927024810887 / 125000000000 : ℝ) := by
  constructor
  · calc (1483239697419 / 200000000000 : ℝ) = Real.sqrt ((1483239697419 / 200000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 55 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 55 ≤ Real.sqrt ((927024810887 / 125000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (927024810887 / 125000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_55 : (0 : ℝ) ≤ primeTerm 55 ∧ primeTerm 55 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_55
  have hl := PsiOmega.Num.log_bound_55
  have hc := PsiOmega.Num.theta_55_cos
  have hs := PsiOmega.Num.theta_55_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_55
  have hqpos : (0 : ℝ) < Real.sqrt 55 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 55)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 55) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 55) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 55) = 2028 / 5 - 169 / 2 * Real.log 55 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (972225182220384975300326010712160184650626388834034344085088070935288707044972949907064453365838428555171139819262352848297178888328378957080952977007028218395132986816133306207288472768632539938437950805588115727721033454513026959311237368305120547008809306917813 / 2453048783515389728287165310359980859189466593495149872592158688310325334629242659889850675619201439538957721307243698958230481204304930717212196616777619830502573486359172755387788731863170672807548895316974181268956543405629861456732968022423526360337500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 55) / 2 ∧ (2 * (12 / 5) - Real.log 55) / 2 ≤ (8750026647368069159636227462678551486981284064102050411285181424000272771942309386877068315490865660025165655520905148768213306630377245263900991967317997860092813881462829664450503795262271063351288404461760623464204230105239982391465355366977069768516686681740483 / 22077439051638507554584487793239827732705199341456348853329428194792928011663183939008656080572812955850619491765193290624074330838744376454909769550998578474523161377232554798490098586768536055267940057852767631420608890650668753110596712201811737243037500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (294411461136325978495716516829060754820866229182210689590779252783108083168749602606229509226939502770139793770400370160257069808592373683656302525862199888431139460251681774499624832072798019828914174730329616497312898843723742479121354021730400506442177691999526773494118001508431097972879511201395572212819467224574100913568114277407891098934062165460012126000817533099898707345644708334341695377269376398263334742824439337787943782489692837022933503227421643339163402342539011038668658662332244373729108034873672497789299258908759918713912156710076154326740977532860381305446207688302663384989872282422081755048222187693555947221 / 965108070543521688238016558745485919827452763119658560289088910598323162645188027450009957225710879490774328133123285367691608912082049871031045960425074795302660326001593624994364686425342513562105901678698785835077015298039981544520623270467567887846571819493024593170280925699533040335164424045016360251974594767308572956438739743030623980688987476247206850542468715702199731771510319358362844261615111091642993172977687976763800818946572785783297884988137172939996716074064757537177304933619981763702662131559906200095610984135419130325317382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 55) / 2 * Real.cos (169 / 2 * Real.log 55) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 55) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 55)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 55) / 2 * Real.cos (169 / 2 * Real.log 55) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 55) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 55)) / (2 * (169 / 2)) ≤ (2713694999397392835795277175020624488446927371246102665260113675624921688540551419498731553501260865517105253149105994625219519651999939874582900740927138964097200834662424731506112481382863163922649128111987545993198361605405271552427823081631799546379448278904252716345539535475511038336599507550934750811279437033117139501077157697226283643531870529479190737274936107061011300532912072945776217943748970426013661610402542069680744615295479969065359505689532211071298476875432122977825197747208004374097682538018011997020997361016801006225181315846691330263218648642094994764540731138303850887562316462367538603 / 8894435978129095878801560605398398237129804664910773291624243400074146266938052860979291765792151465386976208074864197948645867733748171611422119571277489313509317564430686847948064950095956604988367989870888010256069772986736469914302064060629105654394005888447714650657309011246896499728875331998870776082197865375515808366539425471770230606029708581094258334599391683911472728006239103206671972715044863820581825082162372393855188347411614793778873308050672185815009735338580805462626042268241751934283734204456095540081150829792022705078125000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_56 : (7483314773547 / 1000000000000 : ℝ) ≤ Real.sqrt 56 ∧ Real.sqrt 56 ≤ (1870828693387 / 250000000000 : ℝ) := by
  constructor
  · calc (7483314773547 / 1000000000000 : ℝ) = Real.sqrt ((7483314773547 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 56 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 56 ≤ Real.sqrt ((1870828693387 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1870828693387 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_56 : (-1212706699703 / 100000000000000 : ℝ) ≤ primeTerm 56 ∧ primeTerm 56 ≤ (-1212499148373 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_56
  have hl := PsiOmega.Num.log_bound_56
  have hc := PsiOmega.Num.theta_56_cos
  have hs := PsiOmega.Num.theta_56_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_56
  have hqpos : (0 : ℝ) < Real.sqrt 56 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 56)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 56) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 56) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 56) = 2028 / 5 - 169 / 2 * Real.log 56 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (950125045718319649156003512460299505798491640268607106452983532101882128654194199134503517639446855011642394738096765208859439719705407419275382812416280461375029156551838916558380650758690091224775173975446571561587379885716762777472318206687213171163106181917813 / 2453048783515389728287165310359980859189466593495149872592158688310325334629242659889850675619201439538957721307243698958230481204304930717212196616777619830502573486359172755387788731863170672807548895316974181268956543405629861456732968022423526360337500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 56) / 2 ∧ (2 * (12 / 5) - Real.log 56) / 2 ≤ (8551125418849587570810744838491308535601666186595813583387840571737305811586714776251115869433909364503450432748403316896892806902256232543850870912422751731338882569969450602356066916275498532215913310674802986569660409691026299179245992810063855850734186681740483 / 22077439051638507554584487793239827732705199341456348853329428194792928011663183939008656080572812955850619491765193290624074330838744376454909769550998578474523161377232554798490098586768536055267940057852767631420608890650668753110596712201811737243037500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (1149413079757457673380782890793358041746269677518589484027593803329414577853346538103558582309803111110534132847659386562525697699592276535573950402906306735829219881096260524953977219653827333771479247980596709087978252110891115414014303089590512998951496417462564241148806831038599342488745782821083842891534906524378140990110665788757080852870151397271258176045955178325121128305506257159360206398012874681227242196638613399038175110456549217003223428334767239131105193289713902522479158333062230939149626306318946131636532503758733302572317361683331632723439970738456199684537651085264921562655412689537387446802837858685009827677808845421 / 4447217989064547939400780302699199118564902332455386645812121700037073133469026430489645882896075732693488104037432098974322933866874085805711059785638744656754658782215343423974032475047978302494183994935444005128034886493368234957151032030314552827197002944223857325328654505623448249864437665999435388041098932687757904183269712735885115303014854290547129167299695841955736364003119551603335986357522431910290912541081186196927594173705807396889436654025336092907504867669290402731313021134120875967141867102228047770040575414896011352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 56) / 2 * Real.cos (169 / 2 * Real.log 56) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 56) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 56)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 56) / 2 * Real.cos (169 / 2 * Real.log 56) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 56) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 56)) / (2 * (169 / 2)) ≤ (662175260248646571360149250003537098665038150148347447391023015158321704275783026735380980045052532613163636972018472564375599123618525649594311838437283409551111728887755462114533854899695802405150138681109899167101057455839533193917434398189514640631550077894851957310541346687762539406197420196689653277723806284990091607394515746712514108416570529742881283297413346447953286643066312025052589284426634380972304894399103530217941082052832481476302731251641593141405306177463647514721735259236394864795641975365945280870459302949565568424912993030201346700758878518080598750133016413988073473797083749529955957665681868479368623449 / 2561597561701179613094849454354738692293383743494302707987782099221354124878159223962036028548139622031449147925560889009210009907319473424089570436527916922290683458556037812209042705627635502236649981082815746953748094620180103335318994449461182428465473695872941819389304995239106191921916095615674783511672985228148552809563354535869826414536556071355146400364624804966504145665796861723521528141932920780327565623662763249430294244054545060608315512718593589514722803777511271973236300173253624557073715450883355515543371438980102539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_57 : (754983443527 / 100000000000 : ℝ) ≤ Real.sqrt 57 ∧ Real.sqrt 57 ≤ (7549834435271 / 1000000000000 : ℝ) := by
  constructor
  · calc (754983443527 / 100000000000 : ℝ) = Real.sqrt ((754983443527 / 100000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 57 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 57 ≤ Real.sqrt ((7549834435271 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (7549834435271 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_57 : (-3 / 400000000000 : ℝ) ≤ primeTerm 57 ∧ primeTerm 57 ≤ (153 / 20000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_57
  have hl := PsiOmega.Num.log_bound_57
  have hc := PsiOmega.Num.theta_57_cos
  have hs := PsiOmega.Num.theta_57_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_57
  have hqpos : (0 : ℝ) < Real.sqrt 57 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 57)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 57) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 57) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 57) = 2028 / 5 - 169 / 2 * Real.log 57 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (17105464517613977552002507773205154527939539766685746545364934164955172790755122955165422370772531152264381814501916050216872274837349160160217198513003558031899165631141359368116865831746262298060438074348179934666562076426081424952014686875293693700721781235828639000188709 / 45195833752878239583461417004818314818453129358575966691897060486710870719489611990973659477846895427797776785918309748789025998483788349578409310697795273806392445904515885597725755732208404816206779833368462559997406505734598864224699651306150562102466982210137500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 57) / 2 ∧ (2 * (12 / 5) - Real.log 57) / 2 ≤ (153949180794586035440461873935139926762481828077752818097157336962997635858341169955957684968849839213226477506923640556927838169207430847203430311662901445889782425415711027381284982554385051742523672444495670437776611331855815840620215427266457830393278639859864488321736019 / 406762503775904156251152753043364833366078164227183700227073544380397836475406507918762935300622058850179991073264787739101233986354095146205683796280157464257532013140642970379531801589875643345861018500316163039976658551611389778022296861755355058922202839891237500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-3785846468106544764695136479047300907058994875658026134695772440435568447030424137277094916298123615730992331952093321260648659885701710781101144187996473692727481864355552127678992295169084238375367797010432981095958301234940886743392849459552952775811657732897714332279437937149054215586431102241223087675657867103805175885485238567595128752476440314716013036360346237563302572421253306043857684738594658437347792371245258236988403897174421184618182239866828953759202044023029779201772458054759855993911013141437607880737504836937174607542190941825054029070466407568864042535789642535803292806866219266388080276264875492866673410813197371407773737 / 14588654259785607983698439370098653642188011627985972866875445808209942938192255318067443371277420292915706975124247967620191629388859679320383379592020525141573197671083433522763686963871377802203053681864885079477227609342930597083973802466646944473542177127781584718378328663704545283913754698227829609577105379068799984190965275397257054772963450439066758407751045541632719276980505336857872724099927131142364172313337367817634375871284438295293772285878269193550559828040644868353333403517057150518921433117035863740670029073953628540039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 57) / 2 * Real.cos (169 / 2 * Real.log 57) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 57) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 57)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 57) / 2 * Real.cos (169 / 2 * Real.log 57) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 57) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 57)) / (2 * (169 / 2)) ≤ (-26286236945192449362771482898137471479088435428664209504879829591324012347678316625763197205519676578561669856633703279018053835918075792422782101833012027823105924103638998468975796664059053421973997341936748886087070026972093851518837080939417927297793117529777156317024114780163126319489269667694403660361462230769240063116908931081785798990875455534941715933183679083687641237495647602325664965964268105488723895001849356931567856175026525722912762387586824261409250799673271864546552184960749362167276460767459883946187181352834087812379777464023127279515511996568801951797521357514711726207257451626548984810044671439223973344002212790469031947714416532879670684737 / 101310099026288944331239162292351761404083414083235922686635040334791270404112884153246134522759863145247965105029499775140219648533747773058217913833475869038702761604746066130303381693551234737521206124061701940814080620437018035305373628240603781066265118942927671655405060164614897804956629848804372288729898465755555445770592190258729547034468405826852488942715594039116106090142398172624116139582827299599751196620398387622460943550586377050651196429710202732989998805837811585787037524424007989714732174423860164865764090791344642639160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_58 : (7615773105863 / 1000000000000 : ℝ) ≤ Real.sqrt 58 ∧ Real.sqrt 58 ≤ (951971638233 / 125000000000 : ℝ) := by
  constructor
  · calc (7615773105863 / 1000000000000 : ℝ) = Real.sqrt ((7615773105863 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 58 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 58 ≤ Real.sqrt ((951971638233 / 125000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (951971638233 / 125000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_58 : (-17 / 2000000000000 : ℝ) ≤ primeTerm 58 ∧ primeTerm 58 ≤ (923 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_58
  have hl := PsiOmega.Num.log_bound_58
  have hc := PsiOmega.Num.theta_58_cos
  have hs := PsiOmega.Num.theta_58_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_58
  have hqpos : (0 : ℝ) < Real.sqrt 58 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 58)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 58) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 58) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 58) = 2028 / 5 - 169 / 2 * Real.log 58 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (16712447359676970815221312573288644929046280477753336793685723399712817118521760490153302275341655456573207300859947912895221274836262199828280272155250165911540566171137234254202660676543640373359137533536975300158290520278163300179280016279112235895524922204320526500188709 / 45195833752878239583461417004818314818453129358575966691897060486710870719489611990973659477846895427797776785918309748789025998483788349578409310697795273806392445904515885597725755732208404816206779833368462559997406505734598864224699651306150562102466982210137500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 58) / 2 ∧ (2 * (12 / 5) - Real.log 58) / 2 ≤ (150412026393377789462889591174722723260411744026602933876953097090810755595335065222786574430291995689610194922704500540306577259173714493345540015988544792088104259852385496465906597576465563284587641810810337085863159337731000958653625437888193022893692914564552088321736019 / 406762503775904156251152753043364833366078164227183700227073544380397836475406507918762935300622058850179991073264787739101233986354095146205683796280157464257532013140642970379531801589875643345861018500316163039976658551611389778022296861755355058922202839891237500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-259062743564282551077587708174889663222703184851944498983132375237504654426419349189059894420751970375615497532688569887003984416347547861719907365785691483249821358794564318362000491654610580400451717863802532372763013932060440514807765317270780249145059591703614752816207331965151265717616787608035528346667787730408975943672226129237787569594434435813169644707697813079206919032524317510585366776449347556224520825605912119522955450444639800415498813241636034851002776787338524803928328017212166178604630218883829373717447444489526898806673825484584282492007136560179717197443429811013709533323737142426121260043354229915814307761183384807076077111751528438291 / 890420792223242674786281699835122902965576881590940726738003284192501400036148395878139854203944109675030943305923337867443336754691142536644493383302034005222973490666713471848369565665977649060244975699761052214186255453059728825926135404458431669527720771959325239158833536603060625238876629530507178318915123234179686535093095422195865159482632473087570703598086275734418901182892171439079145758052193062888438251546470203713035636675075579546739031120499828707919911379433890890706384492007882722102138251772208480265504704220802523195743560791015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 58) / 2 * Real.cos (169 / 2 * Real.log 58) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 58) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 58)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 58) / 2 * Real.cos (169 / 2 * Real.log 58) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 58) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 58)) / (2 * (169 / 2)) ≤ (-14390282074181912120235149313105189920265725679090192309651123642137271825884753478141701280235704689215218636209954851373376871320165256593167454814132982255422909556557490579528907669404548824555635497336717833065784724412839523002686549634708246503521987174902829796163841070364240690499567007829272514916670763603420845769163763091519736604657587649815627307400922959427554475041722411712866956761838252122840575969591385680039701533662614220620952867700379186624554790236358120943353945689830159739811163703291191316006158187977494778787535707359785326130727574268273309313829058883604366236546782320248783946035075027792182786664011265740419073655251996767 / 49467821790180148599237872213062383498087604532830040374333515788472300002008244215452214122441339426390607961440185437080185375260619029813582965739001889179054082814817415102687198092554313836680276427764502900788125302947762712551451966914357314973762265108851402175490752033503368068826479418361509906606395735232204807505171967899770286637924026282642816866560348651912161176827342857726619208780677392382691013974803900206279757593059754419263279506694434928217772854412993938372576916222660151227896569542900471125861372456711251288652420043945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_59 : (1920286436967 / 250000000000 : ℝ) ≤ Real.sqrt 59 ∧ Real.sqrt 59 ≤ (7681145747869 / 1000000000000 : ℝ) := by
  constructor
  · calc (1920286436967 / 250000000000 : ℝ) = Real.sqrt ((1920286436967 / 250000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 59 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 59 ≤ Real.sqrt ((7681145747869 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (7681145747869 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_59 : (-1209599421311 / 12500000000000 : ℝ) ≤ primeTerm 59 ∧ primeTerm 59 ≤ (-9674583301233 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_59
  have hl := PsiOmega.Num.log_bound_59
  have hc := PsiOmega.Num.theta_59_cos
  have hs := PsiOmega.Num.theta_59_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_59
  have hqpos : (0 : ℝ) < Real.sqrt 59 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 59)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 59) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 59) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 59) = 2028 / 5 - 169 / 2 * Real.log 59 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (16326148773924403900749392218137836901760418794022142013579621954546009292261409096347521286894719779698153798325389271063924471161661404253177355350326796966354646136189356824538029003115482591901501224057572597199536293873824073444212107087734030785418862325831464000188709 / 45195833752878239583461417004818314818453129358575966691897060486710870719489611990973659477846895427797776785918309748789025998483788349578409310697795273806392445904515885597725755732208404816206779833368462559997406505734598864224699651306150562102466982210137500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 59) / 2 ∧ (2 * (12 / 5) - Real.log 59) / 2 ≤ (146935339140158934077949046598310296751078528481091007212828564235367695307909826943791636987658445072646922714541680037295048781871646728023044294041225952322166561478795887010200254028285694423023743351825346291431595363704487987999703488054167591123800723332202088321736019 / 406762503775904156251152753043364833366078164227183700227073544380397836475406507918762935300622058850179991073264787739101233986354095146205683796280157464257532013140642970379531801589875643345861018500316163039976658551611389778022296861755355058922202839891237500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (13767352557308933854134528320830083251290245753409381560898284422702719102271418378093062775454101527654861199558816841365974290239622009135812310068679986270048569073678382521410957242250506950281089577603693436838875515399896608551209993906262930842682984320254542532193572431548505603931318623712479560099854829861505735868609253990803350731280656609556774367346904908255136738288207754500765631379844888865518221827093257834260041355637026493913997269098008012669059459578701494820358191301665239140115440858026921628853121252721573492372515347328350133925221939609499347258952227489949600584793475536107948434382265772745973551018956091104410198034485325931897 / 75542285082019524331429998819459584402523143115195157949910061549578020377075962036532777780151072894145088183446337959976839792484211985694075667353493897140001270721748061183039288009029105433693181321062487590606979840466038487742839080964280426905130676167608409766213700527766208768519255538019479805886038765246646973940867183283724510941308261765900569205757828789447260486810421551116448145905210822048077305420395278008611275622755314419387469473763417273562823813568134486313407046549638116851992892109279001766601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 59) / 2 * Real.cos (169 / 2 * Real.log 59) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 59) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 59)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 59) / 2 * Real.cos (169 / 2 * Real.log 59) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 59) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 59)) / (2 * (169 / 2)) ≤ (12393450382593138339585432301840621664631075513397641126057401823476240817936551380314240000889459684824560901772941717883776781709729432103863739273652107024805459587315947444300813517978418134042000677824723004903784869546087694128934822935944682964862283891468757843634375298914953422312093755633262816418201623690466935500965442859860407376760147593976369708136940410582376876397063566401734030131500509156384202682428361845427082688157486728080753942538113187128566055489767686316532006994763137208758665700179847385292553492004785458479725510184709878033914771486964822328823754371926378492264086715295053958478636547151218059879297378337 / 67988056573817571898286998937513625962270828803675642154919055394620218339368365832879500002135965604730579365101704163979155813235790787124668100618144507426001143649573255064735359208126194890323863188956238831546281856419434638968555172867852384214617608550847568789592330474989587891667329984217531825297434888721982276546780464955352059847177435589310512285182045910502534438129379396004803331314689739843269574878355750207750148060479782977448722526387075546206541432211321037682066341894674305166793602898351101589941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_60 : (3872983346207 / 500000000000 : ℝ) ≤ Real.sqrt 60 ∧ Real.sqrt 60 ≤ (1549193338483 / 200000000000 : ℝ) := by
  constructor
  · calc (3872983346207 / 500000000000 : ℝ) = Real.sqrt ((3872983346207 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 60 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 60 ≤ Real.sqrt ((1549193338483 / 200000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1549193338483 / 200000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_60 : (0 : ℝ) ≤ primeTerm 60 ∧ primeTerm 60 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_60
  have hl := PsiOmega.Num.log_bound_60
  have hc := PsiOmega.Num.theta_60_cos
  have hs := PsiOmega.Num.theta_60_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_60
  have hqpos : (0 : ℝ) < Real.sqrt 60 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 60)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 60) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 60) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 60) = 2028 / 5 - 169 / 2 * Real.log 60 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (15946342909763085861436879558038241248663647901232847679595370774432078252378790875278696723319028533875846300003703417387636567122918111929962007403577399840601702478715826618210529884776580329437002161080945606825003507791385285073654413054959228899658087493544432750188709 / 45195833752878239583461417004818314818453129358575966691897060486710870719489611990973659477846895427797776785918309748789025998483788349578409310697795273806392445904515885597725755732208404816206779833368462559997406505734598864224699651306150562102466982210137500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 60) / 2 ∧ (2 * (12 / 5) - Real.log 60) / 2 ≤ (143517086379753632624856890593981860170173410184829809244675016615735201344467570143410441594362891053077444554368746554992987705404229829836898403079568682451980822319807115831218719929971276845433031434835627641620634229491700889308620676308645951064267099610852088321736019 / 406762503775904156251152753043364833366078164227183700227073544380397836475406507918762935300622058850179991073264787739101233986354095146205683796280157464257532013140642970379531801589875643345861018500316163039976658551611389778022296861755355058922202839891237500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (270344607502913736928145503800195924955969707850801937859033809964684325120033708473219574169052622769848026779686851670534184824444053157199506912393325234290336975442382303066173437122099673498928990833322426734516475254486019927733344729199247839761619743231634965902126704006773261769528166599160282409470370312767145850390598798744000951851767152805729860881973877948992996990842942048346325917037541678255547329772193864000737163015924340986363574988343464219668000641743747750178693049232551486385338992897490812953739490618490303856481170222359741732722188658106151561319644400146144282619067347524664062090675540138285930720863434230912700980862213460927017967 / 829932331223359031961511217498945629422251328169868678648914250422610087150492746983392334010448798885871330140401662157948679360788461756892921150123834319165053023066079773739445302833571714969773720568313462299148948442620051745221620762547026174494843854380463486201078252868525242818204711721405417789275328231469510211752691222599512449306365180533575589418726146368439141090446525830136759415462521238321161802714303591403200049566403600798934601152185980788654070217423352510767411400081473451743085972880262470580339431762695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 60) / 2 * Real.cos (169 / 2 * Real.log 60) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 60) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 60)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 60) / 2 * Real.cos (169 / 2 * Real.log 60) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 60) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 60)) / (2 * (169 / 2)) ≤ (19467262562934595556178718222949441208965768322345600901795065246899672899821792415043861907931906842797310716348419876349660727657204964613983440263502667053534191140528191522455942287026191060264421034854443240451090828648520609857852090426172210957218943491109208239761538333951074095828533389475756365244492268037311844845458871210859774176334448620796724293252647805641859851718564542380712740097603567294858081698066276861990088986709635001889739246105349886684145558845329913415896405164905639254018130003626881494324671270985053801056581035648106479337326949499791709448539004669869257638951409671344640500407664331080303776947121597269987655224160224646622320137 / 59755127848081850301228807659924085318402095628230544862721826030427926274835477782804248048752313519782735770108919675372304913976769246496290322808916070979883817660757743709240061804017163477823707880918569285538724287868643725655956694903385884563628757515393371006477634206533817482910739243941190080827823632665804735246193768027164896350058292998417442438148282538527618158512149859769846677913301529159123649795429858581030403568781059257523291282957390616783093055654481380775253620805866088525502190047378897881784439086914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_61 : (3905124837953 / 500000000000 : ℝ) ≤ Real.sqrt 61 ∧ Real.sqrt 61 ≤ (7810249675907 / 1000000000000 : ℝ) := by
  constructor
  · calc (3905124837953 / 500000000000 : ℝ) = Real.sqrt ((3905124837953 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 61 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 61 ≤ Real.sqrt ((7810249675907 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (7810249675907 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_61 : (-3700108539451 / 100000000000000 : ℝ) ≤ primeTerm 61 ∧ primeTerm 61 ≤ (-3697999686029 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_61
  have hl := PsiOmega.Num.log_bound_61
  have hc := PsiOmega.Num.theta_61_cos
  have hs := PsiOmega.Num.theta_61_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_61
  have hqpos : (0 : ℝ) < Real.sqrt 61 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 61)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 61) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 61) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 61) = 2028 / 5 - 169 / 2 * Real.log 61 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (15572815116849968533786881011003496580208725400553448851852053124859977587052060552127509787050937518129925740765076477749232978376376668935620780037810313931961919681842282769768876173470624990316453461316142753075196641668075489060352921235400253380593243095538651500188709 / 45195833752878239583461417004818314818453129358575966691897060486710870719489611990973659477846895427797776785918309748789025998483788349578409310697795273806392445904515885597725755732208404816206779833368462559997406505734598864224699651306150562102466982210137500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 61) / 2 ∧ (2 * (12 / 5) - Real.log 61) / 2 ≤ (140155336259219103254210394175535688133050666027649631828867906697163464409386822062325691446490567659013244313657855136510966745430395590767147967339975251110911592763653041951186636200229785629809522116103374533510906001068485678804089857188156127756254403926202088321736019 / 406762503775904156251152753043364833366078164227183700227073544380397836475406507918762935300622058850179991073264787739101233986354095146205683796280157464257532013140642970379531801589875643345861018500316163039976658551611389778022296861755355058922202839891237500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-2333715468368425263482534449865302464515875440966066895774944487298378825711561108717738824658154051822483928520128460463505798993867631087567480415016256093750988961974567941647172233319924896987112620495454359010661743034047122492061285941380192346352798739929537722437892762411968759552046581678877364277768716329491098143489796810531512644941700936987021133018487828518234040934449862905232928399008513160778429873437651148140251782687573527682979008809417470915529991385453544122659478139910337955021860739227524635749525414122567873765329621886602729122779599219688034815860984053549721885720603306813488428470082048514636372330205117 / 33197293248934361278460448699957825176890053126794747145956570016904403486019709879335693360417951955434853205616066486317947174431538470275716846004953372766602120922643190949577812113342868598790948822732538491965957937704802069808864830501881046979793754175218539448043130114741009712728188468856216711571013129258780408470107648903980497972254607221343023576749045854737565643617861033205470376618500849532846472108572143656128001982656144031957384046087439231546162808696934100430696456003258938069723438915210498823213577270507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 61) / 2 * Real.cos (169 / 2 * Real.log 61) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 61) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 61)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 61) / 2 * Real.cos (169 / 2 * Real.log 61) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 61) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 61)) / (2 * (169 / 2)) ≤ (-647884828500436103834687485203052688275596358122328144628810185489290421365083377312622458089852725257594337916756957645130625728541651762907425590879671293635305054858238347049167656270582115401327884291570029510441393427852462028270677888131958794340731691986411338267987244444909490345597224194775662634342036670241064275131612406738129612833774225023850295061405096334448707851769827238067164374358859676671746118329139698183798460719172510046308530271763683573946880260278230645262864417011406947766494713698051571242255823606765634729393415008765624919159954427937509342178980314784271846929348107828423299965458535978309666148661583460676401412407899437 / 9221470346926211466239013527766062549136125868554096429432380560251223190561030522037692600116097765398570334893351801754985326230982908409921346112487047990722811367400886374882725587039685721886374672981260692212766093806889463835795786250522513049942709493116260957789758365205836031313385685793393530991948091460772335686141013584439027214515168672595284326874734959649323789893850287001519549060694680425790686696825595460035556106293373342210384457246510897651711891304703916786304571112016371686034288587558471895337104797363281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_62 : (7874007874011 / 1000000000000 : ℝ) ≤ Real.sqrt 62 ∧ Real.sqrt 62 ≤ (1968501968503 / 250000000000 : ℝ) := by
  constructor
  · calc (7874007874011 / 1000000000000 : ℝ) = Real.sqrt ((7874007874011 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 62 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 62 ≤ Real.sqrt ((1968501968503 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1968501968503 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_62 : (-1339 / 100000000000000 : ℝ) ≤ primeTerm 62 ∧ primeTerm 62 ≤ (41 / 4000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_62
  have hl := PsiOmega.Num.log_bound_62
  have hc := PsiOmega.Num.theta_62_cos
  have hs := PsiOmega.Num.theta_62_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_62
  have hqpos : (0 : ℝ) < Real.sqrt 62 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 62)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 62) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 62) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 62) = 2028 / 5 - 169 / 2 * Real.log 62 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (15205361216537493630302182119154581207750925922767513907271040341245596827910854883642610614455000586338702505740136007087292878658494306388075341485011369708427200805277405319720836674909729720006117837654158518142089339405442112590536306213926511411757186708808964000188709 / 45195833752878239583461417004818314818453129358575966691897060486710870719489611990973659477846895427797776785918309748789025998483788349578409310697795273806392445904515885597725755732208404816206779833368462559997406505734598864224699651306150562102466982210137500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 62) / 2 ∧ (2 * (12 / 5) - Real.log 62) / 2 ≤ (136848251170856037750527196835239965215217284111595911746435647248147226816561228654984415917857116332813867099554009601803699145941798846974069512306996217325813774916304198080813992801469731723004801537345847350740999898457796188502906589753970511514943061328552088321736019 / 406762503775904156251152753043364833366078164227183700227073544380397836475406507918762935300622058850179991073264787739101233986354095146205683796280157464257532013140642970379531801589875643345861018500316163039976658551611389778022296861755355058922202839891237500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-4040290833575703361103947683795249466142157477957436234013558490374592176117171041797445869044319833612909619765594223097112959203882870692927277854335045743886735687374087523444808402640916487353881603679395929763990239095590716871044811401201235237072057378624996756260612597303053282297226810910732562600199005937783824126909980480866343115844795307605712148087504634689808319659465339601547677055497620658052630704056493273407788050582564316767828098766485916839312297833162986507858308665747447951382936141112288542338757170492857925684195145598093609456164899204330101964703324590767963571547923478486150757170532209547394546802452216754215716421217073 / 12077104929243200341610808645767183471212794075397959075765018503044995117677793997913138213486655133396144521835982772724654632631987067825581778744873508100355000687211282984054491721815018026533270612247193091012725904039981130994006827859950516351016178005090674359250671883179533219928339701748415504542577083796925001832317374975529855136211920479160843961562585120095742474811363002374662892768720066499680423333692358448798768943618104106265449098314071027396917200784422348235492411187172888483373185923559685333462249134939270334143657237291336059570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 62) / 2 * Real.cos (169 / 2 * Real.log 62) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 62) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 62)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 62) / 2 * Real.cos (169 / 2 * Real.log 62) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 62) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 62)) / (2 * (169 / 2)) ≤ (-448868810409255254330767737346958907450947777900430262648146060453494716311392981400474438409886494530443492564843161089788465737316846532710131815909439109924728725160915387748945056882557479938711986581488541821069804816607053839393430477483641384991465164621528122594530061922539090899319038561650327571851701134858347946807391335350776066077357586640058670128025945437003754538241147193303770292404776287706187836069477841409203858036311247015922379491275352631062421550556857184307702482439869947984207752257139684403464431843583690896132708022232141522983694623911810009139518647743617121170154846234350904372193695780751649584041018568713120159060983 / 1341900547693688926845645405085242607912532675044217675085002055893888346408643777545904245942961681488460502426220308080517181403554118647286864304985945344483888965245698109339387969090557558503696734694132565668080656004442347888222980873327835150112908667232297151027852431464392579992037744638712833838064120421880555759146374997281095015134657831017871551284731680010638052756818111374962543640968896277742269259299150938755418771513122678473938788701563447488546355642713594248388045687463654275930353991506631703718027681659918926015961915254592895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_63 : (7937253933193 / 1000000000000 : ℝ) ≤ Real.sqrt 63 ∧ Real.sqrt 63 ≤ (3968626966597 / 500000000000 : ℝ) := by
  constructor
  · calc (7937253933193 / 1000000000000 : ℝ) = Real.sqrt ((7937253933193 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 63 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 63 ≤ Real.sqrt ((3968626966597 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (3968626966597 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_63 : (-272525110123 / 25000000000000 : ℝ) ≤ primeTerm 63 ∧ primeTerm 63 ≤ (-217896291869 / 20000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_63
  have hl := PsiOmega.Num.log_bound_63
  have hc := PsiOmega.Num.theta_63_cos
  have hs := PsiOmega.Num.theta_63_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_63
  have hqpos : (0 : ℝ) < Real.sqrt 63 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 63)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 63) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 63) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 63) = 2028 / 5 - 169 / 2 * Real.log 63 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (14843786831611102020067670826109708320380709532737383877462708773954860800340684541442989744758850058509453861595322154646171242974601843661379030106555293647931411734770389415744009109634989782700649974946538145340259395247229809245796077271029301876919124444557120893788709 / 45195833752878239583461417004818314818453129358575966691897060486710870719489611990973659477846895427797776785918309748789025998483788349578409310697795273806392445904515885597725755732208404816206779833368462559997406505734598864224699651306150562102466982210137500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 63) / 2 ∧ (2 * (12 / 5) - Real.log 63) / 2 ≤ (133594081719848160079541974614156527147357097653771747371934220139219136536860551455590294299911181889181050073582748129367115134107032414705519089500053725798212952192382144981377460281989921904128115695729493992462694474028512261934872765721263264796302049220137513550536019 / 406762503775904156251152753043364833366078164227183700227073544380397836475406507918762935300622058850179991073264787739101233986354095146205683796280157464257532013140642970379531801589875643345861018500316163039976658551611389778022296861755355058922202839891237500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-4064790826508168699540857517009955033521389257845129392385068476289554548435709155391985221667874368686482389292290943040409462426139276285980159702722905025665931166806789043322727155472785233405708547907075769599458668548953070461276511752326819064733586797195131228205430938313900920630076192157149795491356046730390013216624395144433814259400351064631416546998391623268030692746386311739228868186865532363994457655147966777401874290308574820914994330999966366669981876762681220936300132908696084584627564489403268782379673396986852230189341474777956483997625323268462382439850249222804445634682608277425022073846565988632971281984494037633462111002177311486201 / 59755127848081850301228807659924085318402095628230544862721826030427926274835477782804248048752313519782735770108919675372304913976769246496290322808916070979883817660757743709240061804017163477823707880918569285538724287868643725655956694903385884563628757515393371006477634206533817482910739243941190080827823632665804735246193768027164896350058292998417442438148282538527618158512149859769846677913301529159123649795429858581030403568781059257523291282957390616783093055654481380775253620805866088525502190047378897881784439086914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 63) / 2 * Real.cos (169 / 2 * Real.log 63) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 63) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 63)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 63) / 2 * Real.cos (169 / 2 * Real.log 63) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 63) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 63)) / (2 * (169 / 2)) ≤ (-56423371645451720444263502040882824589060704872745265254339374331227110082451827163917428532153735667544608641983660532220568663334687246010771103807787932043887827642713635504292805540822611384079109031998091471331624310725656033969813691276010288846062531688791961002965255832802567179297148535131010577174393693178244669483716357300028168764971950953083824606174849643558049826908745406663841778192238719988144948950593816819953650235923610680607471539392397682911439730320245356867069204363326414850883598024186159258475950587846354869109421439778854323082563848042928863712274793165377361950071192947259872971611120766828389590027937835113917933654509519853057337117821 / 829932331223359031961511217498945629422251328169868678648914250422610087150492746983392334010448798885871330140401662157948679360788461756892921150123834319165053023066079773739445302833571714969773720568313462299148948442620051745221620762547026174494843854380463486201078252868525242818204711721405417789275328231469510211752691222599512449306365180533575589418726146368439141090446525830136759415462521238321161802714303591403200049566403600798934601152185980788654070217423352510767411400081473451743085972880262470580339431762695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_64 : (8 : ℝ) ≤ Real.sqrt 64 ∧ Real.sqrt 64 ≤ (8000000000001 / 1000000000000 : ℝ) := by
  constructor
  · calc (8 : ℝ) = Real.sqrt ((8 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 64 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 64 ≤ Real.sqrt ((8000000000001 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (8000000000001 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_64 : (-2486633467849 / 50000000000000 : ℝ) ≤ primeTerm 64 ∧ primeTerm 64 ≤ (-497260685109 / 10000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_64
  have hl := PsiOmega.Num.log_bound_64
  have hc := PsiOmega.Num.theta_64_cos
  have hs := PsiOmega.Num.theta_64_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_64
  have hqpos : (0 : ℝ) < Real.sqrt 64 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 64)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 64) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 64) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 64) = 2028 / 5 - 169 / 2 * Real.log 64 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (29676781930815632195625676161235459148248413970494965869561153181604532481798819581889374408833033838280639033339823730551288686872417858317885296671397248230318294369421595218576103320721634363897102827354320515329821298894403634706141396392263206620613540343438606910506206482547 / 92578377530221987032689447748580754162767476474907914380248176450950273497000289878906597522210457197078693406069705078153711441852217830874470799075081976345359577519229963288326276704008248882636092295414791444035167530436154825297182945841446606851137624420548082662500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 64) / 2 ∧ (2 * (12 / 5) - Real.log 64) / 2 ≤ (267091037884644916917318835447982343695378843693117611568102188762941215719660036937198713504492799763825510423524604845104189229703664726753535099929253797884889688633405171266480644619693061323003821025434368593703247976795488723112626180284212369936201063482140540369187622207277 / 833205397771997883294205029737226787464907288274171229422233588058552461473002608910159377699894114773708240654627345703383402976669960477870237191675737787108236197673069669594936490336074239943724830658733122996316507773925393427674646512573019461660238619784932743962500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (7992074772540238796876741530445579044213812940253046024679675534372670834553024960829975145525272698752239629356499409450589366035654119677939582232423246170055440670531262220499455958737169095088851331399956019123657324476483056791329485837872367938836568917847850595846224232078624645364108951273353926084417979672805072297130899261636339438611411093467076691022074379763158853417119144927634169842116732517915071691326316842874859448474432801014768287111837282902660049695943542463107129811712612816534147393945606676359745808474328334556043110032236283690443792992454074535932670868031432773521301278172501730183873860035623118942452518219582135159175667621168267082818641389961 / 27858324716838336180139676648259760151266234843523266758311911507567557091192882470942084838249923410898080910861027982366819190070638243592440886421132374704348791366092023101512928029203110578964262355646121892753017708368684670304152345097670315857654831963850355265482050726384246285540736546566130823127379538173545131726576112827267545664171518610925083940810012984323484571253468560859118800352303143066201430193789108812894124123007481177084564271858530311003952900036187120406460517819323346432280285829060944806666151399112787246704101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 64) / 2 * Real.cos (169 / 2 * Real.log 64) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 64) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 64)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 64) / 2 * Real.cos (169 / 2 * Real.log 64) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 64) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 64)) / (2 * (169 / 2)) ≤ (287752883869193525315636222502103620909399678704992454255900493346496071782662027473556055997402068602960337462146480670279262236295586923383194535423140551040995260407920011970044974220047946949219349535559755544939722705431635919376390624030538253826514595503731777943974730020807833872802125426217378023523716569037310412376829051519628055955882381011041101690323757125718243894356510066271484158291653740556811178441808619029194844495987554213743070160165459142209560440700176612478018784270611674561530349121441591367340965135538166334025510610072155342948417632103264071176489098996809252678120352718768079215947823450184031939429188018484855016911352583 / 1002899689806180102485028359337351365445584454366837603299228814272432055282943768953915054176997242792330912790997007365205490842542976769327871911160765489356556489179312831654465409051311980842713444803260388139108637501272648130949484423516131370875573950698612789557353826149832866279466515676380709632585663374247624742156740061781631643910174669993303021869160467435645444565124868190928276812682913150383251486976407917264188468428269322375044313786907091196142304401302736334632578641495640471562090289846194013039981450368060340881347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_65 : (4031128874149 / 500000000000 : ℝ) ≤ Real.sqrt 65 ∧ Real.sqrt 65 ≤ (8062257748299 / 1000000000000 : ℝ) := by
  constructor
  · calc (4031128874149 / 500000000000 : ℝ) = Real.sqrt ((4031128874149 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 65 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 65 ≤ Real.sqrt ((8062257748299 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (8062257748299 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_65 : (0 : ℝ) ≤ primeTerm 65 ∧ primeTerm 65 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_65
  have hl := PsiOmega.Num.log_bound_65
  have hc := PsiOmega.Num.theta_65_cos
  have hs := PsiOmega.Num.theta_65_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_65
  have hqpos : (0 : ℝ) < Real.sqrt 65 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 65)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 65) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 65) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 65) = 2028 / 5 - 169 / 2 * Real.log 65 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (28959105711529463940346563907732174578007593279428347507267489827057124554571810015260721464279074393818203901477503532011326437229528299862471740553934518548921669957996790682746818410950013466058656439816019749896377951222819405548569526770449053796981772146619649311980815857547 / 92578377530221987032689447748580754162767476474907914380248176450950273497000289878906597522210457197078693406069705078153711441852217830874470799075081976345359577519229963288326276704008248882636092295414791444035167530436154825297182945841446606851137624420548082662500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 65) / 2 ∧ (2 * (12 / 5) - Real.log 65) / 2 ≤ (260631951934394830648716367196549352371313732032043320810307962452836806388735656453698961596276702976950061735422196033690315273080655819098196464235367455819878317799432429960395225113414916956656309664790668391132668302064550156559944499721930110511892938604846098819187622207277 / 833205397771997883294205029737226787464907288274171229422233588058552461473002608910159377699894114773708240654627345703383402976669960477870237191675737787108236197673069669594936490336074239943724830658733122996316507773925393427674646512573019461660238619784932743962500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (142856670251537215272501894569734046424600676832758504185322443159071042158579418594180263151963210830378093556460946114048936980149860099287384895260243615817323544929585886379032943744344644931945198466704207791144602794384186552672276338568600731882055089038399699390321900557143586220426453933182273601395127803586678034446967121387747647978997784540996835541117105010068564624566030028859590494094741880699605091520617472629078138541934272840279782175726345880405579898028719539910404035452716558532322460722305231004671507706585662552290832816328773297679163110801441277605589980322468768130723020327131820918692948437379874004762326054702384668156548417673859212112741 / 703805520284285501781790335580297125470331261151216463539334844011630823418395834044382072489849416719003403029319795030430395603784195969042757659158076590967458170125913943631554301272422247948378206972800244652035409580212335395727585341715245296292344492127953629215023251728584563391266999501217237672673630948478631977968085691303802823923825665156706942192260132093691445618420720086536039170629190647110222274169071695847331186365193721967559017984425390523128774274285183825528406937320327476812364032438809489644026835855098681721253583987163437996059656143188476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 65) / 2 * Real.cos (169 / 2 * Real.log 65) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 65) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 65)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 65) / 2 * Real.cos (169 / 2 * Real.log 65) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 65) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 65)) / (2 * (169 / 2)) ≤ (82300527381199614405830308095138423823178822386273312945463702227390075097123857196101394784128978365419601764884817822699468267301076192289483494528522429359176029845757768488762414130176659424573845841671407215353592692198645856745398074282479384984710755349674856216338969345226961268781976659489004265719353080649396763151823338059415359324991981822547718331062128012237810198975924068873450296942985218343322409843804389095322985303105617749012237355405782664150985014484614337630838930240476629404277676846089660191328319908991567217016877831236665292136915293264421239607357439663403419520058473788814342808961735558138588539924647885689218299977296065372721 / 405391979683748449026311233294251144270910806423100682998656870150699354288996000409564073754153264030145960144888201937527907867779696878168628411675052116397255905992526431531775277532915214818265847216332940919572395918202305187939089156827981290664390427465701290427853392995664708513369791712701128899460011426323692019309617358190990426580123583130263198702741836085966272676210334769844758562282413812735488029921385296808062763346351583853313994359029024941322173981988265883504362395896508626643921682684754266034959457452536840671442064376606140285730361938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_66 : (1624807680927 / 200000000000 : ℝ) ≤ Real.sqrt 66 ∧ Real.sqrt 66 ≤ (2031009601159 / 250000000000 : ℝ) := by
  constructor
  · calc (1624807680927 / 200000000000 : ℝ) = Real.sqrt ((1624807680927 / 200000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 66 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 66 ≤ Real.sqrt ((2031009601159 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2031009601159 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_66 : (-1423 / 50000000000000 : ℝ) ≤ primeTerm 66 ∧ primeTerm 66 ≤ (1933 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_66
  have hl := PsiOmega.Num.log_bound_66
  have hc := PsiOmega.Num.theta_66_cos
  have hs := PsiOmega.Num.theta_66_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_66
  have hqpos : (0 : ℝ) < Real.sqrt 66 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 66)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 66) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 66) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 66) = 2028 / 5 - 169 / 2 * Real.log 66 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (63513936516487657513403287480906365634071221943557172154939654353564393986716663397560679514112857974431946420397081062445842649067267536897164878014236773561749945577260924690828459667932688970890454575290191762948580664146966030892784566863551686474673969165470293642192871489508692777 / 208124617320294277050305853278554656206530098955952208147006503245793251296144878674161011730303628930637836937944649358851655309024994235628419933163500115284215757984783207398816707721790608238814255364491333912212463808665745737357169305899643543842580833221214359700822287500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 66) / 2 ∧ (2 * (12 / 5) - Real.log 66) / 2 ≤ (571625429889847762886730476063594035479831296881145823931907946269358177269100441880275670473434839937151442882892742014843897512958205872598059823620606897711072589873043744612286291930954572019585530123417513125975711720445671640934201689973270472749419999874104578677137870795579558207 / 1873121555882648493452752679506991905858770890603569873323058529212139261665303908067449105572732660375740532441501844229664897781224948120655779398471501037557941821863048866589350369496115474149328298280422005209912174277991711636214523753096791894583227498990929237307400587500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-11670146211291738102946648631565288545937879648056057049224372955205034358792880866950285117669732999834464520415950924477317763116111474812462121473861587361293149669458421826969424066418480091567949872306830706439929842843008256273267317390890026222277028239733642984798512132340932246559356815456780160005879059824394095573850682982672861568354994582994058329970149145840840981599098751902797715070308686376820480898183983377521290646248247089841344370181393779796414711864801061290895730762230066985437890086600866913679323294668840371810244933239945301652863679887248214409662289248717594267480019552094836939460810167255488245721860465206627541392696837122858518990012039 / 70396776732038767294665118017584557846466422560789416565340439389473089692388299450883300300564563861439676219119201206693708298607254550085380060688123958483289833968764100920079845872120374588459504749076647884173597396926426114646531203511503391032039373516607825553565647745874273075570739393184341800906042697775361572268460306374661169170619414054913550228716495607825369135567004239919444551479714534156892526704795923038993295081029115404882686591909689103848766207420957464187945007179169941613698351395519403226717363433271646973872061390876770019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 66) / 2 * Real.cos (169 / 2 * Real.log 66) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 66) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 66)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 66) / 2 * Real.cos (169 / 2 * Real.log 66) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 66) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 66)) / (2 * (169 / 2)) ≤ (-324099186884369929516483483995089602098212143118230519010788631766617150882146971597472660964415603821006287640802079750718333823961343456899500040551738200053060168763969609716442909516060134335198388512362257169370500806162672531032566755152053311485070881277486921992955039020437015359779396406742719464481887398574861032826624009176964410601336013154739420275101203509615668599563852092442110095655588713969795075318542212835547466263275659604536996263805477922338573081884265447142248128024455035446311362199807002884962823940154010453742263602050777394154703127277316778197363213718579006345943107795272300657118192302868322041710988384221220315927380103627962322121593514188450125840443079151 / 1955466020334410202629586611599571051290733960021928237926123316374252491455230540302313897237904551706657672753311144630380786072423737502371668352447887735646939832465669470002217940892232627457208465252129107893711038803511836517959200097541760862001093708794661820932379104052063140988076094255120605580723408271537821451901675177073921365850539279303154173019902655772926920432416784442206793096658737059913681297355442306638702641139697650135630183108602475106910172428359929560776250199421387267047176427653316756297704539813101304829779483079910278320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_67 : (255792274121 / 31250000000 : ℝ) ≤ Real.sqrt 67 ∧ Real.sqrt 67 ≤ (8185352771873 / 1000000000000 : ℝ) := by
  constructor
  · calc (255792274121 / 31250000000 : ℝ) = Real.sqrt ((255792274121 / 31250000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 67 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 67 ≤ Real.sqrt ((8185352771873 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (8185352771873 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_67 : (-4150928515209 / 100000000000000 : ℝ) ≤ primeTerm 67 ∧ primeTerm 67 ≤ (-1037602395681 / 25000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_67
  have hl := PsiOmega.Num.log_bound_67
  have hc := PsiOmega.Num.theta_67_cos
  have hs := PsiOmega.Num.theta_67_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_67
  have hqpos : (0 : ℝ) < Real.sqrt 67 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 67)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 67) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 67) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 67) = 2028 / 5 - 169 / 2 * Real.log 67 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (61949060276584282805959936724054539860021307176547537210101386741869424032907113807012536603815179547181526148508437981514543540240693811165937203157929056612016195837088209768489887119929330510855282700136189291724344179121198133337385985198185137891303128541694506058367869927008692777 / 208124617320294277050305853278554656206530098955952208147006503245793251296144878674161011730303628930637836937944649358851655309024994235628419933163500115284215757984783207398816707721790608238814255364491333912212463808665745737357169305899643543842580833221214359700822287500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 67) / 2 ∧ (2 * (12 / 5) - Real.log 67) / 2 ≤ (557541543775729805002230277747679164002971748266470710284610882020711544244391806734079665857545835836530196939779316545242501746497840256360201213457049208040414394182756876833397659670159578149280767973094926885871576195842929533090870660929500927871092302497862425330994920795579558207 / 1873121555882648493452752679506991905858770890603569873323058529212139261665303908067449105572732660375740532441501844229664897781224948120655779398471501037557941821863048866589350369496115474149328298280422005209912174277991711636214523753096791894583227498990929237307400587500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-43999175811191077844659332480038751729012839022336608712263911557102909795149038957360167215075973545429853799215216442272911781926864805282587695430389753727988096243858050441179237610898328037072228563344084365512584034838369397593123084946441352679614095711825317236485116067455194586336942953498056953629376895191804116153251705198766812576588191108421065229491118492447685341359500797585968997527410194663713528974973435048720287115276423630051938313159903062821664331200647505053908077023731541544059266716729569465188316227301983356170485818381091093656018600872642875440553438793593509756808332081262001905795847188935592205055946641009130667777236449630411725171780623636128103123531 / 154680417624108619543941909706606694486864698009547057882828113892885206843626634535632251636982684265858663567400588588926605148306955798527446422410428619714259889091522682685722317590108244945345591489670368886123627092855916755815132038965705693185633389074577741694846393972868275800814612924477313527381441474604065954691441102874011358040911798460503406264269643669538164604517343300604248282059919630715828305747842604333725501887026864903306684406051562972323949186227689740647340103665168328741036416640545563730580144262559771182824353642063215374946594238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 67) / 2 * Real.cos (169 / 2 * Real.log 67) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 67) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 67)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 67) / 2 * Real.cos (169 / 2 * Real.log 67) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 67) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 67)) / (2 * (169 / 2)) ≤ (-1222046534015363803268274903205574228881856656037073063429273030644610375170864386935627821691343808769110820046495744535185205027016507721982285453155740256302570474038176743266845574967746466424169764980132066794086756663391053996900835794701386926026381989393048816951535392568969722997225482631288104645745246021742865157729038722502958480484317613501314984883389114877981935132662655212811771360697100373822146935371820930778623166433093981299640827052282535555023244653471919825366461359313432257913400367236918129242926474346958621823285282253951872314603680692773446226022921819092121799773358421759439449498538866719582663399197451696461124023854385269678817111110196209095184956103 / 4296678267336350542887275269627963735746241611376307163411892052580144634545184292656451434360630118496073987983349683025739031897415438847984622844734128325396108030320074519047842155280784581815155319157510246836767419245997687661531445526825158144045371918738270602634622054801896550022628136791036486871706707627890720963651141746500315501136438846125094618451934546376060127903259536127895785612775545297661897381884516787047930607972968469536296789056987860342331921839658048351315002879588009131695456017792932325849448451737771421745120934501755982637405395507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_68 : (1649242250247 / 200000000000 : ℝ) ≤ Real.sqrt 68 ∧ Real.sqrt 68 ≤ (2061552812809 / 250000000000 : ℝ) := by
  constructor
  · calc (1649242250247 / 200000000000 : ℝ) = Real.sqrt ((1649242250247 / 200000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 68 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 68 ≤ Real.sqrt ((2061552812809 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2061552812809 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_68 : (-369641721 / 195312500000 : ℝ) ≤ primeTerm 68 ∧ primeTerm 68 ≤ (-188709239909 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_68
  have hl := PsiOmega.Num.log_bound_68
  have hc := PsiOmega.Num.theta_68_cos
  have hs := PsiOmega.Num.theta_68_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_68
  have hqpos : (0 : ℝ) < Real.sqrt 68 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 68)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 68) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 68) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 68) = 2028 / 5 - 169 / 2 * Real.log 68 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (60407368243071032989277899812765730852210426218040990016893011431721029036570114549509996538616411059179834738586560401760833181044515474781788461248069396241072715697563482532294273346929134396049394682098159856178130408737156840187446318080684674325719425786919736171643487233258692777 / 208124617320294277050305853278554656206530098955952208147006503245793251296144878674161011730303628930637836937944649358851655309024994235628419933163500115284215757984783207398816707721790608238814255364491333912212463808665745737357169305899643543842580833221214359700822287500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 68) / 2 ∧ (2 * (12 / 5) - Real.log 68) / 2 ≤ (543666315515885988642525936538889949696922987784208076012218591124242113599224280580885424153700591251361406362222161662334928991519939832854980072453363754843304464862743456138091819327045268384226162606463098599958905967277030049553921306904969410842423563418815796669507757995579558207 / 1873121555882648493452752679506991905858770890603569873323058529212139261665303908067449105572732660375740532441501844229664897781224948120655779398471501037557941821863048866589350369496115474149328298280422005209912174277991711636214523753096791894583227498990929237307400587500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-101102473012000219634540313506059569058848192494688890830083099606120829853621809000027571683010141751403430791139316741038886989821167194130137756738096423857899170193657601620323497745229928925282266347296030006177334295969762895477476563118518486642927192341947876599946037254696808343437950404962769079735646700939058793048081370196040410440455754361252212331250302259613169024370496340087012411710132078007765461578809342012220074822471590561144175276772762856093035155776606255699760152461561859520380829493144382186183397226734833971255963581020704306310399861326058368815209219877615906408131213689786805966652343814947930815625258203114702943803243513862100516003593722841 / 8391949740891309654076709510992116671379378147219349928538851665195594989346063071594631707735605700187644507779979849659646546674639528999969966493621344385539273496718895545015316709532782386357725232729512200853061365714839233713928604544580387000088617028785684770770746200784954199262945579669993138421302163335724064382131136223633428713157107121338075426663934660890742437311053781499796456274952236909495893323993196849702989468697204042063079666126929414731117034843082125686162114999195330335342687534751820948924704007300334808095939325198742153588682413101196289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 68) / 2 * Real.cos (169 / 2 * Real.log 68) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 68) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 68)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 68) / 2 * Real.cos (169 / 2 * Real.log 68) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 68) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 68)) / (2 * (169 / 2)) ≤ (-350035032624992748407246836028477002111363637707356836309720968868464173001667659262057460840374587589900662940151285113650759040349881112717159108589434512083777814157579268413291502482022008026565756048695761918115545769227463802017340765818610628893437580796537865221026609130447971236920273276195055198528571762409739993750859257098843709746646323602975321724830500906318685475498140753350252772744154108246738275884712277419681148374488562319402767362483120053001261589459386724737803866007936196923533132075482049232658247141786423469765553775997728847420877324193826446327193280546782584062426908728694619319190907815189043690899653170444992504955738705294967014242666707707541519233 / 29138714378094825187766352468722627331178396344511631696315457170818038157451607887481360096304186458984876763124930033540439398175831697916562383658407445783122477419162831753525405241433272174853212613644139586295351964287636228173363210224237454861418809127728072120731757641614424302996338818298587286185076956026819667993510889665393849698462177504646095231471995350315077907330047852429848806510250822602416296263865266839246491210754180701607915507385171578927489704316257380854729565969428230331050998384554933850433000025348384750333122656940076922182925045490264892578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_69 : (4153311931459 / 500000000000 : ℝ) ≤ Real.sqrt 69 ∧ Real.sqrt 69 ≤ (8306623862919 / 1000000000000 : ℝ) := by
  constructor
  · calc (4153311931459 / 500000000000 : ℝ) = Real.sqrt ((4153311931459 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 69 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 69 ≤ Real.sqrt ((8306623862919 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (8306623862919 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_69 : (-14382245625279 / 100000000000000 : ℝ) ≤ primeTerm 69 ∧ primeTerm 69 ≤ (-14380354432823 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_69
  have hl := PsiOmega.Num.log_bound_69
  have hc := PsiOmega.Num.theta_69_cos
  have hs := PsiOmega.Num.theta_69_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_69
  have hqpos : (0 : ℝ) < Real.sqrt 69 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 69)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 69) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 69) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 69) = 2028 / 5 - 169 / 2 * Real.log 69 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (151422307225479052676090201474347542896619327079020682748469195621065457402265229933775661256327805502441024163038619810201656660651508048558212693482874455679503622783853688832041448696771171462995136867721081294556731526916803322789630740236854442699958855614590068780834794706780345698217281 / 535161859120390650176135106745371350900629789540684578275429613140580214100096022213439939995751427161682393923894787962831280433827346002765844480399765511936414041941446254694569537850549445866699751974250884929169255451804091298990569366232966125390251753245869207459788491429987500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 69) / 2 ∧ (2 * (12 / 5) - Real.log 69) / 2 ≤ (1362800768544506594097479128537857722078000124971851518069221384388800952347756174059347503308360666202482840366813680108635249645710033722771856365453463157633324602936388455644413100366860075289451636623425373884513554499260640616073301746444222423477834232396601840715427077951557483734244071 / 4816456732083515851585215960708342158105668105866161204478866518265221926900864199920959459961762844455141545315053091665481523904446114024892600323597889607427726377473016292251125840654945012800297767768257964362523299066236821690915124296096695128512265779212822867138096422869887500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (995389291478057789091078696823104032714814724318077372625943985883388934716056428806373060600840615437470117096778911890991788244498196373176071984626085183888515076326843426839877641160343960380508649467842910102765778578662895422968467038539818263663390965368662246942498849447503159576684956318751725603679055805522636835591804211929025599805990270311503263627223465989034062441557427422896458464253648076327257296177741478304855381751383367382517497519309021584779888236189368571602982659020203567852560201518557721276701756276220273942087556216649778127851621956679800723894148519219338332254145600789073111935612925085930208121076447658394009474490440070990250681403614050378978808717186802131 / 3812993992773277579750103134240809988696920491230777837084020508617327901717440649411451219791893462866557965098814855667129799349860029613463766703211709666357640396834068351639863434354232734606692044566191754725049586444807717773451897918073185450638451074419752211717053674258257540105474440208135602412799084386751819862493111517935293395724172830435125030493146669481869817059094069911946727721701695674222464897621560340341616876915454196335342412931750571796990890537524859788448386793999140107409662154603753342736078298848210709076803656210352949006289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 69) / 2 * Real.cos (169 / 2 * Real.log 69) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 69) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 69)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 69) / 2 * Real.cos (169 / 2 * Real.log 69) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 69) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 69)) / (2 * (169 / 2)) ≤ (895968177307171403533232752068429248559047256694848413585146708940616291142411861557805911026013141489652634622375982835208135455579805662081228489589146554308016049895884072313870641709561030490200354593592543857005625201696810507266197419782757858162137120368725118735339977496731568299286900789276463510156054364168432304616535323284663598344870991258233828933471026145542809671413971196432901957958582681065128693014532413128336597821212598870451005476753065065541531329595376661228861165858871754666900236179232742845389739039699824016127669855160532232986964567174139314315932459751006851917656532760889971665538191918160639353362545803666631428863837226387197229736681613 / 3431694593495949821775092820816728989827228442107700053375618457755595111545696584470306097812704116579902168588933370100416819414874026652117390032890538699721876357150661516475877090918809461146022840109572579252544627800326945996106708126265866905574605966977776990545348306832431786094926996187322042171519175948076637876243800366141764056151755547391612527443832002533682835353184662920752054949531526106800218407859404306307455189223908776701808171638575514617291801483772373809603548114599226096668695939143378008462470468963389638169123290589317654105660156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_70 : (418330013267 / 50000000000 : ℝ) ≤ Real.sqrt 70 ∧ Real.sqrt 70 ≤ (8366600265341 / 1000000000000 : ℝ) := by
  constructor
  · calc (418330013267 / 50000000000 : ℝ) = Real.sqrt ((418330013267 / 50000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 70 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 70 ≤ Real.sqrt ((8366600265341 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (8366600265341 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_70 : (0 : ℝ) ≤ primeTerm 70 ∧ primeTerm 70 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_70
  have hl := PsiOmega.Num.log_bound_70
  have hc := PsiOmega.Num.theta_70_cos
  have hs := PsiOmega.Num.theta_70_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_70
  have hqpos : (0 : ℝ) < Real.sqrt 70 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 70)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 70) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 70) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 70) = 2028 / 5 - 169 / 2 * Real.log 70 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (396322584613532497564879508594344139912077257305650087722142269083853680086567606554927105605230474889681389107019535419235628330625622715761316017330604257260515886156751843275820317223782411459615559173464011849438442208339202161390221488991902022267732267472939709133092333640801380817138095981939 / 1437240856929044417535381789242397462034398474756463776423481002212991894011285779080836358211449952062530309087496396553950980527414963144602004487606737854401160342904744949086575147672654752259080321197335687332590606657218651870303753910773212252704442523300418015068949708565711599762500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 70) / 2 ∧ (2 * (12 / 5) - Real.log 70) / 2 ≤ (3566903271211566283793049313722546802758584302263970179420073258832625450252934690926351284441755056834046488418867876291240233501063030205403871891947088247538404676232138655737944980118238644298129661626660594304250307551724745346534096474750803235241756035499298750636727013309440471558876827714949 / 12935167712361399757818436103181577158309586272808173987811329019916927046101572011727527223903049568562772781787467568985558824746734668301418040388460640689610443086142704541779176329053892770331722890776021185993315459914967866832733785196958910274339982709703762135620547377091404397862500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (154103429982027936558702904147556516801089354842521204170075804042751600844576141973495534073824480526167674565979651363661397402984957599846579590564523893074494308016492920335132850478918867824052017347265604549156868023075753603403273771796889892623666426124205698977054335245155024022351541645442998079661491032434702976645360802278270071235134833133362606444404748165567332707425904344068388017392663581705557262939399758387512283279426578942849613892183905441070131733876411512207328788352889900708314247217915509071655982791922428083225849638394113598160699274587663437715595002792458473472715796549611600337860617899889438043666338379489813296738387383309086466523155518583903297983821378518917453500488778134897526607 / 839276354521585738609288474667290676551308622195874711165829986049755770906007020262189002543438684818823998902143780719560118086488300656618596563714179327637674266007514247189705188155084330962643828191507983378990272327243763584667791622139295391169808460375616264441127542311014839869572238029988812923594520622835234250249434667757846994253562673790802044646148902630730034697221904321341140074836847401715449567636209319378420417476271140490425073155361673710901270897585684671527777672662220464417607949249529175617648121229864786742150143636401378037353391596457148790359497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 70) / 2 * Real.cos (169 / 2 * Real.log 70) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 70) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 70)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 70) / 2 * Real.cos (169 / 2 * Real.log 70) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 70) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 70)) / (2 * (169 / 2)) ≤ (11097483697553338720694971024266300322590508688222534820724666812007101687242360010755659805518317184362809890244813452862173860781982145047739932902146145467293901431992456565479159135106873836412761142906852378778428472293241069019544411885594138265663047967050109402154490800843723344435545936254986015777322868544572455251019508662246457361100575125423916390690815519886503663709022262712669128542219851264066810437877533717938358013592627371932741206721801029033343364787240441834607625708147975486239955628343312396973120435290233309758981431241259615608289023221377187631718202383662189360125381729967612185639776993289044837291965398590639671751740519847520535622888365972556534107985075420054724953345323001 / 60427897525554173179868770176044928711694220798102979203939758995582415505232505458877608183127585306955327920954352211808328502227157647276538952587420911589912547152541025797658773547166071829310355629788574803287299607561550978096080996794029268164226209147044371039761183046393068470609201138159194530498805484844136866017959296078564983586256512512937747214522720989412562498199977111136562085388253012923512368869807070995246270058291522115310605267186040507184891504626169296349999992431679873438067772345966100644470664728550264645434810341820899218689444194944914712905883789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_71 : (1053268721647 / 125000000000 : ℝ) ≤ Real.sqrt 71 ∧ Real.sqrt 71 ≤ (8426149773177 / 1000000000000 : ℝ) := by
  constructor
  · calc (1053268721647 / 125000000000 : ℝ) = Real.sqrt ((1053268721647 / 125000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 71 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 71 ≤ Real.sqrt ((8426149773177 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (8426149773177 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_71 : (-1507604628441 / 25000000000000 : ℝ) ≤ primeTerm 71 ∧ primeTerm 71 ≤ (-3014376608859 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_71
  have hl := PsiOmega.Num.log_bound_71
  have hc := PsiOmega.Num.theta_71_cos
  have hs := PsiOmega.Num.theta_71_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_71
  have hqpos : (0 : ℝ) < Real.sqrt 71 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 71)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 71) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 71) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 71) = 2028 / 5 - 169 / 2 * Real.log 71 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (386129216117367624073707456300678626166937079314479858766656595777187187760977239148916940373420684694671844428087398847369652550521790455366482196778432131329210301676085495583915182331144367813558380795492296804637403586500389535710099667449361129987810414259870121880984078787241982244325595981939 / 1437240856929044417535381789242397462034398474756463776423481002212991894011285779080836358211449952062530309087496396553950980527414963144602004487606737854401160342904744949086575147672654752259080321197335687332590606657218651870303753910773212252704442523300418015068949708565711599762500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 71) / 2 ∧ (2 * (12 / 5) - Real.log 71) / 2 ≤ (3475162954978194824418836244430928103170953149427599598419500595211749655736830756551397539714710288397147409371713226255373793841923984734001536554499042296910998409485195827031268244918493971961834464054838155329301453205103680572669605842452289341830957775362409651891991115121934060908876827714949 / 12935167712361399757818436103181577158309586272808173987811329019916927046101572011727527223903049568562772781787467568985558824746734668301418040388460640689610443086142704541779176329053892770331722890776021185993315459914967866832733785196958910274339982709703762135620547377091404397862500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-95411117646300878362694459207027297223621286114066311996913377114769047875975458671258992123986444565963609931999265850257408035428544833239290997703315748432594922261706644613556180717904316363484862992641410415753506531487493090147131209620360184380832266975091050840365291027877930665369588335778845984948997064278460248260017483135724365962401697157497491107513501354693910457521564551616693653085686338868171342520818939067526718756954618519364751127976565736304131018027345959862961239159297981961174854471829946797638868546276274965430122552676990219387485873604091998180250446079563790261050878043206205185449112274109780912382981430720051224570021014718817328038597928750743677285094737 / 800396303674302805527962183635035206366833326526522360959844575929408808618552227270306589644850430315803526785033970565376394354332256943338963092531375243795084253318323371114449680476269083941119983855731948260298034980052722534816543218745513335389908275962463631096961538611426200742313612012852490352243919966540560007333216350324484819654047654906084103246830847388010058114263443299618854594075057412829827849994859046343250672794600620737481187014924691878224631211839375182655122444784374679963691663026360679261825677137245928518438476215745332753518478008706234732017037458717823028564453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 71) / 2 * Real.cos (169 / 2 * Real.log 71) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 71) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 71)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 71) / 2 * Real.cos (169 / 2 * Real.log 71) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 71) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 71)) / (2 * (169 / 2)) ≤ (-165598558965668545093783799840439628484211313816301074404236197787633559719014100724377828609650721221676037168769655721307646406042481793653174937754432114429190428782108295332186428132990449286575744477689860253261043424467121265546010845678110500472841617101562708997254557892460390072155499119346855655905623955252983051974294693885021378527360558649179620797699071977769868452792528070082871306431678193379835303622274226557754955146989095563600680041698643225114743321645252811256244999259253227510721185047536859893001328157442515728640345492467691461315605679222924689735286064641208227899148181539830093724688024994379656435913478258237911648949308308976738838458942863213599755053492871673861573434113303337 / 1389576916101220148486045457699713899942418969664101321110841277655223626073875394566504495911198663742714456224017310009334017976271279415519033146755859798255354606455422519295919584160189381842222194193979076840795199618147087734056498643655405096163035201323721581765558226755948265177627798633424462417090138830799583346064611719313341700788277178656396012581303554493073017559485144617393844781380308008385117795129963622123699084712848299891460394123133145621917762520554470803220698688861761597159186914976320623718447356141051959233400132319002313808191802098448324187529578921385109424591064453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_72 : (4242640687119 / 500000000000 : ℝ) ≤ Real.sqrt 72 ∧ Real.sqrt 72 ≤ (8485281374239 / 1000000000000 : ℝ) := by
  constructor
  · calc (4242640687119 / 500000000000 : ℝ) = Real.sqrt ((4242640687119 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 72 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 72 ≤ Real.sqrt ((8485281374239 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (8485281374239 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_72 : (-582019217017 / 12500000000000 : ℝ) ≤ primeTerm 72 ∧ primeTerm 72 ≤ (-1163894435491 / 25000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_72
  have hl := PsiOmega.Num.log_bound_72
  have hc := PsiOmega.Num.theta_72_cos
  have hs := PsiOmega.Num.theta_72_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_72
  have hqpos : (0 : ℝ) < Real.sqrt 72 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 72)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 72) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 72) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 72) = 2028 / 5 - 169 / 2 * Real.log 72 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (376078416897642319776798179667920046407237981702953338801938455782954704713141434777139203722995618348967627119802450555138902176016055248362000471021908838901101914386425524377788830720489377086479315330089484662692761391685301782617240672425339971251122836615307770742381664251598898457997470981939 / 1437240856929044417535381789242397462034398474756463776423481002212991894011285779080836358211449952062530309087496396553950980527414963144602004487606737854401160342904744949086575147672654752259080321197335687332590606657218651870303753910773212252704442523300418015068949708565711599762500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 72) / 2 ∧ (2 * (12 / 5) - Real.log 72) / 2 ≤ (3384705762216995275009070859826032554222927639301921553305702858741216659905341029618539008594762865052152910621898597261128395256875949667747632055290506628377475593162835310347705953850089419471272004340309584253642546153851443790246821106366798446064434947204792173661021221347906495258876827714949 / 12935167712361399757818436103181577158309586272808173987811329019916927046101572011727527223903049568562772781787467568985558824746734668301418040388460640689610443086142704541779176329053892770331722890776021185993315459914967866832733785196958910274339982709703762135620547377091404397862500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-1282591719553071387879997757544794602138005591970034062419189777829316823676297489253932745267183115730318775168063025741840716995524955589819911915772137127966270151656273817333612300558389340653122996234727667533700790388376517660520915918631051072506582878672689009182973678659488672259255786977034022067202506648923656629004440868864748432826937477979922450425112095774860121815207146354190520921880420869380139720198350972196878500138492978960834831783357953868691340387408715950336039985923651377045522405968698721952514129156144540455405278247710589291833431394613746621070308324240899299976945921958020994413584412472014514256240295376560515206693289739128248188959805784028956692718270813571 / 4950253365293397866894849652821600560061990567780596056386745056918111478188646847191253662361811788345780463284580533191338270902448754464894070995961521077445635862736160833344206728983844604257104333192280047885295583851442256125630955257366877648013411053325874875577236115160520169112305757238001215938462145318431692064191225534756043455386133505059860251813701303452677119852542124944307166035005686818694133257814595255930574443175241491686244783487880438348586312058975788756991999380003215232046511910581542964795036854562837679754019663201968063995039268449887413281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 72) / 2 * Real.cos (169 / 2 * Real.log 72) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 72) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 72)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 72) / 2 * Real.cos (169 / 2 * Real.log 72) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 72) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 72)) / (2 * (169 / 2)) ≤ (-890578511920617003021545833768009972987449300888723854562852689538895765760326143591943052493824283382575696504921350875601580171715843236180616442524328018535572116194398929533472805611506653368827850365282183580613683840752685395990276519165154905197081077057388945253181622428699520751762726170605311230269163623195315492924129674359934267912832998376282525553394182699583404734329814502216943019786648263685904915340298416228715466272438212873615580869334328671519467055848075050788055509061999123823897152858491857672427687905688372465096244389225460685679237685765731303033090577955863076780139172751020420490672178875298943209215945346515466964299813459053516954795696006706847291375976581167 / 3437675948120415185343645592237222611154160116514302816935239622859799637631004754993926154417924853017903099503180925827318243682256079489509771524973278526003913793566778356489032450683225419622989120272416699920344155452390455642799274484282553922231535453698524219150858413305916784105767886970834177735043156471133119489021684399136141288462592711847125174870625905175470222119820920100213309746531726957426481429037913372174010029982806591448781099644361415519851605596510964414577777347224455022254522160126071503329886704557526166495846988334700044440999491979088481445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_73 : (8544003745317 / 1000000000000 : ℝ) ≤ Real.sqrt 73 ∧ Real.sqrt 73 ≤ (4272001872659 / 500000000000 : ℝ) := by
  constructor
  · calc (8544003745317 / 1000000000000 : ℝ) = Real.sqrt ((8544003745317 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 73 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 73 ≤ Real.sqrt ((4272001872659 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (4272001872659 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_73 : (588164068879 / 50000000000000 : ℝ) ≤ primeTerm 73 ∧ primeTerm 73 ≤ (117677511819 / 10000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_73
  have hl := PsiOmega.Num.log_bound_73
  have hc := PsiOmega.Num.theta_73_cos
  have hs := PsiOmega.Num.theta_73_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_73
  have hqpos : (0 : ℝ) < Real.sqrt 73 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 73)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 73) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 73) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 73) = 2028 / 5 - 169 / 2 * Real.log 73 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (366166253819014835320963636653745522829570695150570181990383852914509688851616103106187661881052834398987596857688644985176014108158724959975324061236393696199916844058432968234035697045170917390936708281076429224570711350910847822749791334211436628466359368875698130188686345636238806654019345981939 / 1437240856929044417535381789242397462034398474756463776423481002212991894011285779080836358211449952062530309087496396553950980527414963144602004487606737854401160342904744949086575147672654752259080321197335687332590606657218651870303753910773212252704442523300418015068949708565711599762500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 73) / 2 ∧ (2 * (12 / 5) - Real.log 73) / 2 ≤ (3295496294711162574351762983253885967828784327290370074365176403999567545921178469315481563880625753557991285191414766640074301643118377435699824238592536956570473167686701290182630077990053792439255521165262001345750806331297941455222395752304625037345830248431052700896917005364480368857676827714949 / 12935167712361399757818436103181577158309586272808173987811329019916927046101572011727527223903049568562772781787467568985558824746734668301418040388460640689610443086142704541779176329053892770331722890776021185993315459914967866832733785196958910274339982709703762135620547377091404397862500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-553868776624182495107378497931832442375708885906989336391689056815699857322584631511780710995477078943567002836997365787818877556719591285769099417838839643903069887380934017650644885975786103285403972373752372647828133716028069622940746040067491336140977316697765327783113544855626749919473956729989966227798873334958324220952493791957783832932916311089939057555043959522869734104491463376704811057453778886103686422387043574266192564862050687390183689032966703925114204732600808204122180921865446218325690100270871090390186425345640811472938371002642966834479132113881012190983978956461348312316415090000402691928282165762866960279078663998904729259062315056716947517039192399093492124267794574322720358778835969 / 6714210836172685908874307797338325412410468977566997689326639888398046167248056162097512020347509478550591991217150245756480944691906405252948772509713434621101394128060113977517641505240674647701150625532063867031922178617950108677342332977114363129358467683004930115529020338488118718956577904239910503388756164982681874001995477342062775954028501390326416357169191221045840277577775234570729120598694779213723596541089674555027363339810169123923400585242893389687210167180685477372222221381297763715340863593996233404941184969838918293937201149091211024298827132771657190322875976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 73) / 2 * Real.cos (169 / 2 * Real.log 73) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 73) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 73)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 73) / 2 * Real.cos (169 / 2 * Real.log 73) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 73) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 73)) / (2 * (169 / 2)) ≤ (-7689699973032941486296703989225233227337000458489265429166070389158527860882344950888077182577836348099442279325109423753990887008488597749233635901986340191782854532415802442517503287646967781062597469941757744796617830592184625706573445985323576143281792292587214068321108411288765908261996290997482080599313110553610801704517509346179467281510419751744774854505666496425431122587922787292755804068071227717317683396998231308938989110542957150170355275556317420463454785526020811917261584566469084202616696690006450518618521835124660693967616921665062126444677102439854710217864082349268341828890996636527215952554185396907777799199812514643779137342553520328885704493654247455402305759391481796962952132191301210427313741 / 93252928280176193178809830518587852950145402466208301240647776227750641211778557806909889171493187202091555433571531191062235342943144517402066284857131036404186029556390471909967243128342703440293758687945331486554474703027084842740865735793255043463312051152846251604569726923446093318841359781109868102621613402537248250027714963084205221583729185976755782738460989181192226077469100480149015563870760822412827729737356591042046713052919015610047230350595741523433474544176187185725308630295802273824178661027725463957516457914429420749127793737377930893039265732939683198928833007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_74 : (4301162633521 / 500000000000 : ℝ) ≤ Real.sqrt 74 ∧ Real.sqrt 74 ≤ (8602325267043 / 1000000000000 : ℝ) := by
  constructor
  · calc (4301162633521 / 500000000000 : ℝ) = Real.sqrt ((4301162633521 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 74 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 74 ≤ Real.sqrt ((8602325267043 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (8602325267043 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_74 : (-2425274746367 / 25000000000000 : ℝ) ≤ primeTerm 74 ∧ primeTerm 74 ≤ (-2424856068549 / 25000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_74
  have hl := PsiOmega.Num.log_bound_74
  have hc := PsiOmega.Num.theta_74_cos
  have hs := PsiOmega.Num.theta_74_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_74
  have hqpos : (0 : ℝ) < Real.sqrt 74 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 74)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 74) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 74) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 74) = 2028 / 5 - 169 / 2 * Real.log 74 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (356388954292400465624509957753847611661095825373843304886917409745308347264680570782269707005654896310180274970218652847396293328002560053719969878304498243105995419947078038551903174368486837369709342152245943087600385031789667427964433607528159612690887832215384103193760447482163054899331845981939 / 1437240856929044417535381789242397462034398474756463776423481002212991894011285779080836358211449952062530309087496396553950980527414963144602004487606737854401160342904744949086575147672654752259080321197335687332590606657218651870303753910773212252704442523300418015068949708565711599762500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 74) / 2 ∧ (2 * (12 / 5) - Real.log 74) / 2 ≤ (3207500599160087302899312869749586320696905240324988082453282714190177997816256545734648880380334512954057630490166688415109897954905267789645073103226065879586187120291644992249905057261424222674341186470458080890840972042321437179842001756862811012465490707460765850386887764234888719507676827714949 / 12935167712361399757818436103181577158309586272808173987811329019916927046101572011727527223903049568562772781787467568985558824746734668301418040388460640689610443086142704541779176329053892770331722890776021185993315459914967866832733785196958910274339982709703762135620547377091404397862500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (66911372901891936002230013176403190536773708934082689272082632775528738466782632537804076424850696642683584229353779940301817293337021416967689441442554940592918288793569685945987068047215771289082679562005018578425232983019231147682649013281379031314694333109693381469501294493676206284102791210274081296699306985557158695160766792989571272446178194474813085237032612767851241082196681889544176056995033376032132317586145823933517754005391760028367111861380779755267303893277311103758372555444384330963968709182933128568988021931073667016074587410005153301493927031785715325618992991795471746464422437651246488145646771345265748121901150333420843386126133041173925399062287318130804122736359801726548579257 / 373011713120704772715239322074351411800581609864833204962591104911002564847114231227639556685972748808366221734286124764248941371772578069608265139428524145616744118225561887639868972513370813761175034751781325946217898812108339370963462943173020173853248204611385006418278907693784373275365439124439472410486453610148993000110859852336820886334916743907023130953843956724768904309876401920596062255483043289651310918949426364168186852211676062440188921402382966093733898176704748742901234521183209095296714644110901855830065831657717682996511174949511723572157062931758732795715332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 74) / 2 * Real.cos (169 / 2 * Real.log 74) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 74) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 74)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 74) / 2 * Real.cos (169 / 2 * Real.log 74) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 74) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 74)) / (2 * (169 / 2)) ≤ (240922533077824304693584457733267329956571942211774634946100834389921982566238169074515658127924201457990347874116312165064903029871331872730551591945429889141622064286816090180775545777245754122457383027577951580586403154635132661413588928186480611120229183458374087454621655231402827939840229281477732614302167923896722485539014867787295145841301571068064843691177098666375424965035524917857911985712670839445798394022771306727650029237871577707845107692032803689780208691347252181553189227949502934652846678358770871620544081466409349926932003591122248402298350635222384117859587840771758297397559081864428289578087019098649193469217884553620788419649796713533979824407826427567797079 / 1342842167234537181774861559467665082482093795513399537865327977679609233449611232419502404069501895710118398243430049151296188938381281050589754501942686924220278825612022795503528301048134929540230125106412773406384435723590021735468466595422872625871693536600986023105804067697623743791315580847982100677751232996536374800399095468412555190805700278065283271433838244209168055515555046914145824119738955842744719308217934911005472667962033824784680117048578677937442033436137095474444444276259552743068172718799246680988236993967783658787440229818242204859765426554331438064575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_75 : (2165063509461 / 250000000000 : ℝ) ≤ Real.sqrt 75 ∧ Real.sqrt 75 ≤ (1732050807569 / 200000000000 : ℝ) := by
  constructor
  · calc (2165063509461 / 250000000000 : ℝ) = Real.sqrt ((2165063509461 / 250000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 75 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 75 ≤ Real.sqrt ((1732050807569 / 200000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1732050807569 / 200000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_75 : (0 : ℝ) ≤ primeTerm 75 ∧ primeTerm 75 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_75
  have hl := PsiOmega.Num.log_bound_75
  have hc := PsiOmega.Num.theta_75_cos
  have hs := PsiOmega.Num.theta_75_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_75
  have hqpos : (0 : ℝ) < Real.sqrt 75 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 75)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 75) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 75) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 75) = 2028 / 5 - 169 / 2 * Real.log 75 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (1147007821552883890592675287275820897768498264335695493149409851956258793385421446040775864271091882850917303358344461068860928561941849425948790222048255022243230119448044561177519391249514934273324776296716631295248809371852819267087587082237592264241266030923889510297307253697640076441819832396609133111 / 4754319455437575551941748654342599442139226400172169592756277557789464322802738781624673550309207657475295073415674617484245592084681799919223056142774220878728463955151408149585987173168610615080672489424405389576155764701139782235719432445388336698121407940509094472529317119500237120722762112500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 75) / 2 ∧ (2 * (12 / 5) - Real.log 75) / 2 ≤ (10323070429386305410381899402103172398278989764789765462268525515108502781372104990116685954798300933970343678602925576787836318508887087063639414206065883896147643447945143862701194430856102504612972896304683299867476908329032982530112036193193161739236827450788429809594498013645103938634955404562837829601 / 42788875098938179967475737889083394979253037601549526334806498020105178905224649034622061952782868917277655660741071557358210328762136199273007505284967987908556175596362673346273884558517495535726052404819648506185401882310258040121474892008495030283092671464581850252763854075502134086504859012500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (29710838601427222982655872372565577520111928095973645377083421141512487974271359573573746693898087841161070469885371343544554179188758134251086894904283981489983389530103331662318896374435282677488494306545710349131783493354140056876735983695914614448996658869605236246126336670036798953266195719193163296565923285879288790556406475073094485893325033630033995462201019072044883667619736317401465124375810145003906965161611382147637403654467107148851594635295865925377009644540272400410239346531166642200267352170013845576088824181120916032784462155118301191510807870016537656594371857998709250294952720073636310689378922090203549613901301170979589125531095153384737299662947496573559145907113966288692486798512250968495527 / 133641934704181306656072539473744081712031956530361279268936579734379854396128362636025908724200781129467400763207935324441193582594180891217397852670960517318440208428444791345357092642373105637844982931607829935076638747516235581084030472521446772997858573919525419543305032689884500270160015582984280856253996974066542117728621695537152525213056139571119099022353698941643586087508038315439685203332603232275480319938395562984932508172143522095055325144178430375080887471533367374513973204130768822665456340332499445207617021106080981072887472842952018732703483209799025242649619520125120475384505880356300622224807739257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 75) / 2 * Real.cos (169 / 2 * Real.log 75) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 75) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 75)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 75) / 2 * Real.cos (169 / 2 * Real.log 75) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 75) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 75)) / (2 * (169 / 2)) ≤ (267433734684497242258765259107127520078833527344900385841103934413613268643135763303394420875583928784672696981737527267743585791403409733121377294100928685249962062720871303830882161051903941686197234434655488825149469531209538452609611314022767488653522447416947669779219243665699989031341835784994009103319954283372098345332324175475129050027812535264861884842520196091509881117547263499724609692546449745580472890132820483141245401337325081588511006129232707261413514417809109968042081341973920802945290298131515683096927189061380046394313061265916100449179207303140470875054905766017957859495952166619754393391751129675439050311430966391091245736118866689502282723074793051782262776242388648983842274718152733785440509 / 1202777412337631759904652855263696735408287608773251513420429217609418689565155263724233178517807030165206606868871417919970742243347628020956580674038644655865961875856003122108213833781357950740604846384470469415689748727646120229756274252693020956980727165275728775889745294208960502431440140246858527706285972766598879059557595259834372726917505256140071891201183290474792274787572344838957166829993429090479322879445560066864392573549291698855497926297605873375727987243800306370625758837176919403989107062992495006868553189954728829655987255586568168594331348888191227183846575681126084278460552923206705600023269653320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_76 : (8717797887081 / 1000000000000 : ℝ) ≤ Real.sqrt 76 ∧ Real.sqrt 76 ≤ (4358898943541 / 500000000000 : ℝ) := by
  constructor
  · calc (8717797887081 / 1000000000000 : ℝ) = Real.sqrt ((8717797887081 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 76 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 76 ≤ Real.sqrt ((4358898943541 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (4358898943541 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_76 : (-207 / 100000000000000 : ℝ) ≤ primeTerm 76 ∧ primeTerm 76 ≤ (159 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_76
  have hl := PsiOmega.Num.log_bound_76
  have hc := PsiOmega.Num.theta_76_cos
  have hs := PsiOmega.Num.theta_76_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_76
  have hqpos : (0 : ℝ) < Real.sqrt 76 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 76)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 76) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 76) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 76) = 2028 / 5 - 169 / 2 * Real.log 76 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (3840686903338216388181707183458842486522453432320597472640121662832683454424487466475365545207785794640994532382900894130747716575215991314086117726011018367408090903752246550194564059670328778389047730541050950107173213412750948941950047932864875734289126197316267581456190114532089511476965132486712280203650561 / 16368888923418256184133395471217507091912691673699171471549818573868793979658012290933451424710636813512224648311570339942000845513547287713688940369820646548639043702852495840025224123848041085802616428136245960446615066233553914388252455657282219223133799590183727323289284905900460895029554537993987500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 76) / 2 ∧ (2 * (12 / 5) - Real.log 76) / 2 ≤ (34566182253836753844814700803515565995106771161640556521614180960579243207016874616972471516152711877108308485983843797924080834203609583767820782983017757611159799611581650238038100467130172052817804683405344593156327412222502139242875308952407558052772283942231722906476500305850541590609398886464677068262592551 / 147320000310764305657200559240957563827214225063292543243948367164819145816922110618401062822395731321610021834804133059478007609621925589423200463328385818937751393325672462560227017114632369772223547853226213644019535596101985229494272100915539973008204196311653545909603564153104148055265990841945887500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (203971370590941690828241183081674100299237784072467439329895747400099969300499814203839402032100440501135215990625197712281166088049408286190269387471960926343904177470794270693977367686697589642505802262098500940415697676072427410400289509468158802290635002072870338670776128745744678788000857316853587394322310033404191845655428437897621167667533315601699686309163079374865626814834822485714625222785583007374598706186743070960703441164903516121834555094312557122145089161826132781085581437299329266591677473703779345185026641863724198751908035210381478809132580485845948567563183842116888913300758275159632655545731966790363591267472368909121739400549768841862842063245128509183477930050199981750838391938012420197623033799017828804955908144838069 / 12095999840153118696406876116056140386750424640981072275469592572664311701684686856603229591456391442729976340829970728848079553292568043455392075944554499688369531319285529714729284964396018475727753726891743730538678836641267072787742362904737241256824143215831638210508164282016810206654388816243921807135316640089429187262545996254237506637408201712331102038391969415664967235394933766967842479042932287814568067565267040297255280030955081562984250215172689137140071602273126735662923814518709169237118509446291294876259516848057129498932383979827227936108532238578596193437901263430580756761275529861450195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 76) / 2 * Real.cos (169 / 2 * Real.log 76) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 76) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 76)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 76) / 2 * Real.cos (169 / 2 * Real.log 76) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 76) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 76)) / (2 * (169 / 2)) ≤ (14711259669008274542839636091757230965240284794803529400188826970753177842382237413800535093285633478115796097504218614644884273112745011495312517514771740519804606288391500733154599258809732876016697745257461529761780299934431261559734672359751396292007750176151064649416021143637925668664609658629359379490185141119591235549849830197623887129556436614581542065371707681098731188313687853036044171878808800234221417063809107549197560084078795440108548695017125654676426559886130392477668489001136047625386186080623366280209618677688702775414967120841890742701516566505008306270106682217691414602009040767170095299682925819760196190811590267331254230538352240081200648463541438628044520309592693304729583699676712822380204123356863348232409 / 870911988491024546141295080356042107846030574150637203833810665231830442521297453675432530584860183876558296539757892477061727837064899128788229468007923977562606254988558139460508517436513330252398268336205548598784876238171229240717450129141081370491338311539877951156587828305210334879115994769562370113742798086438901482903311730305100477893390523287839346764221797927877640948435231221684658491091124722648900864699226901402380162228765872534866015492433617874085155363665124967730514645347060185072532680132973231090685213060113323923131646547560411399814321177658925927528890967001814486811838150024414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_77 : (137108818553 / 15625000000 : ℝ) ≤ Real.sqrt 77 ∧ Real.sqrt 77 ≤ (8774964387393 / 1000000000000 : ℝ) := by
  constructor
  · calc (137108818553 / 15625000000 : ℝ) = Real.sqrt ((137108818553 / 15625000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 77 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 77 ≤ Real.sqrt ((8774964387393 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (8774964387393 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_77 : (-993 / 100000000000000 : ℝ) ≤ primeTerm 77 ∧ primeTerm 77 ≤ (583 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_77
  have hl := PsiOmega.Num.log_bound_77
  have hc := PsiOmega.Num.theta_77_cos
  have hs := PsiOmega.Num.theta_77_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_77
  have hqpos : (0 : ℝ) < Real.sqrt 77 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 77)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 77) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 77) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 77) = 2028 / 5 - 169 / 2 * Real.log 77 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (3733699177595089307401978262401786398827191823017304290271696528673124827987993628685796723060180199528658928271960836881944699668397035317403971391694816759403536731248761687684547664830922984253934397859561162134511643357430601139868947623953818264109465103413568549389305421075608004436258279344898998953650561 / 16368888923418256184133395471217507091912691673699171471549818573868793979658012290933451424710636813512224648311570339942000845513547287713688940369820646548639043702852495840025224123848041085802616428136245960446615066233553914388252455657282219223133799590183727323289284905900460895029554537993987500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 77) / 2 ∧ (2 * (12 / 5) - Real.log 77) / 2 ≤ (33603292723905817867199823253358752595826919428009913862720625977280832202364379735108135420638435398781021501003519520238485771990462638507486901926467725852118051162925715929335572413340235193126881260693657299003295200821113847744751834190396620671052800755674999874309418681997492304440650687477827068262592551 / 147320000310764305657200559240957563827214225063292543243948367164819145816922110618401062822395731321610021834804133059478007609621925589423200463328385818937751393325672462560227017114632369772223547853226213644019535596101985229494272100915539973008204196311653545909603564153104148055265990841945887500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-1450987309587313008927432031529733718653943748425099545585542897164904283022604617786174001746169824657305357956013783093452904310451419783980962862732289478038088165420389436382881357299305506046640453935011167556242558385574017136746163256069070816998103006686488913922851986954427490083667678870819240118564998868247953931798046036681433098977692622765284297584309482945246078282535265502896427061662985924702117633176199073466140295402017614194464296670693591402792306155466231991378676773567154077335788345876410807380380129040829068810130174751494535630035815670815023025413632027265257596536136841273661322499639161906380538911533715791946022631656603787632617812366794468935231638334798063223065663477019005113 / 7475097557467671313544898722843531580557131926875815233711524951063608153049161036566632056487790732277893704278775245946460295232376186522573533260413471029342132849595092063088013321808452579757294096971368729962409864562550604978997279321927769026205105594500447807702341513392346395408672287870465594314274962213468659731035047123666672040024294576254419442060466939307116287742535668368493963641948816779937846929829637634869977436121838429273409022743132172457472227356897473058294898803828756013539117928692587928596655767003078379924950426986736013983086481665544827792892473891273813611322921133250929415225982666015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 77) / 2 * Real.cos (169 / 2 * Real.log 77) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 77) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 77)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 77) / 2 * Real.cos (169 / 2 * Real.log 77) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 77) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 77)) / (2 * (169 / 2)) ≤ (-2518701453193491716131040922323209349487536328478980661238531363868129306419556955078352749027246505513759416934456861701455760015037807373009030712182888442254726656177399465593878705208444468974712845609194778199829394484555190682884425399410736163677664459920598592863398482334607908260423034174080604061151076251553427051143003923775133217536305907296229978995598520929573950826009283286640376706512189763153637718594190262520174298250589119204073654549419428830088812269954963657274116391019982316597757767950986831669326011744460855989989203223754996447205969022320991989418308667176528587116465683842872191188211976562920312384071267112791622103624929091620615132409534236916110671915569601716184336727626699467182400457283411535831 / 12977599926159151586015449171603353438467242928603845891860286373374319710154793466261513986957970021315787681039540357545938012556208657157245717465995609425941202863880368165083356461473007950967524473908626267295850459309983689199648054378346821226050530546007721888372120682972823603140056055330669434573394031620605312033046956811921305625042178083775033753577199547408187999553013313139746464656161140242947650919843120893871488604378191717488557331151271132738667061383502557392873088201091590301283190848424631820480305151047011076258594491296416690942858475113793103807104989394572593075213404745227308012545108795166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_78 : (8831760866327 / 1000000000000 : ℝ) ≤ Real.sqrt 78 ∧ Real.sqrt 78 ≤ (1103970108291 / 125000000000 : ℝ) := by
  constructor
  · calc (8831760866327 / 1000000000000 : ℝ) = Real.sqrt ((8831760866327 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 78 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 78 ≤ Real.sqrt ((1103970108291 / 125000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1103970108291 / 125000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_78 : (-5674975879667 / 100000000000000 : ℝ) ≤ primeTerm 78 ∧ primeTerm 78 ≤ (-1418531234119 / 25000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_78
  have hl := PsiOmega.Num.log_bound_78
  have hc := PsiOmega.Num.theta_78_cos
  have hs := PsiOmega.Num.theta_78_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_78
  have hqpos : (0 : ℝ) < Real.sqrt 78 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 78)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 78) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 78) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 78) = 2028 / 5 - 169 / 2 * Real.log 78 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (3628091977202276150756772060807994027761868594828156972779565656428327593842969733803647571867956605735231837976067654651741384575297434712554868462187466833884531932194696466364081623358262750106949289223433259251718572550136869743356550531470721759336930555608263240829523058692913781529635586925861161453650561 / 16368888923418256184133395471217507091912691673699171471549818573868793979658012290933451424710636813512224648311570339942000845513547287713688940369820646548639043702852495840025224123848041085802616428136245960446615066233553914388252455657282219223133799590183727323289284905900460895029554537993987500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 78) / 2 ∧ (2 * (12 / 5) - Real.log 78) / 2 ≤ (32652827922017225286035633844221652364624181018363879973572823172248305174837007661221670828066898605276373436486017125162126077096379646213772550021990379334869453091889392349597537661408063939284867727741277267037815510299399532468233945705454773885599536288477189262605160215579300271031782098000101868262592551 / 147320000310764305657200559240957563827214225063292543243948367164819145816922110618401062822395731321610021834804133059478007609621925589423200463328385818937751393325672462560227017114632369772223547853226213644019535596101985229494272100915539973008204196311653545909603564153104148055265990841945887500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-163174521152038742028411162198077228863483513727322230977403011327563175300156544637786659185506498547544820536322446116022962063416781828286192534687120729573977527994590974224489746530730891478255259587066842391542507891415724287642970047912017044587592316401416127899908787357898109012064642517224706665870094703446517694741008261794387505991185039884409316651713461371005686272713206038011930560162970660398660613389551402005355215776695181380191715491942669206790288095599060000160012129489716328482648475722349898726079252969655475431698153886363278166548943602557016684676449237810437008872194598366640556358963967438333545820935972531419195729186079626004822325290821294857060379532932513134946605082500832255298861946131244657924495437649 / 870911988491024546141295080356042107846030574150637203833810665231830442521297453675432530584860183876558296539757892477061727837064899128788229468007923977562606254988558139460508517436513330252398268336205548598784876238171229240717450129141081370491338311539877951156587828305210334879115994769562370113742798086438901482903311730305100477893390523287839346764221797927877640948435231221684658491091124722648900864699226901402380162228765872534866015492433617874085155363665124967730514645347060185072532680132973231090685213060113323923131646547560411399814321177658925927528890967001814486811838150024414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 78) / 2 * Real.cos (169 / 2 * Real.log 78) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 78) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 78)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 78) / 2 * Real.cos (169 / 2 * Real.log 78) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 78) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 78)) / (2 * (169 / 2)) ≤ (-2265972969016447641068108488361164881636364434666959020477068781674497613350175357163270866649252262822537194768375307880967609650060315353409754070083017002079207001766645161785976427798063843085210436839159810833761433981609570096465722584545842494166213272262883578040374515560586905874014775835943480199280613441636001464239143128578667585735457305594937114921628895082790686940366565207847892318292921886524609719988492123415372778625679160908184343298425236351528199348269198694673425760519690658213362219234786520959199077498337402948492743398072066608936841157425063112980596206733446602823360162504835208697525093868557085133773981530210371063433076262796858501265222946335191836254297632193413207511208230253342863107460897779727825103 / 12095999840153118696406876116056140386750424640981072275469592572664311701684686856603229591456391442729976340829970728848079553292568043455392075944554499688369531319285529714729284964396018475727753726891743730538678836641267072787742362904737241256824143215831638210508164282016810206654388816243921807135316640089429187262545996254237506637408201712331102038391969415664967235394933766967842479042932287814568067565267040297255280030955081562984250215172689137140071602273126735662923814518709169237118509446291294876259516848057129498932383979827227936108532238578596193437901263430580756761275529861450195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_79 : (1777638883463 / 200000000000 : ℝ) ≤ Real.sqrt 79 ∧ Real.sqrt 79 ≤ (2222048604329 / 250000000000 : ℝ) := by
  constructor
  · calc (1777638883463 / 200000000000 : ℝ) = Real.sqrt ((1777638883463 / 200000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 79 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 79 ≤ Real.sqrt ((2222048604329 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2222048604329 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_79 : (-28886134077 / 5000000000000 : ℝ) ≤ primeTerm 79 ∧ primeTerm 79 ≤ (-115277895359 / 20000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_79
  have hl := PsiOmega.Num.log_bound_79
  have hc := PsiOmega.Num.theta_79_cos
  have hs := PsiOmega.Num.theta_79_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_79
  have hqpos : (0 : ℝ) < Real.sqrt 79 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 79)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 79) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 79) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 79) = 2028 / 5 - 169 / 2 * Real.log 79 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (13636845545897497485276294410555275729667648341292080410272395162925259467822134272170502076908274715463089582217423229238386420310956849175979205591285892266590622006867137078798831940950591055981168762681759836474531063326607010501705026696559356982579119888763320061246818146555124127790708523836821923570414630459973 / 63345848662513845679184538200296332172443282119206707783550342050284828740320684158597327134327720430153263580928407877549169478046958053892190834514586331334052394752362953683842734660310667261659944696929461288610632518511766658413697460380926859196070929097454875082305940632349852314448607899701166268337500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 79) / 2 ∧ (2 * (12 / 5) - Real.log 79) / 2 ≤ (122731610411292206388939408179399686290994286582039131566635155432820161726342260010438274787976787931011994662363150260050942335300632533729599285634847923542419672422915507140826507992588491955552138986628417357919454105845557620318543791075085374635127551649739136582723083161484243216967059821649170056326329074967043 / 570112637962624611112660843802666989551989539072860370051953078452563458662886157427375944208949483871379372228355670897942525302422622485029717510631276982006471552771266583154584611942796005354939502272365151597495692666605899925723277143428341732764638361877093875740753465691148670830037471097310496415037500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (12828181972289817882970720789026886521700951130672581099719429962253921852752002428536391248645632177359655372117804297342657799135792597132376368929489217551469303921081103184388376151492901555936312007473139955929124059990202254550701431246318808425267904584879788481863497911316468984312157267410027821123477430748155877527979007301776252591617507556323331624299311495587030164248795622363778286022160602583283907014127037850536974665681298745025614315228542442776989982216214664428225165902751499969225697655727684132731032045375330176271664461572866716333118831896652583291368744817005276141163014208594862158557401857575459848842508471015998111263712977729071362521349447470801190908534711392707826099487050812083506924661939966204052889099 / 1094112761485389695046432138565743397823749279291800115789306902168441650759644995995795516375600129255443880673719363429791359272730810383154564286876882126455733501523481297214360571045734918631178795695481362162468362413053988526515059847919813980206697438965689321311484954437510372660115797321823556010261099930295424154673116383367778744727887394496734209267023148128644468718307171682517002419642767534758386262838858756291888913643961535800112054418263730436449081297470117271430759279950388418646616226785251738888194004378820154133272059171112819421432578256678470167214147591506478466839236472093250503200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 79) / 2 * Real.cos (169 / 2 * Real.log 79) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 79) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 79)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 79) / 2 * Real.cos (169 / 2 * Real.log 79) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 79) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 79)) / (2 * (169 / 2)) ≤ (289301712875239153121875135700517179774839639966531598599872846231735294836134398781102910401789764607117021366584464329276674616998360670860597947708515804111290106144314946187731929526442221003401607576380913483503244729992886558401345179890819292372472929023812003286790942384041299308475710973451056411567915190783313732285444602775455878748788393380291633543877996967714534813663872163445658166375591807769758524232153061901200385709064788981150318498517496049203041164066468187625405969340797947896321545916994100210047975279268945486315273893536417421186833862990282438206667721649394400735398813431089132694152495652392202117964707482338065679778368805251015081349627991633037501218424173026174293113269320937889269371 / 24617537133421268138544723117729226451034358784065502605259405298789937142092012409905399118451002908247487315158685677170305583636443233620977696454729847845254003784278329187323112848529035669201522903148330648655538154293714741846588846578195814554650692376728009729508411474843983384852605439741030010230874748431647043480145118625775021756377466376176519708508020832894500546161911362856632554441962269532063690913874322016567500556989134555502521224410933934820104329193077638607192083798883739419548865102668164124984365098523453467998621331350038436982233010775265578762318320808895765503882820622098136322000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_80 : (8944271909999 / 1000000000000 : ℝ) ≤ Real.sqrt 80 ∧ Real.sqrt 80 ≤ (894427191 / 100000000 : ℝ) := by
  constructor
  · calc (8944271909999 / 1000000000000 : ℝ) = Real.sqrt ((8944271909999 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 80 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 80 ≤ Real.sqrt ((894427191 / 100000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (894427191 / 100000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_80 : (0 : ℝ) ≤ primeTerm 80 ∧ primeTerm 80 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_80
  have hl := PsiOmega.Num.log_bound_80
  have hc := PsiOmega.Num.theta_80_cos
  have hs := PsiOmega.Num.theta_80_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_80
  have hqpos : (0 : ℝ) < Real.sqrt 80 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 80)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 80) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 80) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 80) = 2028 / 5 - 169 / 2 * Real.log 80 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (13238438728381554205418575897635212342326135264018201382596362694206207472978292636512011614011056217014312526185030948472521707878081452779549508771728353878568200197747154004054019974533156756838420479581318015261982532939242706095411936108669251679334980155412583112638457774078949623653108214358108112591234942959973 / 63345848662513845679184538200296332172443282119206707783550342050284828740320684158597327134327720430153263580928407877549169478046958053892190834514586331334052394752362953683842734660310667261659944696929461288610632518511766658413697460380926859196070929097454875082305940632349852314448607899701166268337500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 80) / 2 ∧ (2 * (12 / 5) - Real.log 80) / 2 ≤ (119145949059259096199027174803105254558544913170095705080239904362427374726946873983849095145142657423348663244830605372463023591122557503380609238181115210770802931513306892229637802351483864759355624156269636423939364044374972707612284059749426522242535901759436427675562278708203315412331137238618334568376329074967043 / 570112637962624611112660843802666989551989539072860370051953078452563458662886157427375944208949483871379372228355670897942525302422622485029717510631276982006471552771266583154584611942796005354939502272365151597495692666605899925723277143428341732764638361877093875740753465691148670830037471097310496415037500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (2208258276856406035877398455948364350120885343184451284844527195081613509996285429134447212276674732689481551117946962296312442079707798891313297669204294228039989865776767665718159876082893872015818329450863589863694296745664734030633177395169490770032284826780363061693134680577108713941331170083491686493520124605336775266983213715471242733560737411385092287789491221728502902951746462865228180863331283062675680984159349202292970785048252725268691211689540993331995587282948716063906375182754272101421521156779251693600231820128844530213517941147331102480771270746865866263170871564720850950368733034848377380354047040315523415529719459789227594384674302166266792469101924863409656266913553600853145565494140097623071017400563954279226297138691 / 11862394329465740506410546931871472364075694234202257854876527938801853418681784462253504075063792480304807494211661487708626964041338314346234241574187309194076425628922296699029315049787608532258615297820464526265932360893340776435698903731699098030256711219675780120610919807976127141612091945544952458394212306832295191217329812995246967393096232764462449896095989000315055905495874004020962046717451056861564035847007281312307489154261110756491925146059292764437129785221721316433658453652084121433369758402353837403819824618547058090131923694213632177921122237182900077930525939510559234355254652673911818722488065169784476893255487084388732910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 80) / 2 * Real.cos (169 / 2 * Real.log 80) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 80) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 80)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 80) / 2 * Real.cos (169 / 2 * Real.log 80) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 80) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 80)) / (2 * (169 / 2)) ≤ (5088557971357227245584468467912493302088224767807228300075610793096480855522013803927063187126035873309562616975390845203431206639475154087828682277545960185747860517098996150385074286505888436826898111400524712227906111609101005066756272467311629469324988583558400958984589920807923027993565022481664495501940946736918515876443713585686225957811272865003826603364747236081452177568133877721072554595338408658736348964558484795852788824639537530206158975869905568859819503634395667253284648805382220073656687546970424902545299537992327543937554433780567645150593800840773391344845057066420581042315445212749630991408092912614613745820980189246313890884673988462674068700460135641145810001544921368848516865645460117251672876797 / 27330956535089066126769900131031872326830399515602002097635520370999470276642831401032073388946977874622276466663668067680676525151243476253723692586927560383152084649036971594563541874710650058323849646178350268516708159498257148907850274197834721861711462650132997397887559237576996934274259842535570464140265154941608120564727889141049012873693720289321484560605158656725888806262493705264296555637007235009043538591504776143556455011417599182957395536520610529263147025150845913063149077214401815782483923359023241378400875921132421839663952191468208537930265634469401779551931764632328475954506719760692830336612502151183434762060642242431640625000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_81 : (9 : ℝ) ≤ Real.sqrt 81 ∧ Real.sqrt 81 ≤ (9000000000001 / 1000000000000 : ℝ) := by
  constructor
  · calc (9 : ℝ) = Real.sqrt ((9 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 81 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 81 ≤ Real.sqrt ((9000000000001 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (9000000000001 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_81 : (4047882575043 / 100000000000000 : ℝ) ≤ primeTerm 81 ∧ primeTerm 81 ≤ (809703466857 / 20000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_81
  have hl := PsiOmega.Num.log_bound_81
  have hc := PsiOmega.Num.theta_81_cos
  have hs := PsiOmega.Num.theta_81_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_81
  have hqpos : (0 : ℝ) < Real.sqrt 81 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 81)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 81) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 81) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 81) = 2028 / 5 - 169 / 2 * Real.log 81 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (12844981191995241522228673272747357742816798790034104185043701396332606894649178731749581680534251997220253628226816107808003724438471543981544268208132219363248869687896073315231769645961064316314841136871444375223088743650227067818545999492905426433607429904577575635755388168463390149780240691948591031893305255459973 / 63345848662513845679184538200296332172443282119206707783550342050284828740320684158597327134327720430153263580928407877549169478046958053892190834514586331334052394752362953683842734660310667261659944696929461288610632518511766658413697460380926859196070929097454875082305940632349852314448607899701166268337500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 81) / 2 ∧ (2 * (12 / 5) - Real.log 81) / 2 ≤ (115604831237052736242391539846862544823644809828826815860405432061713608204518383535032567419877672258297156967797750376461268414350964375980700872517366022923259535495505009684270970054695511378213263548815676845626149170632071842016449916798787159871401588208299218674370813886639140427195378435380046880326329074967043 / 570112637962624611112660843802666989551989539072860370051953078452563458662886157427375944208949483871379372228355670897942525302422622485029717510631276982006471552771266583154584611942796005354939502272365151597495692666605899925723277143428341732764638361877093875740753465691148670830037471097310496415037500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (271203113885088392667640721752518936005374512430705611838339137637791404063591922830931289284041871701329189984214370044272850864301506517941831891330393865881703369152210881585713329455248863041604513177305578214300764972563036203908308592219578447233156573956875532994036783906283640628198071935658175855044056687217850001727518663350666231052350954978706619775265012319891278134326335345507848697174031549949233180120575343314336808075374524293795511569910518270965936071956776968069474307939186338112903404327183444325568509696623901559427433903099370659709080616578938860706771052500384236448315584155347460299531390546967045369544538752078427766838707189629799669639121153761293789946082316785793821660925730776428675399569872500867088214651071560401023 / 1630355062313958548078584877499555644130333184140622788353721651685895995437569910281591886841654970132475913574873452529000281203882113670042998026127937624537547680025519873521269218691788492547242038988294247034889999647518975327186375629782399505684818981536759914921946755703554112702780659976338678613694161072813606492687935208332208908688854268933436586360667866660124761936526256326611343651477646134433725867925373846727444102829637431800532422092949942404700936820313509213076173186228258041510904173232990114224246150819689265092122642950881748529423144842205152164718728648880837063251788127561286841630935668945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 81) / 2 * Real.cos (169 / 2 * Real.log 81) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 81) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 81)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 81) / 2 * Real.cos (169 / 2 * Real.log 81) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 81) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 81)) / (2 * (169 / 2)) ≤ (19529686200873381281675318004827372243106387285597767246670079604952807042705979359279588782217930430448591675073700247361187317914909650097194357836392779829834885599151185753781373560248031603533684959153185536370656425534749553768026712566228256503746367994762570959362212632183145961951467045113321300161392400178307213691626924555174877406592054893232862345697938947971595571695537970522761818399578791471253906221340861706049360075059282256469457890889403112819222683244428185262974027381206507997768749058577155351984825770955175643680392506382208746964726283499614766170615359340419741014731456413226054337538678673046548137652374725996061020338981848007045818482371923360457219213855650508724462777792955171443311438723660294430974354978198979324711587 / 117385564486605015461658111179968006377383989258124840761467958921384511671505033540274615852599157849538265777390888582088020246679512184243095857881211508966703432961837430893531383745808771463401426807157185786512079974621366223557419045344332764409306966670646713874380166410655896114600207518296384860185979597242579667473531334999919041425597507363207434217968086399528982859429890455516016742906390521679228262490626916964375975403733895089638334390692395853138467451062572663341484469408434578988785100472775288224145722859017627086632830292463485894118466428638770955859748462719420268554128745184412652597427368164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_82 : (9055385138137 / 1000000000000 : ℝ) ≤ Real.sqrt 82 ∧ Real.sqrt 82 ≤ (4527692569069 / 500000000000 : ℝ) := by
  constructor
  · calc (9055385138137 / 1000000000000 : ℝ) = Real.sqrt ((9055385138137 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 82 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 82 ≤ Real.sqrt ((4527692569069 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (4527692569069 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_82 : (-31 / 50000000000000 : ℝ) ≤ primeTerm 82 ∧ primeTerm 82 ≤ (37 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_82
  have hl := PsiOmega.Num.log_bound_82
  have hc := PsiOmega.Num.theta_82_cos
  have hs := PsiOmega.Num.theta_82_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_82
  have hqpos : (0 : ℝ) < Real.sqrt 82 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 82)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 82) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 82) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 82) = 2028 / 5 - 169 / 2 * Real.log 82 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (53945306791508307163909027302803341542127199443796456692470070524200461523964424453420915317201112214505948865559176014642382644194316673548123264765925385732929716260468933595979028434235069358947377642947080127199115464172052463899873814992862343340320540516100154270149626347866502107931078222898548460751689925480011689831 / 274334844057635849633591401257318739666812226707908092113487293183244871212657581957792898695008372269724955793314959630472433069543429451019443780001541210665953406416611604577440871601936441311432020516393173687266630947647277920625145035452317852682806587976015407898071205475727225861241365315807126713103823112500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 82) / 2 ∧ (2 * (12 / 5) - Real.log 82) / 2 ≤ (485507763349797465489339110504572765272961961838289061514969551692537714203192932660451259002263987679463668646293279444297441199376695120706376120439499409782913518725787795238432240668550293816385783858534285550987179751910725543170697436310468341973191549078827416827194053379350771402814894657478690204082672312426296571121 / 2469013596518722646702322611315868657001310040371172829021385638649203840913918237620136088255075350427524602139834636674251897625890865059174994020013870895993580657749504441196967844417427971802888184647538563185399678528825501285626305319070860674145259291784138671082640849281545032751172287842264140417934408012500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-29466798468944866964674646902341370590977212877022112250572860541432667343171064314379983590179712354829273630846580162733227220087976198859905057949694465380122475553282502439914247335996942826282706602869281168375065905274597195535620694191454782060274088281089849366619075527194219424188136623825233235199407239472942883520502350176932120685339535581946977467902363514104082330619587958265963824239189347324572660258735002569111052116520548988818292554027316959665813436767201756257904050394487413357573482317808957891926741242077324859179673931738475431651282973037092674295499883812768112658007694267105283678943055006914240865860912947184831800936890685175878137603422687474510597068021671009502623413208859289849143089238624719542229221823 / 2504942529501281127051015519574321553435667764808260134282869913534853092095344521830604473718712603195532269486991856433923104597401338900995875975510782561596887819493044357414539273753517283286978491373704724258937835699308308318295786831941311187307014846734553413046335837445532410893422406298936088873843567074410774980778221724665708093475922501911167528734018827992818518958797458453609280541291870711781040063749251575971845599111334510762985250030466926989542741123846172798872322044441598770738260181672006683185583574064760260303204482124329189247446796238794500476813830930230408295311554669390545604870521350601660156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 82) / 2 * Real.cos (169 / 2 * Real.log 82) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 82) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 82)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 82) / 2 * Real.cos (169 / 2 * Real.log 82) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 82) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 82)) / (2 * (169 / 2)) ≤ (-32670924560333404071640756089816292142301930763058532734103963878189325881769836917881111082075602839704884337794972618549472411707741389013683308483792044722615572426305212526255914562387981618720829764597994721237750127836436833217574651601136145051866360067417257293056733635489049153203441170815580972742630452614707344603565163203966160443619140809537494405141710048170644373697012206757537601440411636502461682550423350117015735697424833658702546604362094668121865342797885546138919008769737388294515132879269182001641687748950692761258317066345711047902054944960907486479916907815680762187848552155288339260022442468161762726551292774753857947799595687256742838457154076495536025448714745944082647445241280831272462660352811445147231125360173371177675250306103 / 2783269477223645696723350577304801726039630849786955704758744348372058991217049468700671637465236225772813632763324284926581227330445932112217639972789758401774319799436715952682821415281685870318864990415227471398819817443675898131439763146601456874785572051927281570051484263828369345437136006998817876526492852304900861089753579694073008992751025002123519476371132031103131687731997176059565867268102078568645600070832501751079828443457038345292205833367185474432825267915384636443191468938268443078598066868524451870206203971183066955892449424582587988052718662487549444974237589922478231439235060743767272894300579278446289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_83 : (1138804197393 / 125000000000 : ℝ) ≤ Real.sqrt 83 ∧ Real.sqrt 83 ≤ (1822086715829 / 200000000000 : ℝ) := by
  constructor
  · calc (1138804197393 / 125000000000 : ℝ) = Real.sqrt ((1138804197393 / 125000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 83 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 83 ≤ Real.sqrt ((1822086715829 / 200000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1822086715829 / 200000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_83 : (35901779793 / 1562500000000 : ℝ) ≤ primeTerm 83 ∧ primeTerm 83 ≤ (574513473911 / 25000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_83
  have hl := PsiOmega.Num.log_bound_83
  have hc := PsiOmega.Num.theta_83_cos
  have hs := PsiOmega.Num.theta_83_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_83
  have hqpos : (0 : ℝ) < Real.sqrt 83 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 83)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 83) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 83) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 83) = 2028 / 5 - 169 / 2 * Real.log 83 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (52282651014010106724651599392866613807688635399246029827375638995925996521057469278157529392398227993231284796499143591834004836825423666753815460891108134064154897344432668426965660891278353649856161163658729697966728118642340159403552658103530310171613088208738220762044797913838329303336483615461179338142919101342511689831 / 274334844057635849633591401257318739666812226707908092113487293183244871212657581957792898695008372269724955793314959630472433069543429451019443780001541210665953406416611604577440871601936441311432020516393173687266630947647277920625145035452317852682806587976015407898071205475727225861241365315807126713103823112500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 83) / 2 ∧ (2 * (12 / 5) - Real.log 83) / 2 ≤ (470543861372502889544987687989108859851122706188505205546049816717641841024353282830592544389148700050444848718503118233659847781970882185508804309653686984757550860458831842711198207357616318839808425676584587676986886338917962159619496604243949592203948099121716449664337144603369138946387647138631465640149477316826296571121 / 2469013596518722646702322611315868657001310040371172829021385638649203840913918237620136088255075350427524602139834636674251897625890865059174994020013870895993580657749504441196967844417427971802888184647538563185399678528825501285626305319070860674145259291784138671082640849281545032751172287842264140417934408012500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-350180636580239841115844660370213793925464216371223645229905285088996568315391579290540949771079320539427995568070583203298452403124707650501617662997004159501269926550547596043150964059896496436573448003870107091223200320068577168829599036337460718133681191052290744559708719166329565850555330985120196907529779416014060906198053407365091186712023554026687637310357879218041549663436907958985531759849485551457674967213964014953824334485338964489935522063549372775069357414360072728127597618240853953471242350929968119280628953784689648351833864052483342896326198298634059600777843907472712221968251587576323562241657017325575517355214152564488641337253142277170428485842397216113185127106872451756125047389169368051957451420836622320468041511 / 2099618573255048146793538674355381539177243586934575923583081850950948691820548912182025635938012360479663165787507473296048859262523432272389799708462976203707232174969967381724235924312999057544656696018142860227305490644068901880147129435788076434821182267797270856557136637811529608260914837633299157010819027542108388135861977517790288929015705596394884191323646293201983596256857470244400531507248695605064682715921035426086430474370905253744392399701681206273463058296089577971943737789986132545084165561483060954946116746085029313594926180235944940077794824368241290030193000880263156691361590477127107832937938361932983752922154963016510009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 83) / 2 * Real.cos (169 / 2 * Real.log 83) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 83) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 83)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 83) / 2 * Real.cos (169 / 2 * Real.log 83) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 83) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 83)) / (2 * (169 / 2)) ≤ (-607862549906561086861865497242346571215264720704171179377825229335927924253433857410793265263866895052541239458938443210973915942077290639448472690567919939117637986799799059948116075562255887317841819691037971345264853789497143512109612344608204366377859571953540060919875908934492978836813944066006126781796404785359643091416516818613217429849034210329560560122705497336327307085812695730013013286911774550816014291897482097965384710139791353585096101573288347908581363027907703648814480480464350907933019420140093597605750025243134755008993415774085300783028990638891586454140467735974307237959230060593917081357469855672117716218157302319816545021208173957516651690037873287258219967385310075253511913016005494760988052404812626570218073116505025016904004096417 / 3645171134123347477072115754089204061071603449539194311776183769012063701077341861427127840170160348054970773936644918916751491775214292139565624493859333686991722525989526704382354035265623363792806763920386910116849810145952954653033210826020966032675663659370261903745028885089461125452977148668922147588227478371715951624760377635052584946207822215963340609936885925697888187945933108063195367200084540981015074159585130948066719573560599398861792360593196538669206698430711072867957878107614813446326676322019203046781452684175398113880080174020737743190616014528196684080196182083790202589169427911679006654406142989466985682156519033014774322509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_84 : (9165151389911 / 1000000000000 : ℝ) ≤ Real.sqrt 84 ∧ Real.sqrt 84 ≤ (1145643923739 / 125000000000 : ℝ) := by
  constructor
  · calc (9165151389911 / 1000000000000 : ℝ) = Real.sqrt ((9165151389911 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 84 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 84 ≤ Real.sqrt ((1145643923739 / 125000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1145643923739 / 125000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_84 : (-2567139322229 / 25000000000000 : ℝ) ≤ primeTerm 84 ∧ primeTerm 84 ≤ (-2053400348881 / 20000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_84
  have hl := PsiOmega.Num.log_bound_84
  have hc := PsiOmega.Num.theta_84_cos
  have hs := PsiOmega.Num.theta_84_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_84
  have hqpos : (0 : ℝ) < Real.sqrt 84 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 84)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 84) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 84) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 84) = 2028 / 5 - 169 / 2 * Real.log 84 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (235853496718956107187330864250998706486452225542281039305536443612058993563113727333063765681132490786755064819207279957128609324028004568997092380763453331958073568608664443266048089811351273337543025846570877151764831766501261558461805932892532768748731363906747507095899882436448731728104216264066906116238846199242055553705358753 / 1277704385809208837142015508474115509204810273839693746419158868971115207612717819637887987334749778536470001784000071825419029541374949561233371685937318131651883350109331133690061494173769703759666112570342099901017904773322133966028549872252858663109622419654536649715174410868596952541374793027855007802592671305013587500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 84) / 2 ∧ (2 * (12 / 5) - Real.log 84) / 2 ≤ (2122681481021718596647437016183626884797460976380242257385268052981031126168945610010286194824275790509854973643080460430808993039973771890442707779897083095047860134380977151453869367898853318677675986799245931307623701174332611446639305608413164609260181540771395089358965205656612003384584422545503069821271593055927803707022926023 / 11499339472282879534278139576267039582843292464557243717772429820740036868514460376740991886012748006828230016056000646428771265872374546051100345173435863184866950150983980203210553447563927333836995013133078899109161142959899205694256948850275727967986601776890829847436569697817372572872373137250695070223334041745122287500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-186440010289933743014447715841355066131970262529203196794315522789159255749895591302096590630232603664573094890067532516939583333501497256510073269925424816037692110928021963422003770472160067399135583431118678197956618350469780219432460529000332958570422117997184961170681892542700756305139410749712442227412631643146722323019851523515146132112497451040419140299827907914509696380455912722186753293365259621205459563356703546869951107604693588612504357358402296399180397621145856165055033308917590191199107627631609145698541881889752930281748789951365218481955245632648363432102277830089356216569058252867060163140936839865714560461783067530397688026320650534855172858506418012139467087048829338908505976120832620507411781475069128514506173357362960626836309729098679709 / 1178248409235425095976938913452762442294230713428270050595858567444885260987889394008188694840969958129423983299261086192925710316657119843763653523356516951361412166567934614148268163010099832794173303920769944065845500290677252815666534817480854503310065175427941481036046770121949962023778700352966641069300573393869980793953822560780563286557826536724315420572588118450912996795888719645795243430505260846172248563003647300347406637001255730710842418311443991612664612724093725254306677829389365694822855833310747522534944846547934544902417892043003285185876567989074555628941427802041064498934769340646788643691182902000521908556437358884741309697496980390951648587360978126525878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 84) / 2 * Real.cos (169 / 2 * Real.log 84) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 84) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 84)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 84) / 2 * Real.cos (169 / 2 * Real.log 84) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 84) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 84)) / (2 * (169 / 2)) ≤ (-41424837185887753265880626273484290542810586807619151068121138927380818460945249891939445119911633289517104416201675398675521343399693736550886543498803573118921314328283989563710978000084868997469586022667492300991765275131994523246120032150191647781062376065859203528595771748816962368387192816185006694009025045908623106619979557218466012148965950201289822833865098627559001603513003240614191133303325083137730706346259560089662845801702153395427464794950853885976141855156252661868661665493634305222540356831921533138953565240752765263195559446959924345638267158717134096264649708087807697317714122995635268282008803381984984952073759190659054702754172622383622306967923767974949517617991092028993394739595776942160397264276227874765979770664502111698493714461710047 / 261832979830094465772653091878391653843162380761837789021301903876641169108419865335153043297993324028760885177613574709539046737034915520836367449634781544746980481459541025366281814002244407287594067537948876459076777842372722847925896626106856556291125594539542551341343726693766658227506377856214809126511238531971106843100849457951236285901739230383181204571686248544647332621308604365732276317890057965816055236223032733410534808222501273491298315180320887025036580605354161167623706184308747932182856851846832782785543299232874343311648420454000730041305903997572123473098095067120236555318837631254841920820262867111227090790319413085498068821665995642433699686080217361450195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_85 : (2304886114323 / 250000000000 : ℝ) ≤ Real.sqrt 85 ∧ Real.sqrt 85 ≤ (9219544457293 / 1000000000000 : ℝ) := by
  constructor
  · calc (2304886114323 / 250000000000 : ℝ) = Real.sqrt ((2304886114323 / 250000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 85 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 85 ≤ Real.sqrt ((9219544457293 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (9219544457293 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_85 : (0 : ℝ) ≤ primeTerm 85 ∧ primeTerm 85 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_85
  have hl := PsiOmega.Num.log_bound_85
  have hc := PsiOmega.Num.theta_85_cos
  have hs := PsiOmega.Num.theta_85_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_85
  have hqpos : (0 : ℝ) < Real.sqrt 85 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 85)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 85) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 85) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 85) = 2028 / 5 - 169 / 2 * Real.log 85 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (228293027491916815074614114778746223912909277236785287863622079173957819039227205573341123914229668283717160351162969936273807282439980503809105369727408309924312361077597744882618908881931006172474483214202363193426555519872537744794701813726723504043957702625991982180511872307865734060790241348860845460320278072440708834955358753 / 1277704385809208837142015508474115509204810273839693746419158868971115207612717819637887987334749778536470001784000071825419029541374949561233371685937318131651883350109331133690061494173769703759666112570342099901017904773322133966028549872252858663109622419654536649715174410868596952541374793027855007802592671305013587500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 85) / 2 ∧ (2 * (12 / 5) - Real.log 85) / 2 ≤ (2054637258061781969777587935665982963135734794442850295759163182126028762009256602018969699201521275037550872341665636172615305992968283681853107350583729386546574933555275577893097088075815810897519429212560488095813071323888560070204984133964446662254270459098795665001675531948248033763108728500556152413586297999857353707022926023 / 11499339472282879534278139576267039582843292464557243717772429820740036868514460376740991886012748006828230016056000646428771265872374546051100345173435863184866950150983980203210553447563927333836995013133078899109161142959899205694256948850275727967986601776890829847436569697817372572872373137250695070223334041745122287500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-44975469909176922552578350630448320645315783695870474229633045963082651929088085702987553650614059053558121356264501127240894750021999374589038680237976916098727970411074832480574183996008267256483898471428451613083644289527635816641094833721425544098427781117795097540310388217827084958674611808163483559379303925015933374829517036342037111227525782402579041522284812155518147658046503345861764970529374834604730980626757056387565920882244433972966939013142781768476628247976331515048482367157950043166361832803292865808691573794749573367216599074735986293973027060312555538607101433319956458815625539954034211227532175423979521781843917568466465530793206182931976287242155455464041783103446563159346265071279113267599704002376859020921366853933867382979487575950024772916341401 / 5306359096782540140056269347586718176914501139067744193521100112755102820246916536027503709953867006433679474518525525270518114410941260784748484557580704105959929079960209960503282924431737565527191206961847190057182239745341961833715265419582477904485866459461332726607118414433699777626055893170127246429117672137130554830282851544192245089670677280138857230471267942740625197713006094591200617505886247678387520128557945385082736811005692476743379603168641403072904231456853743324161863247866723890048251794442145512397850419487957179909567527151162082453252882411862833739371531216419851151030575332465249576107719825971336521639684762954711914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 85) / 2 * Real.cos (169 / 2 * Real.log 85) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 85) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 85)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 85) / 2 * Real.cos (169 / 2 * Real.log 85) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 85) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 85)) / (2 * (169 / 2)) ≤ (-622946759816520596058853317254472776102107074431280296043293391330410950172199009535913251452610021083777081897285075182994084104993428925742059342342702869784096965704529913491712822454578737342418196854184793571688064921153621017933648226941016813620185475008996119824744114950670067858289741613138001492537074004134939119911627456742687667215088241481733055493856798945241670188051452390585993305234268802515715097934542779489604156925494515679267933928009442244754790833684628601103403844691180165395565697338767604642390257568959648218926698182193947240043357287978091811816617584550623493168771628866463411694995860553967846420973436025216918457067381804426875289647118121685524972607268815077243139304921513265304595353057756770949985098295493263779312626359682614533875381451447627 / 73699431899757501945225963160926641346034738042607558243348612677154205836762729667048662638248152867134437146090632295423862700151961955343728952188620890360554570555002916118101151728218577298988766763358988750794197774240860581023823130827534415340081478603629621202876644644912496911472998516251767311515523224126813261531706271447114515134314962224150794867656499204730905523791751313766675243137308995533160001785527019237260233486190173288102494488453352820457003214678524212835581433998148942917336830478363132116636811381777183054299548988210584478517401144609206024157937933561386821542091324062017355223718330916268562800551177263259887695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_86 : (1854723699099 / 200000000000 : ℝ) ≤ Real.sqrt 86 ∧ Real.sqrt 86 ≤ (1159202311937 / 125000000000 : ℝ) := by
  constructor
  · calc (1854723699099 / 200000000000 : ℝ) = Real.sqrt ((1854723699099 / 200000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 86 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 86 ≤ Real.sqrt ((1159202311937 / 125000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1159202311937 / 125000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_86 : (7163136194981 / 100000000000000 : ℝ) ≤ primeTerm 86 ∧ primeTerm 86 ≤ (1791081137181 / 25000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_86
  have hl := PsiOmega.Num.log_bound_86
  have hc := PsiOmega.Num.theta_86_cos
  have hs := PsiOmega.Num.theta_86_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_86
  have hqpos : (0 : ℝ) < Real.sqrt 86 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 86)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 86) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 86) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 86) = 2028 / 5 - 169 / 2 * Real.log 86 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (220820986833911352419664755380532129782245150516529618758090786868287675735752729754250691063251230551675282739709940327931364014118649188235541374787583397287907272215709353944900216244399494089276387400002386080021096223192462503859938157467436534714022765071979297368007215954883302702661279743183164246423720917739819147455358753 / 1277704385809208837142015508474115509204810273839693746419158868971115207612717819637887987334749778536470001784000071825419029541374949561233371685937318131651883350109331133690061494173769703759666112570342099901017904773322133966028549872252858663109622419654536649715174410868596952541374793027855007802592671305013587500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 86) / 2 ∧ (2 * (12 / 5) - Real.log 86) / 2 ≤ (1987388892218384339539916264331283302103740678717145943956284688025506537763548936076524018928656636181910603699102578953142132392401681947260525378876636248408386476105185393075800205295329283333414864389723597589562298299509242349391269367331492708893525172264835314292707074405734248406007060784788426188948194029308303707022926023 / 11499339472282879534278139576267039582843292464557243717772429820740036868514460376740991886012748006828230016056000646428771265872374546051100345173435863184866950150983980203210553447563927333836995013133078899109161142959899205694256948850275727967986601776890829847436569697817372572872373137250695070223334041745122287500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (732250170399439881240676784622914553182923923628642182935242717302365676552900137913450127915326568841527304212596346064091610000073501377858134448284972727709817451136623011700480001838422524214885264811675434766110578566831629588537577225463343754446913358532317031804373187320793922462716407092064063589090706961700536545008770294382485902292930605299409137912267010466302494367903302315660920310186860100799807342221529021832610213303735784587043196360681384847922497247520086144984992699776950972215882161703483502815522914327046981553836889048595106533933522368167509768594745919171898648998954304037076933223689204768085345161136797833730313248894258739752008655077405712950824689807370326005322506708826916039910798602490163257659055654259094488594417379753177166767522669185243 / 5306359096782540140056269347586718176914501139067744193521100112755102820246916536027503709953867006433679474518525525270518114410941260784748484557580704105959929079960209960503282924431737565527191206961847190057182239745341961833715265419582477904485866459461332726607118414433699777626055893170127246429117672137130554830282851544192245089670677280138857230471267942740625197713006094591200617505886247678387520128557945385082736811005692476743379603168641403072904231456853743324161863247866723890048251794442145512397850419487957179909567527151162082453252882411862833739371531216419851151030575332465249576107719825971336521639684762954711914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 86) / 2 * Real.cos (169 / 2 * Real.log 86) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 86) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 86)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 86) / 2 * Real.cos (169 / 2 * Real.log 86) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 86) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 86)) / (2 * (169 / 2)) ≤ (26365379375871931033803514699798131525688396365444902663278599759936680962119240294895652060061060489224763824068382823134581685973691428891772449510468948129912211365013094031179793680463408485272752938204068224850763392619377463507862655357844014673325089274394357789745693072389404671366418839421735303455305983166429102317557043640583821053943153650756417281195711676040596163714088982156763310261205806024131304672191558052008937913125824485576169982758648620256417219866296189382468775496063192045171463131907085647742495991398597895438733175092810698703678513712703767633987204666717461105726340486311510285752467958309191680362798063191770387920012441975767837635634641222530234183239963616388821444894544343952046173388303300809159981744549526947031368701 / 191028927484171445042025696513121854368922041006438790966759604059183701528888995296990133558339212231612461082666918909738652118793885388250945444072905347814557446878567558578118185279542552358978883450626498842058560630832310626013749555104969204561491192540607978157856262919613191994538012154124580871448236196936699973890182655590920823228144382084998860296965645938662507117668219405283222230211904916421950724628086033862978525196204929162761665714071090510624552332446734759669827076923202060041737064599917238446322615101566458476744430977441834968317103766827062014617375123791114641437100711968748984739877913734968114779028651466369628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_87 : (291480595409 / 31250000000 : ℝ) ≤ Real.sqrt 87 ∧ Real.sqrt 87 ≤ (9327379053089 / 1000000000000 : ℝ) := by
  constructor
  · calc (291480595409 / 31250000000 : ℝ) = Real.sqrt ((291480595409 / 31250000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 87 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 87 ≤ Real.sqrt ((9327379053089 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (9327379053089 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_87 : (-507 / 100000000000000 : ℝ) ≤ primeTerm 87 ∧ primeTerm 87 ≤ (33 / 4000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_87
  have hl := PsiOmega.Num.log_bound_87
  have hc := PsiOmega.Num.theta_87_cos
  have hs := PsiOmega.Num.theta_87_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_87
  have hqpos : (0 : ℝ) < Real.sqrt 87 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 87)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 87) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 87) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 87) = 2028 / 5 - 169 / 2 * Real.log 87 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (1105107736979680629772590516162738242486605531714076049423119405646411052150803854411394558378224858554372666541965776973138537773912552962330568113615451049175399595805035005637673089433048107620069814098694911457437221857805922572150865699049571606760865241116985225608604394334199252649458246128418958004891594300579730852137930256506901 / 6615591719378899352620445112490071931973402636634437585628168001572515719414898470942026476118918619074515848227047499891693141379879279717340569545596313024662194503878035669536304129428928349241387145379373986473198722849211159512183445158911454598579964865826428538353303705119319207321669469231806347434616718291381037229737500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 87) / 2 ∧ (2 * (12 / 5) - Real.log 87) / 2 ≤ (9945969688671184578161674754979957535097229361182749479193052176447826157406077183886391653894789712976195919692560912442344050831005937533311859752330180644986047693181062326384963287244493148429720108656968867142897947563078952475937800747021995413284196140915741698899814155161626365929650780996277239360024704031444422361665623459029491 / 59540325474410094173584006012410647387760623729709938270653512014152641474734086238478238285070267571670642634043427499025238272418913517456065125910366817221959750534902321025826737164860355143172484308414365878258788505642900435609651006430203091387219683792437856845179733346073872865895025223086257126911550464622429335067637500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (4470620905290107165232392404963019795533434005416235556145944836674710762792572517385471976096907332851838389161331321074013438079016228613468192486041399984887160495667713327021604551998161515324496628059428680876243249447403672645667410305120561350614159530604141399783139547499973079089286325760956562059375685176279732521414948391544655444686150967384726647440957422972059734752459728143010743539920716535569956163791653445830450467059236362639279120924371228467919166339942674567174999346258113513979929567731996730169994096057493744420341633953752065640837341049419394694654736065666653658638568066756039252613088319215013626864833975173407384455513903293378783985915380963468056836279574455034272780393508489208916078435591052561172734126267633154218070662514184319314108701601463 / 28751526995848548099531783941442357305123008257466421152793165814799333493754870161856204039208335013164320563917525203286398810295244777181825387616367528443270003248127655730499187723637854579899810990571584922537199122966082919068537171139359349519316046144112036073234632660697881944321687773127875988305122482346748720484570429959850292326175605745973164221747488668617827964096073539966531072596909896880277618983517818073041275605444606406721083774718522617498392808124019510953875718286109335937264649118482771881832998020741146414387987754243955645012779894373826603112521267128803884474391722896153015234990830562250694164506793123760001766060084849030431541905272752046585083007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 87) / 2 * Real.cos (169 / 2 * Real.log 87) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 87) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 87)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 87) / 2 * Real.cos (169 / 2 * Real.log 87) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 87) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 87)) / (2 * (169 / 2)) ≤ (40241281445727585438219624760578771284982597748377477668976556112080145341152227890590734669982511161111952632126897907422238655379881458315142921544020898933547171055409217775165780725353948143647245952419459937265579061160422026158045738350720847583497046084103392851908416731212233535911163766316124042299423812455461134875259552013248679175729685208682380579566210636001355642239820486365724380674114939171680872255339414899068286333748420450801879241080681768861921077486365534371450829715215463114298737707413490478389863904346881064365225792243503163098596357581259630826026666780474731870558592864380572410420945995386739996488442603374024065699601099126144275537260156435622985078932174067062782073793903042527884163089228178365446577861641233076327352742038216095489839267655791 / 258763742962636932895786055472981215746107074317197790375138492333194001443793831456705836352875015118478885075257726829577589292657202994636428488547307755989430029233148901574492689512740691219098298915144264302834792106694746271616834540254234145673844415297008324659111693946280937498895189958150883894746102341120738484361133869638652630935580451713758477995727398017560451676864661859698779653372189071922498570851660362657371480449001457660489753972466703557485535273116175598584881464574984023435381842066344946936496982186670317729491889788195600805115019049364439428012691404159234960269525506065377137114917475060256247480561138113840015894540763641273883877147454768419265747070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_88 : (4690415759823 / 500000000000 : ℝ) ≤ Real.sqrt 88 ∧ Real.sqrt 88 ≤ (9380831519647 / 1000000000000 : ℝ) := by
  constructor
  · calc (4690415759823 / 500000000000 : ℝ) = Real.sqrt ((4690415759823 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 88 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 88 ≤ Real.sqrt ((9380831519647 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (9380831519647 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_88 : (-321 / 100000000000000 : ℝ) ≤ primeTerm 88 ∧ primeTerm 88 ≤ (131 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_88
  have hl := PsiOmega.Num.log_bound_88
  have hc := PsiOmega.Num.theta_88_cos
  have hs := PsiOmega.Num.theta_88_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_88
  have hqpos : (0 : ℝ) < Real.sqrt 88 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 88)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 88) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 88) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 88) = 2028 / 5 - 169 / 2 * Real.log 88 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (1067303944220404602061892900281451713133976422201773018906651548306010397490660024313961930309818768616334960243124260461832557144029847785723205693492390043261819107009870667226533635253441208743606103380452670824611840920065457223031905965446150297233313442329317925335405059302405105640562684650541642849623030942546813016181356231506901 / 6615591719378899352620445112490071931973402636634437585628168001572515719414898470942026476118918619074515848227047499891693141379879279717340569545596313024662194503878035669536304129428928349241387145379373986473198722849211159512183445158911454598579964865826428538353303705119319207321669469231806347434616718291381037229737500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 88) / 2 ∧ (2 * (12 / 5) - Real.log 88) / 2 ≤ (9605735554200473483908320950578247718847020144262814456386937528762708142206377660014893788274319919177801395290905001389255286344054872136706631250366123163215954847146796163721788488954349864363069602561271870171490867897729471711105315872897597249674185914716230217585436192500937812791335751265119348760708825439403975009211636259029491 / 59540325474410094173584006012410647387760623729709938270653512014152641474734086238478238285070267571670642634043427499025238272418913517456065125910366817221959750534902321025826737164860355143172484308414365878258788505642900435609651006430203091387219683792437856845179733346073872865895025223086257126911550464622429335067637500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (601566697814188552112195046409891340636970132472446922613832647801481424980518910962736900241494623573976070677837849499816109159096358970897583057577965210849521726793798137615086899316123127057469812197754428922987049076091753881884216669795683647453498559527957601367409707107071394252423791507134425307093224589234169595416841052385807334206580585469397735977153436211272054960095056585333220445973400588529533493640189177875762735020765437875682431551921045538830527060632597721137103550543246487131098810396293915385841808170479485731787069030998400229196556728262802193153573208244175648793836349313867698427597441188675128224067940680691098081031508317581882837118664800923300999317851155268095985385776969384361055004559462647304161126111186149441927200553136577755983794934343636700793 / 14567103704794081220482140529875958277758649938825786687811530208599277193454830069653013882836433050132445615420531481042452630817766897101002817779183089887762842874500854465963871558019362902697070617556115709003768426518451033100939917963232951418167776330290205570506884040758890428969449907840164232710424045533037956663865211926294565845371137856471037591347328479613385095972416159816152501745664238286742791237332108901258496073420828265783389908563795328739930668939193905375022806078405200057171477540990990540434439239033730915134297097339358049849052709983843476159692221366982836626882185055287960427753352057621003793972494125334291981836914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 88) / 2 * Real.cos (169 / 2 * Real.log 88) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 88) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 88)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 88) / 2 * Real.cos (169 / 2 * Real.log 88) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 88) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 88)) / (2 * (169 / 2)) ≤ (216676374355556515580880012256773448188281394141642823184345122463468377798352617605246563902676171213626088259929827105790817959246289186915646236568972095138091776848809345985375678821090423202869892734278367372009471137517072012586889196208540847138449759650510557504038552966162298189394268673985967778489681257125688473916967134228034180684458210009246641497441429265078160339255546543254489232497314823474733892037137628603439421132962129778227962446891912363280193897051409671637596795016211813299118555180357992986458876273125263442284711493971015802555325640458947529472696318038495794040932939073574502803241414117902181012555396650226767365840431897266535710118225709312216398141604223910845646236930198062317345634453130856848404492133571902970715506080198261780956672171561 / 5244157333725869239373570590755344979993113977977283207612150875095739789643738825075084997821115898047680421551391333175282947094396082956361014400505912359594623434820307607746993760886970644970945422320201655241356633546642371916338370466763862510540399478904474005382478254673200554429001966822459123775752656391893664398991476293466043704333609628329573532885038252660818634550069817533814900628439125783227404845439559204453058586431498175682020367082966318346375040818109805935008210188225872020581731914756756594556398126052143129448346955042168897945658975594183651417489199692113821185677586619903665753991206740743561365830097885120345113461289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_89 : (1179247641507 / 125000000000 : ℝ) ≤ Real.sqrt 89 ∧ Real.sqrt 89 ≤ (9433981132057 / 1000000000000 : ℝ) := by
  constructor
  · calc (1179247641507 / 125000000000 : ℝ) = Real.sqrt ((1179247641507 / 125000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 89 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 89 ≤ Real.sqrt ((9433981132057 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (9433981132057 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_89 : (4667410605851 / 100000000000000 : ℝ) ≤ primeTerm 89 ∧ primeTerm 89 ≤ (4668399916441 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_89
  have hl := PsiOmega.Num.log_bound_89
  have hc := PsiOmega.Num.theta_89_cos
  have hs := PsiOmega.Num.theta_89_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_89
  have hqpos : (0 : ℝ) < Real.sqrt 89 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 89)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 89) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 89) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 89) = 2028 / 5 - 169 / 2 * Real.log 89 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (1029927322104646223492946183579685068303046004316304156128920615437259939241316969519072023182356809278249169434548666687591054214126796384885974049939783780714258972553208457328434394101045043622016603220800630503935864565561483121537206065698896398038365393730221388128123563364387029651765556277256139721581029803384862363121590606506901 / 6615591719378899352620445112490071931973402636634437585628168001572515719414898470942026476118918619074515848227047499891693141379879279717340569545596313024662194503878035669536304129428928349241387145379373986473198722849211159512183445158911454598579964865826428538353303705119319207321669469231806347434616718291381037229737500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 89) / 2 ∧ (2 * (12 / 5) - Real.log 89) / 2 ≤ (9269345955501383296523539971005675990620821443318058382224848981285011024283812019858619461602673341025228403925259730710915644904996083943997647452687194467940959006378434140065589649780180203130530142982251510391851490311710096983173542234028444342224850383922865340692391134536689291408510681475900925486510199636608860217561636259029491 / 59540325474410094173584006012410647387760623729709938270653512014152641474734086238478238285070267571670642634043427499025238272418913517456065125910366817221959750534902321025826737164860355143172484308414365878258788505642900435609651006430203091387219683792437856845179733346073872865895025223086257126911550464622429335067637500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-6978978998845895891029920998814595227788941522453745757679614765113072217371224892220147431954280540454972870929475143760892346165756596773239421626266671844831988672468125965911694811008915284607662765831217707393911777661858309607392570078623223456952928063904599981597377698023275693399132863396707010616821341465498544138272515579492021201089135352288222160535199026687081202415429438116241443213647220550388728024815893461127820768089956005190989199165501814605518657637614916320099778358492491397500795669653199450422081688829167077226826524864208103820355444543323912710209355826181894485076700137027718646920290724872260245905186386905859079487999072386859362054168742274620397086071048073810866466776993785749271477443195957603151515636311514412954001320270042358350295847 / 71128436058564849709385451806034952528118407904422786561579737346676158171166162449477606849787270752599832106545563872277600736414877427250990321187417431092592006223148703447089216591891420423325540124785721235369963020109624185063183193179848395596522345362745144387240644730268019672702392128125801917531367409829286897772779355108860184791851259064799988239000627341862231913927813280352307137430001163509486285338535687994426250358500138016520458537909156878612942719429657741088978545304712890904157605180620070998215035346844389234054185045602334227778577685467985723435997174643470881967198169215273244276139414343852557587756318971358847567563056945800781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 89) / 2 * Real.cos (169 / 2 * Real.log 89) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 89) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 89)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 89) / 2 * Real.cos (169 / 2 * Real.log 89) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 89) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 89)) / (2 * (169 / 2)) ≤ (-193819445599093674914593608815064384682931564836506272835338637044266393617156738621694268049164804297244348280281328965935603474431592088032834360463238391133870749003788304195823510718453242652815984715202907891018235784395073482357619477873397275622731787050704162121583464566856731615331785566368807168668821562475275160225454405744181543313941409625345599174695833657269294141226539019123647258028099364881236260641129436405689784676700386826941795684296848438551624514656322768192255971292466687447236001306719726160580328309757905489814914895471874187125083889596374514716769479617594341903647999648919443815082384044032370253521776986340672243655644628891920929645005662698438435766219383757200102105216304424780035824647789570618840708362726697205363887518210206918075907653320247845438328795647 / 1975789890515690269705151439056526459114400219567299626710548259629893282532393401374377968049646409794439780737376774229933353789302150756971953366317150863683111283976352873530256016441428345092376114577381145426943417225267338473977310921662455433236731815631809566312240131396333879797288670225716719931426872495257969382577204308579449577551423862911110784416684092829506442053550368898675198261944476764152396814959324666511840287736114944903346070497476579961470631095268270585804959591797580302893266810572779749950417648523455256501505140155620395216071602374110714539888810406763080054644393589313145674337205953995904377437675526982190210210084915161132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_90 : (1897366596101 / 200000000000 : ℝ) ≤ Real.sqrt 90 ∧ Real.sqrt 90 ≤ (4743416490253 / 500000000000 : ℝ) := by
  constructor
  · calc (1897366596101 / 200000000000 : ℝ) = Real.sqrt ((1897366596101 / 200000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 90 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 90 ≤ Real.sqrt ((4743416490253 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (4743416490253 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_90 : (0 : ℝ) ≤ primeTerm 90 ∧ primeTerm 90 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_90
  have hl := PsiOmega.Num.log_bound_90
  have hc := PsiOmega.Num.theta_90_cos
  have hs := PsiOmega.Num.theta_90_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_90
  have hqpos : (0 : ℝ) < Real.sqrt 90 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 90)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 90) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 90) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 90) = 2028 / 5 - 169 / 2 * Real.log 90 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (5695009957948001317375335701753466489975951494820075973157142465777115504753506738940257336691266719289289987620866202827713224649108376394360784484026123230995977652151398391402593795245514269025991749907513788240567656756043455021178978744058761403232658653914864843497473439061741299596291935807126690619289351605099443549135855204095183074439 / 37942661196230857234158791051023696664252403104592318627919071437970910733673324381434171187517402593804214650454666380981323449788535448254772344797070812346553045963677349218882676989374780489609748108992993420205209089907271882385446688174266063105965017113604082826730698518815331103201056451994478984889307214468571026684165443512500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 90) / 2 ∧ (2 * (12 / 5) - Real.log 90) / 2 ≤ (51255089947778616210386160215788735707204197370766803608408317068524724339965781044301420625317450117022536164755365077037044889367776787440634588622644821253018145533211165180354115781968930020115014325834342560132041872487400355430530196095604849959789829547789683729759338981109852705443831775203997678056460629586506491283315874990225941882449 / 341483950766077715107429119459213269978271627941330867651271642941738196603059919432907540687656623344237931854091997428831911048096819034292951103173637311118977413673096142969944092904373024406487732980936940781846881809165446941469020193568394567953685154022436745440576286669337979928809508067950310864003764930217139240157488991612500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-4181994933678736669423136378636800887399889674645061355079370844444094649013047599772783333133666273149843196203891656653720325151559750674817457685726732700875105713453096395212548216975651807521805962170382840595689263161868241222620924733527091430314288087589504116834693389116580032171209689906658557938111576187775053163014344548942153581208633687362914063638497691096722373814273319861236646420492960078155923597658646566335423357742479872602100467176146733948381195123224505580030128577964607395965797619872696551076159951930311136879023391101473403274353131263376737910552004366774364446878386799660380861781583578116661711636452630674873023112707426658760895670760155297450693634760933769090818547988212994873927725455216726497386117683692472456463524985018800510266123828932574028150373 / 28262712321407906424721530564953943889565298566263689946698116804190851884254661444008181955651900612943148752842116736246577465979068501804599361783720775911357351592038692681756732510586667616001888545956076531617409929842275075130938435134878083347451750576352454359821734195698179220521829179553579898630296428353416415684562741706388246894754852993101811298885935123184291553198045337763561791376278654097892973327475767112381748534011043362220741401927476542472206918948953446591441090685999675625340439856571984147304324405325766759791513714630819689009447312677250048461911536971394164188519784709366865418678407408501081028758019290022319211613803605827461689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 90) / 2 * Real.cos (169 / 2 * Real.log 90) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 90) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 90)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 90) / 2 * Real.cos (169 / 2 * Real.log 90) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 90) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 90)) / (2 * (169 / 2)) ≤ (-1451884910660820092625208139060667763975084952674269262146485052269894107579034383111602374957712568491676527875989170204015272779917972880631516358830428019091658979357269972742276234019861289600806364148960492615084748238499813544618824948939568924033721579115296741244266669491062154424533974968554608221121548083727877268831132553949507508498843204275947092378713587244499945235071600024048719960464526367981191166828743001672324501540507103257434802909222375344839975039772530651180375609181144523054988373656637825069042875398599522535464275703177748980116440411737144399459054165950968988474275155749610734780367282657578951132849949274458682026017180800990023741871681916969911001076065277428934108341596364987282372838450465400277967086591714078617027236736783908483054514075026538144487 / 9813441778266634175250531446164563850543506446619336787047957223677379126477313001391729845712465490605259983625734977863394953464954340904374778397125269413665747080568990514498865455064815144445100189568082129033822892306345512198242512199610445606754080061233491097160324373506312229347857354011659687024408482067158477668250951981384807949567657289271462256557616362216767900415987964501236733116763421561768393516484641358465884907642723389659979653447040466136182957968386613399805934265972109592132097172420827828925112640738113458260942262024590169794946983568489600160385950337289640343236036357419050492596669239062875357207645586813305281810348474245646420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_91 : (9539392014169 / 1000000000000 : ℝ) ≤ Real.sqrt 91 ∧ Real.sqrt 91 ≤ (953939201417 / 100000000000 : ℝ) := by
  constructor
  · calc (9539392014169 / 1000000000000 : ℝ) = Real.sqrt ((9539392014169 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 91 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 91 ≤ Real.sqrt ((953939201417 / 100000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (953939201417 / 100000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_91 : (-3967525247429 / 100000000000000 : ℝ) ≤ primeTerm 91 ∧ primeTerm 91 ≤ (-495814928827 / 12500000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_91
  have hl := PsiOmega.Num.log_bound_91
  have hc := PsiOmega.Num.theta_91_cos
  have hs := PsiOmega.Num.theta_91_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_91
  have hqpos : (0 : ℝ) < Real.sqrt 91 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 91)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 91) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 91) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 91) = 2028 / 5 - 169 / 2 * Real.log 91 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (32526881870890887197678014826654201129090854860753000519393873514838316432947811607054144778284069086010351390382807782314369643870298921254695223989698007544964651080540749983469466685712393777513912275321995317151638576700594320160414672751013049575838791043600779673854981118884500952780944767556971798538456927201843079785412982892951444041506990299 / 224990153744399159606537983805688306081580709037828360053035462587665066184802792190889843691640630373987197585601703880626573894472519977469702018609327475874661805325702088434526583933652200235238997361568221796521056753995836279128161030181160619308028106544239787705060918965658540271226535686706193810336505451230078828341189881179255262500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 91) / 2 ∧ (2 * (12 / 5) - Real.log 91) / 2 ≤ (292741938782999658748785252205154874452324574961332862463647548410602268460747983414902321997208640784774970322016783975509618417507520841346199850765724601859687212603766914055832199795417092289484411714054458190925587794427970941945873828624589301366494106426559555959759672569515581084990174577546452277823612899344433483768941210529869716843975015709 / 2024911383699592436458841854251194754734226381340455240477319163288985595663225129718008593224765673365884778270415334925639165050252679797227318167483947282871956247931318795910739255402869802117150976254113996168689510785962526512153449271630445573772252958898158089345548270690926862441038821180355744293028549061070709455070708930613297362500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-28068618108045996288869062687603003777262759238038378358522915722986804710055872580127535899398867144323648567061482223570789650907370977120215402242277902914291450648092522169426006544939413018640771196275087306676087701176422845565762156776794648886749862871466823929232773963145849033383646204307298892912477386668319050732069177898441902166724912742643609565857215747609215035444657425207972794102583761495753966334511961520642309772825676056033370805319735273101006177730004060986213544793834726130300399584010061109492649599744556671378493717229821112525122279191564708780314453434419672594676122870409159140451139737135688096942649599623578468807061223996465053650967691147390612925209545753008228133429362929530458128667799603834423278484740584662900075810783503129734751166326454833222570808064281 / 361530924675397448425273195216867440351869643308789050535132381791785576045799221554751509496773330997523180342944054087338702322339909155042084241976818511540064918909580082071041618263163550037361813606400161392021763384604201049362858096612113247823370719354887805035774018657579421461675805579705230432395323233021604138390427410781163838183448542874263929558443991071353745763788096379071842055705255043214931484378111129007347733996387668978355025016053374981960001406276188618284533792542303121103567861025332671464152541477492423143944920831148215329131494030414149963616008286471438603454250137108111598818192526457421235146173644121026377135294880597117117869477291859241668134927749633789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 91) / 2 * Real.cos (169 / 2 * Real.log 91) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 91) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 91)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 91) / 2 * Real.cos (169 / 2 * Real.log 91) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 91) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 91)) / (2 * (169 / 2)) ≤ (-19487154428466995879366956274342136607966083750935344609976440741942542214862284232346898988898960238544432998889303643889075631253096441480948147692943468404545548121169374659838284278425179171534476113268628725883002028976483875260809072284486203226407926050628448803054602958294876113093717255900366103860641014616970987788355165425306309954276113777216068364724849366483879388043803682484196868457362950341142165569258160699996429081966000518562737029770694887803176293951253658119467743836367272036827624628185235735876774614732077680678533770542472784961532377756459464464574083669869965655185677512440211212519397962731189876495226578338133996895238743609321324686788908113268097010386083197205852539644270233124783895811641876083191467158136004960780899332718942671810158024105276165879801352651689700637267 / 251063142135692672517550830011713500244353918964436840649397487355406650031805014968577437150537035414946653015933370893985209946069381357668114056928346188569489527020541723660445568238308020859279037226666778744459557905975139617613095900425078644321785221774227642385954179623319042681719309430350854466941196689598336207215574590820252665405172599218238839971141660466217879002630622485466556983128649335565924641929243839588435926386380325679413211816703732626361112087691797651586481800376599389655255459045369910738994820470480849405517306132741816200785759743343159696955561310049610141287673706325077499179300365595431413295953919528490539677288111525775776298248119346695602871477603912353515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_92 : (76733304373 / 8000000000 : ℝ) ≤ Real.sqrt 92 ∧ Real.sqrt 92 ≤ (4795831523313 / 500000000000 : ℝ) := by
  constructor
  · calc (76733304373 / 8000000000 : ℝ) = Real.sqrt ((76733304373 / 8000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 92 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 92 ≤ Real.sqrt ((4795831523313 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (4795831523313 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_92 : (-675660989203 / 100000000000000 : ℝ) ≤ primeTerm 92 ∧ primeTerm 92 ≤ (-84423502157 / 12500000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_92
  have hl := PsiOmega.Num.log_bound_92
  have hc := PsiOmega.Num.theta_92_cos
  have hs := PsiOmega.Num.theta_92_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_92
  have hqpos : (0 : ℝ) < Real.sqrt 92 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 92)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 92) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 92) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 92) = 2028 / 5 - 169 / 2 * Real.log 92 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (31297415240353426828423575691363522495563411399711582999876832813296680527020155088272578429976502307555929377797600399737857639429768887653399526735325727484519555062766272422917899058390038860901858869289166032697033500378322900304219215630607264134275648548751575920308077059369657875077084008283836582397124764786814856875105127625734569822756990299 / 224990153744399159606537983805688306081580709037828360053035462587665066184802792190889843691640630373987197585601703880626573894472519977469702018609327475874661805325702088434526583933652200235238997361568221796521056753995836279128161030181160619308028106544239787705060918965658540271226535686706193810336505451230078828341189881179255262500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 92) / 2 ∧ (2 * (12 / 5) - Real.log 92) / 2 ≤ (281676739118029025001491837946306046314774025857314591880153596222113885992389267670297991034601515639981281879650716142382719090138531495152061221244779915424270678837375974128486339307512245993864958697222390451798682150362582365960586718259384555839267418432465736559725670503438693482567461963141625500968140400337329335685189381579763066843975015709 / 2024911383699592436458841854251194754734226381340455240477319163288985595663225129718008593224765673365884778270415334925639165050252679797227318167483947282871956247931318795910739255402869802117150976254113996168689510785962526512153449271630445573772252958898158089345548270690926862441038821180355744293028549061070709455070708930613297362500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (13017654806762267188622971504767464171190702181532525394952039421333937434157135271524505278065787352674154884837243795234947278480344040594587511455410793909212061669316270170213535175264695272481356606270937599760891725261546068524196255207288311928920823231411740880782158582060222543619062979734675565009240500160143897380294223972569414401055900161427158458579157529363423843406450528711739044311931326563542506363532173250402189690991370325609866778842770993814355721197027100620076724931928817664011728652011465190549120406426096818027423160697134890274335502481761803429883933092944389247346301240090202037157501484068649976127657613853311234903616887062722643169848791515889170579560774135028512265938521770884448500118341611208378173632546842543427675951707258448381458478437046401124261537747600871389736598675984253 / 278959046817436302797278700013015000271504354404929822943774985950451833368672238853974930167263372683274058906592634326650233273410423730742348952142606876188321696689490804067161742487008912065865596918518643049399508784416821797347884333805642938135316913082475158206615755137021158535243677144834282741045774099553706896906193989800280739339080665798043155523490733851353198891811802761629507759031832595073249602143604266209373251540422584088236902018559702918179013430768664057318313111529554877394728287828188789709994244967200943783908117925268684667539733048159066329950623677832900156986304118138974999088111517328257125884393243920545044085875679473084195886942354829661780968308448791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 92) / 2 * Real.cos (169 / 2 * Real.log 92) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 92) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 92)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 92) / 2 * Real.cos (169 / 2 * Real.log 92) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 92) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 92)) / (2 * (169 / 2)) ≤ (1875299925493089632794122551468454657585673325383560546822058222022523721842944438132315902364547457254046098588721693083032038251720837968182068699962601811122499658516716864918884312537456951957179476712429263134209517941531604686812778285709858814839662363385381920503582132109795050406567782071371143182956673234085769915397320135654971347848335599324377723182414687127976799097022391626318714418641425613398447998239727018837480079310735882008697913429363049244698420192197963056294134333260513708137082298746965958697825745177065351053031263987577655559752270987801963017134026124210270086336614944161789447617780914707805449423751772144408596960461565275619780700294197913291508997973568846308862678122373480512282289916247224813521202936503811010108977572656878786104025682802608685784812362676653 / 40170102741710827602808132801874160039096627034309894503903597976865064005088802394972389944085925666391464482549339343037633591371101017226898249108535390171118324323286675785671290918129283337484645956266684599113529264956022338818095344068012583091485635483876422781752668739731046829075089508856136714710591470335733793154491934531240426464827615874918214395382665674594860640420899597674649117300583893690547942708679014334149748221820852108706113890672597220217777934030687624253837088060255902344840873447259185718239171275276935904882768981238690592125721558934905551512889809607937622606027793012012399868688058495269026127352627124558486348366097844124124207719699095471296459436416625976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_93 : (301364086281 / 31250000000 : ℝ) ≤ Real.sqrt 93 ∧ Real.sqrt 93 ≤ (9643650760993 / 1000000000000 : ℝ) := by
  constructor
  · calc (301364086281 / 31250000000 : ℝ) = Real.sqrt ((301364086281 / 31250000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 93 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 93 ≤ Real.sqrt ((9643650760993 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (9643650760993 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_93 : (-663 / 100000000000000 : ℝ) ≤ primeTerm 93 ∧ primeTerm 93 ≤ (401 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_93
  have hl := PsiOmega.Num.log_bound_93
  have hc := PsiOmega.Num.theta_93_cos
  have hs := PsiOmega.Num.theta_93_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_93
  have hqpos : (0 : ℝ) < Real.sqrt 93 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 93)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 93) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 93) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 93) = 2028 / 5 - 169 / 2 * Real.log 93 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (30081240401320157780149309055210021185739098380874823472483712019059639783570537234543554331030929288328963081968981287581234071940260437272419005972114856691855441831551264601628970965541364229615575175328632415478233361976303969255017252411523478545679564005920302735649073139005465724248836203766652066764134901402585382871057673916411303154006990299 / 224990153744399159606537983805688306081580709037828360053035462587665066184802792190889843691640630373987197585601703880626573894472519977469702018609327475874661805325702088434526583933652200235238997361568221796521056753995836279128161030181160619308028106544239787705060918965658540271226535686706193810336505451230078828341189881179255262500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 93) / 2 ∧ (2 * (12 / 5) - Real.log 93) / 2 ≤ (270731165576074189657439926774103245683704254251525526025745540238072933629169330533626849459942770042628544075706590954466245467084958141768050422533833843327657198637448567989255043298049427217632917494641830765535078719992048820877406778543333377311762507512660932370088017492220582990763956964897930483178815684939386671466086065018866987243975015709 / 2024911383699592436458841854251194754734226381340455240477319163288985595663225129718008593224765673365884778270415334925639165050252679797227318167483947282871956247931318795910739255402869802117150976254113996168689510785962526512153449271630445573772252958898158089345548270690926862441038821180355744293028549061070709455070708930613297362500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (34188555212038312915945487900113113125409768728234241401396910066666325995183264859282065566135486119112734075289152505053254866420377451511127793836709041299569315360706044858514229076422935219647857105068593799813747128983242413063333162905977376873561606793023404300487609158296459385689538188223848880456969825271349868075421691269882969074975513169590479149704130607764469515763114662791785567027702527335747022300436074042086458795963231001373159911827798868319877888236109625625315984813526733399031802334695883871632079957198173987157010311520143742977026246949827636671459196089878432478419090341579481257373263505999486237952901531291007168569897374245808226940151901335038013765120636319547729693445929950170921861197235860198277350975702546420533724060902460118187019639843836447223300734713021865212278027 / 272420944157652639450467480481459961202640971098564280218530259717238118524093983255834892741468137386009823150969369459619368431064866924553075148576764527527657906923330863346837639147469640689321871990740862352929207797282052536472543294732073181772770422932104646686148198375997225132073903461752229239302513769095416891509955068164336659510820962693401519065908919776712108292784963634403816170929524018626220314593363541220091065957443929773668849627499709881034192803485023493474915147978080934955789343582215614951166254850782171663972771411395199870644270554842838212842405935383691559556937615370092772546983903640876099496477777266157269615112968235433785045842143388341582976863719522953033447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 93) / 2 * Real.cos (169 / 2 * Real.log 93) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 93) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 93)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 93) / 2 * Real.cos (169 / 2 * Real.log 93) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 93) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 93)) / (2 * (169 / 2)) ≤ (19695473460581402464385121558850322188242804903738249766911438556914485054785391887728207169953351171327036174542179817591569748171134648858568019671408715219547952798452265583511186833604636528349261428315059256901353482638103861748109847321723470055027719550819087221345002705307889911913894230407019698325525643211562565047444614763531644597140257367778458279271955874658026811730538573756371283076846906546662233907017955358643569093659703765374806669330822231626531393949254622484457620918394215342041683747428581953760477290253796182111969908981537464449598955855917723103435972995518644410807831226289556322015763606462459650009354373308731834560045431391118230658564500615970405147801093362533470013218920336576116391607919257901936571410752737242128107538768110682575803280344601484111149 / 156914463834807920323469268757320937652721199352773025405873429597129156269878134355360898219085647134341658134958356808740756216293363348542571285580216367855930954387838577287778480148942513037049398266666736715287223691234462261008184937765674152701115763608892276491221362264574401676074568393969284041838247930998960129509734119262657915878232874511399274981963537791386174376644139053416598114455405834728702901205777399742772453991487703549633257385439832891475695054807373532241551125235374618534534661903356194211871762794050530878448316332963635125491099839589474810597225818781006338304796066453173436987062728497144633309971199705306587298305069703609860186405074591684751794673502445220947265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_94 : (605959982177 / 62500000000 : ℝ) ≤ Real.sqrt 94 ∧ Real.sqrt 94 ≤ (9695359714833 / 1000000000000 : ℝ) := by
  constructor
  · calc (605959982177 / 62500000000 : ℝ) = Real.sqrt ((605959982177 / 62500000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 94 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 94 ≤ Real.sqrt ((9695359714833 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (9695359714833 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_94 : (-5325264431579 / 100000000000000 : ℝ) ≤ primeTerm 94 ∧ primeTerm 94 ≤ (-2662183598239 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_94
  have hl := PsiOmega.Num.log_bound_94
  have hc := PsiOmega.Num.theta_94_cos
  have hs := PsiOmega.Num.theta_94_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_94
  have hqpos : (0 : ℝ) < Real.sqrt 94 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 94)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 94) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 94) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 94) = 2028 / 5 - 169 / 2 * Real.log 94 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (28878073029174044287229907077253150651255043101924455765481929766317001787942569892882755347787652679881714807147185944514013906684095069965714335005549575916703300107769994398588759754163372708829307887745460390349552559110888379131391324821179111039309934516132214699299100778380246710269433955417796674473114228761533642988175570122573282841506990299 / 224990153744399159606537983805688306081580709037828360053035462587665066184802792190889843691640630373987197585601703880626573894472519977469702018609327475874661805325702088434526583933652200235238997361568221796521056753995836279128161030181160619308028106544239787705060918965658540271226535686706193810336505451230078828341189881179255262500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 94) / 2 ∧ (2 * (12 / 5) - Real.log 94) / 2 ≤ (259902659235614613603904341410678766210713523260115488320947029941414411131864097163522631076447425769966761474228871016405549409421054853035589525065931106477741840142028519998625612677538830579658020828240405846215661190693052356459291703653819227842614686623168845498692895997973054900823714978609552504889359562896236255555943400207228637243975015709 / 2024911383699592436458841854251194754734226381340455240477319163288985595663225129718008593224765673365884778270415334925639165050252679797227318167483947282871956247931318795910739255402869802117150976254113996168689510785962526512153449271630445573772252958898158089345548270690926862441038821180355744293028549061070709455070708930613297362500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (14320757595567396738362832956959652711693626491462958262934969984512868472303585221988701220009119100981206475365574420470817459297001433228871371801513820626123809628183606702246441716250669997687824739905830857706344328691115467954439000507585893134572972708761977162234638788166728197421677848799663437894690409529402905430126078314953183186367106259360947861845688597644107055068817771677587035032481232879135125791221661094600104271157653432520479914908439150683352932674479839090378568221793505829232309512125343675102884543233080567198640602456893394471769680736796384106648384852306208010676207022244501043264389589946503361030479835891276082233989288202772204787209570541589428882104997532472171997739663306480535992019800252771847915514156359314922073511925523864690625006711423350801830176562235869383962263 / 136210472078826319725233740240729980601320485549282140109265129858619059262046991627917446370734068693004911575484684729809684215532433462276537574288382263763828953461665431673418819573734820344660935995370431176464603898641026268236271647366036590886385211466052323343074099187998612566036951730876114619651256884547708445754977534082168329755410481346700759532954459888356054146392481817201908085464762009313110157296681770610045532978721964886834424813749854940517096401742511746737457573989040467477894671791107807475583127425391085831986385705697599935322135277421419106421202967691845779778468807685046386273491951820438049748238888633078634807556484117716892522921071694170791488431859761476516723632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 94) / 2 * Real.cos (169 / 2 * Real.log 94) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 94) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 94)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 94) / 2 * Real.cos (169 / 2 * Real.log 94) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 94) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 94)) / (2 * (169 / 2)) ≤ (257817075307674125385155654657205659013063291904653778897336926954985741636434211830237074246039822136876236370463428204933000929708588859709321065568225022836859789895010102837741861509189387770255249999364942755896036806257923868944077702944664017823045741845874717519773686396387439799021754542738154257236140656833052055071637155659783141145700589965165956963134978192207821814818308460773775575177289171624555784206661626742293415257196692571401156808846350703542124211477951201919883910581889767842347558003827778359342513697423285725010864438799137104925178632273652879464213355979558676467598510269363547082320663799714713061050961117379151286986360635029589943080362714438329271633871794512842304446626524171215207060109289317748948987965459712798910481370465898050335641746123813407493620295392757929696676463 / 2451788497418873755054207324333139650823768739887078521966772337455143066716845849302514034673213236474088408358724325136574315879583802320977676337190880747748921162309977770121538752327226766203896847916667761176362870175538472828252889652588658635954933806388941820175333785383975026188665131155770063153722623921858752023589595613479029935597388664240613671593180277990408974635064672709634345538365716167635982831340271870980819593616995367963019646647497388929307735231365211441274236331802728414602104092239940534560496293657039544975754942702556798835798434993585543915581653418453224036012438538330834952922855132767884895468299995395415426536016714118904065412579290495074246791773475706577301025390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_95 : (1218349293101 / 125000000000 : ℝ) ≤ Real.sqrt 95 ∧ Real.sqrt 95 ≤ (9746794344809 / 1000000000000 : ℝ) := by
  constructor
  · calc (1218349293101 / 125000000000 : ℝ) = Real.sqrt ((1218349293101 / 125000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 95 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 95 ≤ Real.sqrt ((9746794344809 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (9746794344809 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_95 : (0 : ℝ) ≤ primeTerm 95 ∧ primeTerm 95 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_95
  have hl := PsiOmega.Num.log_bound_95
  have hc := PsiOmega.Num.theta_95_cos
  have hs := PsiOmega.Num.theta_95_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_95
  have hqpos : (0 : ℝ) < Real.sqrt 95 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 95)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 95) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 95) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 95) = 2028 / 5 - 169 / 2 * Real.log 95 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (27687637825818895249289550029204087250749525069573639437489399136894100209929808047794375299291681495144277380040599770327352591991626928235777151920872547786962359463616564095949094854220752240599722470418037291020146290044662211699371246656142936483395364410393708792790609548708914214549375243237966039859671117398527636670656882293890316279006990299 / 224990153744399159606537983805688306081580709037828360053035462587665066184802792190889843691640630373987197585601703880626573894472519977469702018609327475874661805325702088434526583933652200235238997361568221796521056753995836279128161030181160619308028106544239787705060918965658540271226535686706193810336505451230078828341189881179255262500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 95) / 2 ∧ (2 * (12 / 5) - Real.log 95) / 2 ≤ (249188742413814982361211284817961405237720217066866557619152970641120848920391762219227927720957823809180738561175004701200156394495748308059128145528728558501369283646683627680604686460260610269072343418591154607403054615846807984171730543534884300227883800914256826465104478033867714789375458152968247490902699601557581181571916720588910787243975015709 / 2024911383699592436458841854251194754734226381340455240477319163288985595663225129718008593224765673365884778270415334925639165050252679797227318167483947282871956247931318795910739255402869802117150976254113996168689510785962526512153449271630445573772252958898158089345548270690926862441038821180355744293028549061070709455070708930613297362500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (365032132538786321299122450599049092180915325480848880251741683280164241902860604691841669762941508351883336287556587477677063517665816096997392318216527894239048498203327647379403765608996843183419512056885642456948872301793673133544295004681859183424257572947565185296867379698136035167515885463521997292134609930981096747492050813618706733649108240751104061694731766498895799403493000735116395128972882801732119100827043720159077100046055202151128172023480930223383963988249339293425499728758297541337762436814288761689433388980208585046866442335632991643894980849297135274104662774452348334061308037681271918481150632449590485027140707317791140828222850284910465804430027449423040089809108195674220764474602507703526831641195691704559987836595159194300856490797760884839604484240112558530943369352438556256774248235751 / 34052618019706579931308435060182495150330121387320535027316282464654764815511747906979361592683517173251227893871171182452421053883108365569134393572095565940957238365416357918354704893433705086165233998842607794116150974660256567059067911841509147721596302866513080835768524796999653141509237932719028654912814221136927111438744383520542082438852620336675189883238614972089013536598120454300477021366190502328277539324170442652511383244680491221708606203437463735129274100435627936684364393497260116869473667947776951868895781856347771457996596426424399983830533819355354776605300741922961444944617201921261596568372987955109512437059722158269658701889121029429223130730267923542697872107964940369129180908203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 95) / 2 * Real.cos (169 / 2 * Real.log 95) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 95) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 95)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 95) / 2 * Real.cos (169 / 2 * Real.log 95) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 95) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 95)) / (2 * (169 / 2)) ≤ (105294569371811606046644769437999040970127854207304090744833599866559633991349735500510796896362763539243802269354656894538997826357511990267874475426631061497476319269236541683249260522748010625629501536106322369018802113728402616401913262432025524431817138478807953267670631086938356044950204250372126407848498090049824159339512923091003810750422684269058025577844831992194760092357359966657522788116530724447802884734270011595832115088756507121810236136283108385435740240626897610548689158529234424136510136487503375659603069370736645840334878267489181288445745491642781498265996013535129422021199569266056193387189924920952352452542548273764022396396672592805583823906119027964372283276993504771902482014041866999049383912636675132211109693908483975043671417376692392037145110591599503184102740798450288916769 / 9807153989675495020216829297332558603295074959548314087867089349820572266867383397210056138692852945896353633434897300546297263518335209283910705348763522990995684649239911080486155009308907064815587391666671044705451480702153891313011558610354634543819735225555767280701335141535900104754660524623080252614890495687435008094358382453916119742389554656962454686372721111961635898540258690838537382153462864670543931325361087483923278374467981471852078586589989555717230940925460845765096945327210913658408416368959762138241985174628158179903019770810227195343193739974342175662326613673812896144049754153323339811691420531071539581873199981581661706144066856475616261650317161980296987167093902826309204101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_96 : (2449489742783 / 250000000000 : ℝ) ≤ Real.sqrt 96 ∧ Real.sqrt 96 ≤ (9797958971133 / 1000000000000 : ℝ) := by
  constructor
  · calc (2449489742783 / 250000000000 : ℝ) = Real.sqrt ((2449489742783 / 250000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 96 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 96 ≤ Real.sqrt ((9797958971133 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (9797958971133 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_96 : (-27134709791 / 100000000000000 : ℝ) ≤ primeTerm 96 ∧ primeTerm 96 ≤ (-13564632653 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_96
  have hl := PsiOmega.Num.log_bound_96
  have hc := PsiOmega.Num.theta_96_cos
  have hs := PsiOmega.Num.theta_96_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_96
  have hqpos : (0 : ℝ) < Real.sqrt 96 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 96)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 96) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 96) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 96) = 2028 / 5 - 169 / 2 * Real.log 96 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (184715947863391697668664099834379244773836715197261188257309738057524311540349992673968312210962480546505943678341430787915931814507931958845380853865983964399836967038926680175254955251893203906605512974847692719875365702276172336940758034018070540324343906096829830436544105673448583108778305059931681197199023126035377566360612102646661372764223587595433429 / 1567702367561140316646767427758125182984969856664122132991104261736176372382168016425927806053515690804624548427984130020405366068652132247931790074109393248650255628136605136642373182920361090105314987784747727177546972245521721730085018525529433825618449110774518633796250530494162138658211512441865173371423236574967980595712555078562378545171137500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 96) / 2 ∧ (2 * (12 / 5) - Real.log 96) / 2 ≤ (1662443544632485350088261807056924301762781249254116286591391789191784124177190398240634675797994361291148037421317262543822350676751532829781683087339369680844615031946302677390597674894438664528534888126723749646544777963022152878279952906749516975454521443482340289701455942816491267872828012060693397586548278867591350503353773375739227157177313436683285539 / 14109321308050262849820906849823126646864728709977099196919938355625587351439512147833350254481641217241620935851857170183648294617869190231386110666984539237852300653229446229781358646283249810947834890062729544597922750209695495570765166729764904430566041996970667704166254774447459247923903611976786560342809129174711825361412995707061406906540237500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-2437166759606364291152476096217848844121979981918891063570362334298536047903264270480818267077321031714064389216721119827481110045695428614858878890028302299872079465007821329051770644235384014636591674927929445472727647601565466628352462536540806943356292499028654363618512168289471777895286186237515551615657426568329998146592958339167720040512614389239712678287921719379268199639571555696464645480907483385837542263835456055370436418484786214400126638697207868415023545720600741851227933716968857231141406379347489004464872702292792848495276387460085795818835595113607685712797842550463066066539545543219777551376580945448025123251379523291161602161987212570164633122481730884678477232124995375625575766580232839752712347524305202084830125474362875436235708256107216319777236570764228399476503121525468237963 / 29448660913284198263307747981399010753746679793112941058151522737989322686201219464089296657999243565952485051757864104304253474627510567083534355868349415985520124813548304044235602538172568977110725016217887083361899813733545827497183661162457897182684445779625883537102423592061434247511952300928278456443859751578717566185122400738986716619640592109941319153667967077733482742346867153580409218957052400936405646699974722150270067705708094277817147082301406403144618507510778348378375174404718232129942808259136671216719440969885070997851104234901660189197601867301749723637052572144319833006424325265942798797874328274833460369087879356269013124610574412301863471226742962824211015244409253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 96) / 2 * Real.cos (169 / 2 * Real.log 96) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 96) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 96)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 96) / 2 * Real.cos (169 / 2 * Real.log 96) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 96) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 96)) / (2 * (169 / 2)) ≤ (-2707420061350847790672486001986881434047454232069918764625349899604191166342224422538357717154645158711552297582498839607740774208828813990404985783602021072380274305418072744245265125399777673890443557952712886564154995416614489625194044932049825864087028013354606650812972422528135480777284474264249899782404694919640476981629894659112183019674024455636116985776715056575693304254206912151042070297197618354982283977571605462326519482943096904827064704001394427924415075216908004024163708077015497776585383573651884827789898873633257015843472344831533867691695415733767139778567141590404756891231820325351300166106559039393552241569830182032068345523610078172132453906070907452962932721744302765501247661626664123224519297725301319884528859653855043470238581892564440076274671295913311046998810508694228687091863049391444896437781 / 32720734348093553625897497757110011948607421992347712286835025264432580762445799404543662953332492851058316724175404560338059416252789518981704839853721573317244583126164782271372891709080632196789694462464318981513222015259495363885759623513842107980760495310695426152336026213401593608346613667698087173826510835087463962427913778598874129577378435677712576837408852308592758602607630170644899132174502667707117385222194135722522297450786771419796830091446007114605131675011975942642639082671909146811047564732374079129688267744316745553167893594335177987997335408113055248485613969049244258896027028073269776442082586972037178187875421506965570138456193791446514968029714403138012239160454726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_97 : (2462214450449 / 250000000000 : ℝ) ≤ Real.sqrt 97 ∧ Real.sqrt 97 ≤ (9848857801797 / 1000000000000 : ℝ) := by
  constructor
  · calc (2462214450449 / 250000000000 : ℝ) = Real.sqrt ((2462214450449 / 250000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 97 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 97 ≤ Real.sqrt ((9848857801797 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (9848857801797 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_97 : (-58234241037 / 4000000000000 : ℝ) ≤ primeTerm 97 ∧ primeTerm 97 ≤ (-1455648436217 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_97
  have hl := PsiOmega.Num.log_bound_97
  have hc := PsiOmega.Num.theta_97_cos
  have hs := PsiOmega.Num.theta_97_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_97
  have hqpos : (0 : ℝ) < Real.sqrt 97 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 97)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 97) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 97) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 97) = 2028 / 5 - 169 / 2 * Real.log 97 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (1269537609900122129128917807027087545123087687539028809236592310626484602456113136029498509812419787846481815729083891021102163153243006318239766197125387059854866083345903166850368984078233868604828510925540377471764968314868005962200927177582394760110843201274905858343001396700945644199580895036400255970769259385978067775396736881499979062023104344685934954536453 / 11270301679431988721371659903896544153614378442840203869034629030564290903108631653662931275603669351588821742248038305812105339773406091901919770954806652299961860775244858113814809427285902337349245450138855141299834303650473652255719813026087054950099090908957328605923371450002769782055786081000777917682043818861929585677471514075424417416812382242337500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 97) / 2 ∧ (2 * (12 / 5) - Real.log 97) / 2 ≤ (11425838589134314309135540262303886131213221644791542508581381524710237288622012338305928659075697134752551284346791703826943100346836128927346172239213977549413239309919762834585082193548635009008249219466730292412830704665032465224988021453365372745574524211224330111191889543051511372727695869623951646591628598508671105788759908148514155135898312583132030687146723 / 101432715114887898492344939135068897382529405985561834821311661275078618127977684882966381480433024164299395680232344752308948057960654827117277938593259870699656746977203723024333284845573121036143209051249696271698508732854262870301478317234783494550891818180615957453310343050024928038502074729007001259138394369757366271097243626678819756751311440181037500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-202291952234451315847158022169846252498330098642132896885909601129767815858660819934243804716185245004361786963824219143898165061621445380501414231552818833671527479864133708172091158528089559784461633253293263192610825877846451268311787671699273820335831341391518815604944185229207266334959779189003911903953657676937361865415553782736493380853657504284415610764367557686606374862608507410068748066538442043605189960823247593962985430470340335526212345593540428583854718334187612644020463764557104840821856891714914061931712098160548865378280265040310878845738736629950073420905965686046989698134213291930075047436506645767035343389385218875567079805182387986370018208686922804785941832813256835418172266089311700616795195517680113568135192954560253841334541085872177978787393947785896934566967877716416132579263 / 1833484188851197540559208558691182990864362925745776576654477992339511965177595121474575468520977471252092247368241498741814927480784595927142111455167067925976587651964095893339889497023438672350446073331258583094268358435705759444041465133441414766607074964638866147866323651118260098257537092621618437565886350860487726636899541517684019307990397649865358285662364611114834638842327366358570069582248335164537391937440164870734033732788641004806285153101492678328539075181669606413478338580127542390569851566170974387423727318585166945886513100899468420135623722869825972444111879381085792528532043105880200964282543435374127561062143306058872562557525135732471544441122478733809379389306441776766220022822607917285797629602939196047373116016387939453125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 97) / 2 * Real.cos (169 / 2 * Real.log 97) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 97) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 97)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 97) / 2 * Real.cos (169 / 2 * Real.log 97) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 97) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 97)) / (2 * (169 / 2)) ≤ (-4494735724975449748721837991288178574829227807558822377595634913207252906867076656909008933053475807782173769960065471418755725133409210810779492931909675715512033273885451113521286399053733728811546092354564907618442525050591047540978843874399084110058428768119877199931371019504632170885577353461273059036886461362699009704931888230136087780629586940946715224011032181812048811406811886131963254307099121050258738492096118968505351946410226358241712208088541385603394737978848372324391742117835988670135254840698232888596366854374862104373079134214381457582579426319733213167297184967604253069615624020362433811222898147939392107056406518174611344806658912255691214446933262743154897880861228323727642922528610345322029859374367708760422875447346838106921508727295122447974124498697919071702931434217136793798009 / 40744093085582167567982412415359622019208065016572812814543955385322488115057669366101677078243943805602049941516477749818109499572991020603158032337045953910590836710313242074219766600520859385565468296250190735428185743015683543200921447409809217035712776991974803285918303358183557739056379836035965279241918908010838369708878700392978206844231058885896850792496991358107436418718385919079334879605518559211942043054225886016311860728636466773473003402255392851745312781814880142521740857336167608679330034803799430831638384857448154353033624464432631558569416063773910498758041764024128722856267624575115576984056520786091723579158740134641612501278336349610478765358277305195763986429032039483693778284946842606351058435620871023274958133697509765625000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_98 : (9899494936611 / 1000000000000 : ℝ) ≤ Real.sqrt 98 ∧ Real.sqrt 98 ≤ (2474873734153 / 250000000000 : ℝ) := by
  constructor
  · calc (9899494936611 / 1000000000000 : ℝ) = Real.sqrt ((9899494936611 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 98 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 98 ≤ Real.sqrt ((2474873734153 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2474873734153 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_98 : (-861038502619 / 100000000000000 : ℝ) ≤ primeTerm 98 ∧ primeTerm 98 ≤ (-430410160193 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_98
  have hl := PsiOmega.Num.log_bound_98
  have hc := PsiOmega.Num.theta_98_cos
  have hs := PsiOmega.Num.theta_98_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_98
  have hqpos : (0 : ℝ) < Real.sqrt 98 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 98)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 98) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 98) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 98) = 2028 / 5 - 169 / 2 * Real.log 98 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (1211740684338460262279028402568642848662447201962778563992142622052218366626018986078277955603920945033527152518401384082301172248899001803892186083972204186388528211485442112125219292416065881594255664383571686123328619777087422731943698967484552567963356310488996370547965756556999380785166446597810886324149951355334842621793361561176035265103755248932572454536453 / 11270301679431988721371659903896544153614378442840203869034629030564290903108631653662931275603669351588821742248038305812105339773406091901919770954806652299961860775244858113814809427285902337349245450138855141299834303650473652255719813026087054950099090908957328605923371450002769782055786081000777917682043818861929585677471514075424417416812382242337500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 98) / 2 ∧ (2 * (12 / 5) - Real.log 98) / 2 ≤ (10905666259439120440575708784957240838797214428791769445691989185139852602812870472317660799592254385568574577091974643077912916261470803143781351608478925238577069085959076066086002357316574484035628970047809526075332136709443962780352005313876612565333790323789862415627508003970738211079874758825895816221933830620948057423517106170192963271744045929947630687146723 / 101432715114887898492344939135068897382529405985561834821311661275078618127977684882966381480433024164299395680232344752308948057960654827117277938593259870699656746977203723024333284845573121036143209051249696271698508732854262870301478317234783494550891818180615957453310343050024928038502074729007001259138394369757366271097243626678819756751311440181037500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-6103818880579179940383277073124598982074431443463701487293655566043427044720228791723663511266285929863191079989719782833248568181502674867638372181783405534646515093187404171755678155582149522299489142935234923551231425702578737697602993465009806962713090827676325664546057308362860388816564201942651698470381327802884369349939453151030951413203650105208052282662758547456528710000606561264188154742050609769683736464459970167586892122496837923025398314536042656478065443606709139861166488550150570353253903358961426763308959384811645514777579307560100611465347930705393960709549193579450736843319744523242579955063455642014975505709144654095245683233815329319991344114921321881894087157494092031196098908754248470227843998921386679152733437023978412797043473292017810427310758982867059255215104513631284544071965381759795712043253646920404001 / 100796859249266959963359159183640672119217990885798231127728896883839262963692312046879346339602889330950609587478263118414339343546643301473922143287417945065983908183849241959714938905210348073047364300407979378037517881970713030284815805645505950138225406148406867911774211344694284165604715498454708376782076444141775929790356449994842477947536760169049249795103765795404452790729821939659123944706572565531326429957626701781129502675046604747872941412112179484217897873450959593255440867917604736977294992387567551212013344355136832298019526346736192617821334710882173655793378684247810558467664281956066923974415208430481502710965101096808656727248442581362256494402965039259734706881633530282739809735212475061416625976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 98) / 2 * Real.cos (169 / 2 * Real.log 98) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 98) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 98)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 98) / 2 * Real.cos (169 / 2 * Real.log 98) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 98) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 98)) / (2 * (169 / 2)) ≤ (-42376890363704838675152184827988141499489846457134724478103459899724285191587711499791048927318265520650572027057944055676202820524569406345146831171222976717772678474907375085611273365452894353894294608685934693020270641122860662023217209780202038925291703303506580901963799138445554181872541482356374322619031421942949974983708215984376753458965994837246936074614917831963207143318720760610699880173090936823075785581905623233815452989419321080150557759119439274337292322969956289753270916876178379487314467866577946749117191846922379038737064441639208474629240804282919742469875012170024457664201899788722755904094603625775436255293298786223932805057036382022986498015349136982156754838552158734561254732918342093480480898135767206385076261829146034508689201709801831460151725162427087538966595742355094493360771984401164425157326745851131775651395239 / 699978189231020555301105272108615778605680492262487716164784006137772659470085500325551016247242287020490344357487938322321800996851689593568903772829291285180443806832286402498020409063960750507273363197277634569704985291463284932533443094760457987071009764919492138276209801004821417816699413183713252616542197528762332845766364236075294985746783056729508679132665040245864255491179319025410582949351198371745322430261296540146732657465601421860228759806334579751513179676742774953162783804983366229008993002691441327861203780244005779847357821852334670957092602158903983720787351973943128878247668624694909194266772280767232657715035424283393449494780851259460114544465034994859268797789121738074582012050086632370948791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_99 : (4974937185533 / 500000000000 : ℝ) ≤ Real.sqrt 99 ∧ Real.sqrt 99 ≤ (9949874371067 / 1000000000000 : ℝ) := by
  constructor
  · calc (4974937185533 / 500000000000 : ℝ) = Real.sqrt ((4974937185533 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 99 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 99 ≤ Real.sqrt ((9949874371067 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (9949874371067 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_99 : (-461 / 100000000000000 : ℝ) ≤ primeTerm 99 ∧ primeTerm 99 ≤ (27 / 10000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_99
  have hl := PsiOmega.Num.log_bound_99
  have hc := PsiOmega.Num.theta_99_cos
  have hs := PsiOmega.Num.theta_99_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_99
  have hqpos : (0 : ℝ) < Real.sqrt 99 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 99)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 99) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 99) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 99) = 2028 / 5 - 169 / 2 * Real.log 99 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (8826816616108072609139395207487711970064951904593174546841995780470333093916337148643071950013202207199636679358002636380366265182427716212355274922489524446366627098326440185224263509588401604470137357084136028825339711069229302216574202172159009180587108763403519692385186310973323872324155568857262057465061859727206527513486160573294561259729948240451867275394225281969 / 86165660161783981906679411594433233465351221358672537974812888855292404434772348511859925875355852361564684849996111366221613237859425053062456065024062999714516311400816106612190670995517101010606812734864449348204938089603132698167269354074694265565003936959887818275854184152822026016945191397459160470842520397543887182239727421981369804459227133261246579387500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 99) / 2 ∧ (2 * (12 / 5) - Real.log 99) / 2 ≤ (79441350315128123811570049542502294735286531109066018974126609066048612529723848663036688012693080642757219706766037641265236904839295445239910918212792659346095803829905574239174446204564361900736234917815031780625368959114439678899421312749564988137273285660120020221361988877299007268502802138992739859956479923188599299224437288229406143974769695544448895719483003062679 / 775490941456055837160114704349899101188160992228052841773315999697631639912951136606739332878202671254082163649965002295994519140734825477562104585216566997430646802607344959509716038959653909095461314613780044133844442806428194283505424186672248390085035432638990364482687657375398234152506722577132444237582683577894984640157546797832328240133044199351219214487500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (9001608952946037188081985348877715452254944370298099724720932992462411705830733110024416687324401733491256253703210440734574150846838524406071259525543918055866650265821207060427666457008055724731027376831441971927768131358033460826920671731161953142515718594621790674026145394911205180725080514526143754667830259894876087044688370801071504747587343903778220076453373063160880071637385783026355582837239283750648880495221149011209939422324817857226529305074474411167043732362615236694969866766224771297366802771137910231155657577489511321502869598491806420837777333713210460625638176779716732181880869996500366173803963744670362283490313143725253531075152158475824979623254916097020765431188910303045476795133012058977397687422833610190691392638009441384643659564574155106772694950555291572159299525365402307093795182144089247522829683287813690365107796673450900885703 / 368234414453229302876987850339007508483085681719055973330941508042370397454910276259909720737501823112620536814306414554847172133812078531375374584621578611225753462115116839812536055261793274823741147417338511153467276636590505459249272771287925212703170168947230465860113804352089669998539572228892445730049562087153049324134753977394202059643192333802911993870342911872457296317510222515681665744947559082243583660826728466526180119877242410030041226817870720405219424437970528950373709514691558659738101487990899549177940242202204165714034132760170986168294568554495927026093478443400141665120089970797620225421638053970550667024931947396318250501366212476686768300688038920413344628757968844461185127261716641133325319970026612281799316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 99) / 2 * Real.cos (169 / 2 * Real.log 99) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 99) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 99)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 99) / 2 * Real.cos (169 / 2 * Real.log 99) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 99) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 99)) / (2 * (169 / 2)) ≤ (1297008161584154615734953231868792633500144439570385073282452743713172219521698834597078085133735353268647730854893420668602286445482282717130431025106685163727730662884348881424661156320355404413438153527129707423771375711813996414168385597896587689029064736530380166551101201513498247924722415959355012956101837547336156319101704613098471692744933725980364954967623611406506071863427871144446222886764391682364680855060158041424334139169079053749527065624636912369572630737032172146446657615841988626790847545671019506900062441736485058505768083269114394728754310999091336072013372881309666615090978528818017694380458841265419943977421114553958086962082524787023991201364323489351284500915896854200826511159471729715041447735080812682926801632697637381162261419368728596903500149682372027573205128432463198867850500871235574660325207682531712703 / 53025755681265019614286250448817081221564338167544060159655577158101337233507079781426999786200262528217357301260123695897992787268939308518053940185507320016508498544576824933005191957698231574618725228096745606099287835669032786131895279065461230629256504328401187083856387826700912479789698400960512185127136940550039102675404572744765096588619696067619327117329379309633850669721472042258159867272448507843076047159048899179769937262322907044325936661773383738351597119067756168853814170115584447002286614270689535081623394877117399862820915117464622008234417871847413491757460895849620399777292955794857312460715879771759296051590200425069828072196734596642894635299077604539521626541147513602410658325687196323198846075683832168579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_100 : (10 : ℝ) ≤ Real.sqrt 100 ∧ Real.sqrt 100 ≤ (10000000000001 / 1000000000000 : ℝ) := by
  constructor
  · calc (10 : ℝ) = Real.sqrt ((10 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 100 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 100 ≤ Real.sqrt ((10000000000001 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (10000000000001 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_100 : (0 : ℝ) ≤ primeTerm 100 ∧ primeTerm 100 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_100
  have hl := PsiOmega.Num.log_bound_100
  have hc := PsiOmega.Num.theta_100_cos
  have hs := PsiOmega.Num.theta_100_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_100
  have hqpos : (0 : ℝ) < Real.sqrt 100 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 100)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 100) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 100) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 100) = 2028 / 5 - 169 / 2 * Real.log 100 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (66148327165955232324228302655319879275193370336211963548262924805511560215829468211776311942044410035611011757851019787833994855432339117179798851702158044842745631885301264878141727786672854878128092296488161858471632941017302882268946051157781361614264662684377773981660797746012821663334865726909997423779724487751537446685742422671635634278264881662978467954843339206609619431 / 679037015305294686029795864331678945213813369687933444091772477100128467096262534910214819993403454764694293864194505236534679060661747213738938203572565851487217529108960008951923189656601070707087037831560044669014486903988357938044284704451681554517304460602154980816878207780545105407112258381625262547361095402363959784471213681938960899651580887151446532274553112500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 100) / 2 ∧ (2 * (12 / 5) - Real.log 100) / 2 ≤ (595334950582466624822011698409398903782751542264687363456804169936601153403723149772269240615053748568341910407163915425459407069707693444450100651109459276595933057987162368253799800154389464825187676816639713514272083599436662487875907892808439163371053534520108634149111326702178075444404444477392832445899251346270740530472375539260145854054504026917981007305404384452745064721 / 6111333137747652174268162778985110506924320327191400996825952293901156203866362814191933379940631092882248644777750547128812111545955724923650443832153092663384957761980640080567308706909409636363783340484040402021130382135895221442398562340065133990655740145419394827351903870024905948664010325434627362926249858621275638060240923137450648096864227984363018790470978012500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (127185599716232710118646928034906407501277927959162005429774839512138119847982935113910228640986318768024699390417010683161507207651802551700587728355561147438593079535100130472611252711423283787803518053857557120854498087525215250346502545135167034067566205077028983866339040340579207784365073927219955142782529065276769798967076766681867055656923815124262457389222944793055951414370216535446334973802654834682540572493490887348354173826230147432375521501239822249671706446061274994300823490118842683834875613441298997094471624273657790056827473298430919923450088933318785070195509909063883455359980074991724550013212364468731588143836078432940354253978561669257356635332986761792922829451944154166637680943563141030985691791789777915995349802420024629199082460226581007274621345819435660932769137497201667734757727108754164741779030757230186949801826392727531607151287501210564319 / 1498727801041464571867440934514908845603568416912268749559660173810938042224187236522325445563953703133597989646505433198191925297660915618858774023996090303445224054537301306180727469951940695133174050216596402153905521340049890595790822821615742881737248142586201350515754288727686295786471313386181375889290467182511840171622792415980287299248249982427191749831705348382156017465723817145121532344428209594338226123907894614117127189979480996992300345727350801727375772847545268799443271805803550438969148291401885690669142722385459945521801997137069344591781930397755131670095515447733284984219230374959190734532452735018646352195050513182598119494748193392344969112159217532759014262156523791076742226643740511156610057282759717569351196289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 100) / 2 * Real.cos (169 / 2 * Real.log 100) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 100) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 100)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 100) / 2 * Real.cos (169 / 2 * Real.log 100) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 100) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 100)) / (2 * (169 / 2)) ≤ (4579442218537545927753245978352503951278991970963228351628993389803365350573627275148764272159969554981515832955499527463783939209696893623516413812235472897146111860555837304590160521664944441786422399475982530997586882998525289757688592401785203267013893888728203697550618373629014219796579663381173093869864979646641854099566762434654910435073215241939264851944986548127897853517465069360034417674929702285850559776025959906541997127981218087788278134850842263677461773063373914375800854743535675442682285788663725999373663595891676179112816433315761441034012085686062934741702549618609166197034993512469622221436872008665434677743159449445000805549066130379307695290917316704161718227560133181272984809584670353967883521076278008168858119720153499611394338745720029714318209570724760625541121631595568609329134700055119216698863865297315463756429262524657 / 53954200837492724587227873642536718441728463008841674984147766257193769520070740514803716040302333312809527627274195595134909310715792962278915864863859250924028065963342847022506188918269865024794265807797470477540598768241796061448469621578166743742540933133103248618567154394196706648312967281902529532014456818570426246178420526975290342772936999367378902993941392541757616628766057417224375164399415545396176140460684206108216578839261315891722812446184628862185527822511629676779957785008927815802889338490467884864089138005876558038784871896934496405304149494319184740123438556118398259431892293498530866443168298460671268679021818474573532301810934962124418888037731831179324513437634856478762720159174658401637962062179349832496643066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_101 : (7851465329 / 781250000 : ℝ) ≤ Real.sqrt 101 ∧ Real.sqrt 101 ≤ (10049875621121 / 1000000000000 : ℝ) := by
  constructor
  · calc (7851465329 / 781250000 : ℝ) = Real.sqrt ((7851465329 / 781250000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 101 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 101 ≤ Real.sqrt ((10049875621121 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (10049875621121 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_101 : (3898656649819 / 100000000000000 : ℝ) ≤ primeTerm 101 ∧ primeTerm 101 ≤ (3899275959251 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_101
  have hl := PsiOmega.Num.log_bound_101
  have hc := PsiOmega.Num.theta_101_cos
  have hs := PsiOmega.Num.theta_101_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_101
  have hqpos : (0 : ℝ) < Real.sqrt 101 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 101)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 101) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 101) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 101) = 2028 / 5 - 169 / 2 * Real.log 101 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (62770005682381685741241503295841653234477337650333194387617060761360662537989391302663981100080703611111830311704350816950287663447856671486140040543969636089219997969593181280377296932171670910378418093506182015960038757595431092307663948946792835396839939343642902485619593084697689254529172820948420679988880586866997908663802854309284057756771561805787813278647315800359619431 / 679037015305294686029795864331678945213813369687933444091772477100128467096262534910214819993403454764694293864194505236534679060661747213738938203572565851487217529108960008951923189656601070707087037831560044669014486903988357938044284704451681554517304460602154980816878207780545105407112258381625262547361095402363959784471213681938960899651580887151446532274553112500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 101) / 2 ∧ (2 * (12 / 5) - Real.log 101) / 2 ≤ (564930057248932713800319321968126829877496856437989455817566929497952349925038971982500597736596671685251604458066368034808536804981555658849990166912855131854556140171058958324531425210537891706160485110014894616977450405153010969156030084508895221561679313384447520287614287395912496472196488133440023415462826428774564552222594895029849420250637708459665942140472034452745064721 / 6111333137747652174268162778985110506924320327191400996825952293901156203866362814191933379940631092882248644777750547128812111545955724923650443832153092663384957761980640080567308706909409636363783340484040402021130382135895221442398562340065133990655740145419394827351903870024905948664010325434627362926249858621275638060240923137450648096864227984363018790470978012500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (3882982721479480929112848794511986858942530255235730147450925401536864212346246189262375850746665578092637831115778406505286187694313484745960404887267675129631541492456213042938936124364275215299925441223814665558651089554676936965813535060150283310732993919368863367299281346190468115564876354261053251783336066334646382160586035344604151914497339420264970050822324962003064040975556181020686473153726858790694345279707057715161937339153447257217974577658646841676023822386749679702027047864374128411906497208307907973405604083423074223686338173339177688904622630677412126197018367826579451828232408049312122694706120592386800501524932234195355543037092550546792129790715458652175370108009022155192775814573628561699695498259969855431754113484958705742987647522630308421166599247318883599972281929110739223775208051595334902045621859380512788990618285785178728472392054254167 / 45737542756392351436384305862881739672960461941902732835682988702726380683111182755197920091673391819262633961380170690862790689015530872157555359619021310529944581742471353338034895933591940159093446356707653874325730021363827227654749231616691372123329105913885539261345040549550973382155496624334148434121413183060053716175011975585335916114753722608251701349844523571232788618949091099399460825940802294749091373410275104190586156920760528472665415824198938040996575099107216455061135003839219678923619027447567312337315146557173460251519836338411540057122251293876804555361801618888344878668799755095190146927870261688801463384858719274371280502159063519053496371831030808494842964543350945772605658772086807591449281533287344896525610238313674926757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 101) / 2 * Real.cos (169 / 2 * Real.log 101) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 101) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 101)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 101) / 2 * Real.cos (169 / 2 * Real.log 101) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 101) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 101)) / (2 * (169 / 2)) ≤ (139809583418157594518564882674614304949808242248499976594042884566498863347329401030140639561981061284323525009531809552260100644742681576923715862954287709717700998062402558713637442132272546520893201351702271685468142925085749965966467246007464051436486483248464002426953749875606551760956757865855524172044868148107484936253548567516896893783456692017891026487931171863146613101421683707888433206723208409563324127114330985910520549311620599615773544376222655638683841883322500073529584102874788285224871682592454789224637535904359920905322526735446626830654010828756892698570691283797810478849890343815915735992252963977887922487374324309220466871699644103858687251610232640658267219006016770217243826562272092537063764848659278436022409469944734570668304405403771270073462574313817233347898664105561701859674336431849819390904349555757684108956203249181865804526562852068999 / 1646551539230124651709835011063742628226576629908498382084587593298149704592002579187125123300242105493454822609686144871060464804559111397671992946284767179078004942728968720169256253609309845727364068841475539475726280769097780195570972338200889396439847812899879413408421459783835041757597878476029343628370874590161933782300431121072092980131134013897061248594402848564380390282167279578380589733868882610967289442769903750861101649147379025015954969671161769475876703567859792382200860138211908441250284988112423244143345276058244569054714108182815442056401046579564963993024858279980415632076791183426845289403329420796852681854913893877366098077726286685925869385917109105814346723560634047813803715795125073292174135198344416274921968579292297363281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_102 : (5049752469181 / 500000000000 : ℝ) ≤ Real.sqrt 102 ∧ Real.sqrt 102 ≤ (10099504938363 / 1000000000000 : ℝ) := by
  constructor
  · calc (5049752469181 / 500000000000 : ℝ) = Real.sqrt ((5049752469181 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 102 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 102 ≤ Real.sqrt ((10099504938363 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (10099504938363 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_102 : (-18037931569 / 2000000000000 : ℝ) ≤ primeTerm 102 ∧ primeTerm 102 ≤ (-901533525347 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_102
  have hl := PsiOmega.Num.log_bound_102
  have hc := PsiOmega.Num.theta_102_cos
  have hs := PsiOmega.Num.theta_102_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_102
  have hqpos : (0 : ℝ) < Real.sqrt 102 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 102)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 102) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 102) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 102) = 2028 / 5 - 169 / 2 * Real.log 102 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (59424968695523042609706626465724612345877380047974463072746069925954362635737008653422615209358361723711827617927988181221136073026386189430783467213049583769452243131112519491824941935279922498205573058739699256568865740785705080640709042392389969310363154366192364874100782670519897818155025550570829314285898431533333473935376874895298189931987066450165234524159920487859619431 / 679037015305294686029795864331678945213813369687933444091772477100128467096262534910214819993403454764694293864194505236534679060661747213738938203572565851487217529108960008951923189656601070707087037831560044669014486903988357938044284704451681554517304460602154980816878207780545105407112258381625262547361095402363959784471213681938960899651580887151446532274553112500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 102) / 2 ∧ (2 * (12 / 5) - Real.log 102) / 2 ≤ (534824724384933193592507478131967550271485118148558502982937813327695404715842808535298187949453296108972129604537921144990846935864955698845515517060097165851985657389241900574804474001400709407142482928043751290160687918205384966861871461365586761435783056377367110894849631483610627019051846163865642588923371538162243763253445846784942187863530998216390004680720684452745064721 / 6111333137747652174268162778985110506924320327191400996825952293901156203866362814191933379940631092882248644777750547128812111545955724923650443832153092663384957761980640080567308706909409636363783340484040402021130382135895221442398562340065133990655740145419394827351903870024905948664010325434627362926249858621275638060240923137450648096864227984363018790470978012500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (6006629602603151413479247917971854264302203465300466952515359817931318273892752395116856494431303470796353657404276637986636910242254600146286145963586261623088735884039648789799366221074348053580680865028365341632766534487787864916630323641850899818045769451981807322456722400454160083449189107738778072576925240511080082792982633995234091004612407342063062819168443650049956849695095437657789335921235924484512084405879575485148302306664793758412469100533904083732226970845610604087196824512567920109074739723956794493209274576320661877869822306788082405646411920503916725500517666023725839498721071816752535157328882292027485625264129919357508253120808559619017207418237433917114702410030182636004494913688483272612571709251823547249053537460101911439608388279686517976899021432494410795235612057056409894046495255108191490198990840704072047418759455144805432417017497385485383448077 / 187340975130183071483430116814363605700446052114033593694957521726367255278023404565290680695494212891699748705813179149773990662207614452357346752999511287930653006817162663272590933743992586891646756277074550269238190167506236324473852852701967860217156017823275168814469286090960786973308914173272671986161308397813980021452849051997535912406031247803398968728963168547769502183215477143140191543053526199292278265488486826764640898747435124624037543215918850215921971605943158599930408975725443804871143536425235711333642840298182493190225249642133668073972741299719391458761939430966660623027403796869898841816556591877330794024381314147824764936843524174043121139019902191594876782769565473884592778330467563894576257160344964696168899536132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 102) / 2 * Real.cos (169 / 2 * Real.log 102) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 102) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 102)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 102) / 2 * Real.cos (169 / 2 * Real.log 102) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 102) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 102)) / (2 * (169 / 2)) ≤ (432651492460128578439520740924991406349835882492586679675301098024579389632648494011583674457401034547211541858493054597087140054912576951560379213446243869359428546585123850408991563329239004243978286890639714279018068908164336636351891790751781190783168934813870794398092142621216765127267034517955714472935122170639142606678151152159567835766599278928361318907165917478206924176368820252130384633918515336376434722415342929414056110042846499359911380752053638254363673520568490172624266343611975209308758706487092755666277181186737132785789757873103780485894985584501287990676473713323904551945295832779197121840572742066496295445825461081085329554654317792296436321001079463044962768060335567878669715304740089712921204118182115139256866747374914098493286297549242860395971728865042588681206634559442750033331165282212414221365289004163717216864163596595879424845503859921 / 13488550209373181146806968410634179610432115752210418746036941564298442380017685128700929010075583328202381906818548898783727327678948240569728966215964812731007016490835711755626547229567466256198566451949367619385149692060449015362117405394541685935635233283275812154641788598549176662078241820475632383003614204642606561544605131743822585693234249841844725748485348135439404157191514354306093791099853886349044035115171051527054144709815328972930703111546157215546381955627907419194989446252231953950722334622616971216022284501469139509696217974233624101326037373579796185030859639029599564857973073374632716610792074615167817169755454618643383075452733740531104722009432957794831128359408714119690680039793664600409490515544837458124160766601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_103 : (2537222891273 / 250000000000 : ℝ) ≤ Real.sqrt 103 ∧ Real.sqrt 103 ≤ (10148891565093 / 1000000000000 : ℝ) := by
  constructor
  · calc (2537222891273 / 250000000000 : ℝ) = Real.sqrt ((2537222891273 / 250000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 103 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 103 ≤ Real.sqrt ((10148891565093 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (10148891565093 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_103 : (222098655243 / 50000000000000 : ℝ) ≤ primeTerm 103 ∧ primeTerm 103 ≤ (111089357371 / 25000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_103
  have hl := PsiOmega.Num.log_bound_103
  have hc := PsiOmega.Num.theta_103_cos
  have hs := PsiOmega.Num.theta_103_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_103
  have hqpos : (0 : ℝ) < Real.sqrt 103 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 103)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 103) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 103) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 103) = 2028 / 5 - 169 / 2 * Real.log 103 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (56112566736174212236060246828956715256198654168600208976369934004771600246997702231607319789773410398888934390196015865769031450108933343514068250965278984576147192118195975885361273468370709762677393682239367648290124465680367922410767010097011655972392758028839700894758669556011744330044465428047372222892121445152609689748119706947062202041828432710754196183208803525359619431 / 679037015305294686029795864331678945213813369687933444091772477100128467096262534910214819993403454764694293864194505236534679060661747213738938203572565851487217529108960008951923189656601070707087037831560044669014486903988357938044284704451681554517304460602154980816878207780545105407112258381625262547361095402363959784471213681938960899651580887151446532274553112500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 103) / 2 ∧ (2 * (12 / 5) - Real.log 103) / 2 ≤ (505013106767673896889595143119481688012918910091179452685705571141003117621588785981473289188673272384564092184341863708029219728859140771591639210116106865435415112957231485605100841822246383756452549102944836001633590359815726239195051338013302190869253722035191939427876579929231553688378030605395468354334402441156069647223675157619966717031312297293824479629239751252745064721 / 6111333137747652174268162778985110506924320327191400996825952293901156203866362814191933379940631092882248644777750547128812111545955724923650443832153092663384957761980640080567308706909409636363783340484040402021130382135895221442398562340065133990655740145419394827351903870024905948664010325434627362926249858621275638060240923137450648096864227984363018790470978012500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-25667305752732741341777816804463838569565795248267880743581993945680855133638197243326239104925490708570286063504685982353519255812862371557196041627245065719721150271469223464980594535326355986407117035443006786394862723895264392864771016467654732726413052279450541118694848250590309354520826761521945794685939684543920585576611291567933936728496320920251586329307473072844314481186561099616362164892460163561841992594189517225193713170918996421598658298939335956379573822404038682551683868492581894885164097469453634835941585183873115469643569524813474497697068993474411531872375019898701629213608868069447776185396460230100274190739967652066842093717641352216038571752593652438785517600416590217815960490945478565561729447982700104918500139790309410563994350633261511127590163743048920143921047227161004688013688388716164900116368958183701790556898532280481543 / 749363900520732285933720467257454422801784208456134374779830086905469021112093618261162722781976851566798994823252716599095962648830457809429387011998045151722612027268650653090363734975970347566587025108298201076952760670024945297895411410807871440868624071293100675257877144363843147893235656693090687944645233591255920085811396207990143649624124991213595874915852674191078008732861908572560766172214104797169113061953947307058563594989740498496150172863675400863687886423772634399721635902901775219484574145700942845334571361192729972760900998568534672295890965198877565835047757723866642492109615187479595367266226367509323176097525256591299059747374096696172484556079608766379507131078261895538371113321870255578305028641379858784675598144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 103) / 2 * Real.cos (169 / 2 * Real.log 103) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 103) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 103)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 103) / 2 * Real.cos (169 / 2 * Real.log 103) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 103) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 103)) / (2 * (169 / 2)) ≤ (-712723801409843759669560980633770754095313975421742516754641923207662911106731161366250592302515008822807554767459291502463847143869261046602725068858084768159761212255775056987720684459929808275734213265730864906928655395787536429215416290174592296285879509851277597361115242325975988834920613837581426406086192300952100893094374996043965060098149939589132477960905838959800075673522632967266661744897681792822804565399039739272080831569891425989962383931430330207173323238603666584302912717665843259686193820393349657140907385033506061583969309450403909634958001595508139864319392778040355856297974050182450276349432153609973736603503816954715225158117538754808898834726681520288964344012762480858049448604517272323709093569025795867077053026300409221546422824479064289255209709430978889907735394565214384021659989848615630113330184126248599739204923080439604249882614924054130895663 / 20815663903353674609270012979373733966716228012670399299439724636263028364224822729476742299499356987966638745090353238863776740245290494706371861444390143103405889646351407030287881527110287432405195141897172252137576685278470702719316983633551984468572890869252796534941031787884531885923212685919185776240145377534886669050316561333059545822892360867044329858773685394196611353690608571460021282561502911032475362832054091862737877638603902736004171468435427801769107956215906511103378775080604867207904837380581745703738093366464721465580583293570407563774749033302154606529104381218517847003044866318877649090728510208592310447153479349758307215204836019338124571002211354621652975863285052653843642036718618210508473017816107188463211059570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_104 : (2039607805437 / 200000000000 : ℝ) ≤ Real.sqrt 104 ∧ Real.sqrt 104 ≤ (5099019513593 / 500000000000 : ℝ) := by
  constructor
  · calc (2039607805437 / 200000000000 : ℝ) = Real.sqrt ((2039607805437 / 200000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 104 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 104 ≤ Real.sqrt ((5099019513593 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (5099019513593 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_104 : (-286665604503 / 100000000000000 : ℝ) ≤ primeTerm 104 ∧ primeTerm 104 ≤ (-286619139541 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_104
  have hl := PsiOmega.Num.log_bound_104
  have hc := PsiOmega.Num.theta_104_cos
  have hs := PsiOmega.Num.theta_104_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_104
  have hqpos : (0 : ℝ) < Real.sqrt 104 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 104)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 104) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 104) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 104) = 2028 / 5 - 169 / 2 * Real.log 104 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (52832169160919109774393782147363415287950317463116882626510741586151816023457418589693811618005228327158869818105650853379402009578154891753942592926158586165682834561569102489048618917560760324607630893379495023305964993016875805816101947958094037037894307317888615668214250416519533148001842473093668537005137773666274456280960495650801605696147933642536346383967532822234619431 / 679037015305294686029795864331678945213813369687933444091772477100128467096262534910214819993403454764694293864194505236534679060661747213738938203572565851487217529108960008951923189656601070707087037831560044669014486903988357938044284704451681554517304460602154980816878207780545105407112258381625262547361095402363959784471213681938960899651580887151446532274553112500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 104) / 2 ∧ (2 * (12 / 5) - Real.log 104) / 2 ≤ (475489528606458282874704903762566161244213678931727210933793762066174011235431817395921838144202639818403407904880392752507940276718324646198249673961729158524297562336464257773104416835419791000409462666560586551977898781423693199606514203333800847773938405525518834421097445566339580760907595467497618016414293338181017618419388863286786078405679710234128111144551101252745064721 / 6111333137747652174268162778985110506924320327191400996825952293901156203866362814191933379940631092882248644777750547128812111545955724923650443832153092663384957761980640080567308706909409636363783340484040402021130382135895221442398562340065133990655740145419394827351903870024905948664010325434627362926249858621275638060240923137450648096864227984363018790470978012500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-3894079781122468081566172811550450376238835301299333856562955532026413364370676730190136861046106160132548584372528276738930942538328279976436443024986553865209126718631903068907573626195029493906802851574329345223684918915317777176916362908734092220219003691640985028247094287951820194638882353277959065593050451870550268087164394944125289424963532829130733271407345971303329465260905104144580934542283543567848491171912452947147310436237044476185345622324566082223718171157879546115367331124588481586731593841884585926576175287090598632460503203649586798928961777776905348699772820713654952294178859442733180684180696864342308211697287458416570013740740431420201466315672594799147119939689045463654479767298835934204326295774694903100686286309469349049517484226067628014554820551103831787047039964966157605110797310415751958491479437509083951711776377876899 / 53954200837492724587227873642536718441728463008841674984147766257193769520070740514803716040302333312809527627274195595134909310715792962278915864863859250924028065963342847022506188918269865024794265807797470477540598768241796061448469621578166743742540933133103248618567154394196706648312967281902529532014456818570426246178420526975290342772936999367378902993941392541757616628766057417224375164399415545396176140460684206108216578839261315891722812446184628862185527822511629676779957785008927815802889338490467884864089138005876558038784871896934496405304149494319184740123438556118398259431892293498530866443168298460671268679021818474573532301810934962124418888037731831179324513437634856478762720159174658401637962062179349832496643066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 104) / 2 * Real.cos (169 / 2 * Real.log 104) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 104) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 104)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 104) / 2 * Real.cos (169 / 2 * Real.log 104) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 104) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 104)) / (2 * (169 / 2)) ≤ (-108151350832548873067205698238716641483419385878160787968850745038201170778357046878435007116651991847733228082976366673027217499101416226978960562164782987544168412023545134302110172617037558732475439934849221573978276357750886908329398858589041769615141321534923083016007804604008485693528767299003902088506933316437534084365589452090416482168423960070607793179467398406908597873472432322576428826925180781185651188878508850017569303453400958160365182794964594456106721583749736414181214420808329562749990066375735353712668081755242356731049561763687367759157860750393449269044755193590416091314849495877048476522824810136533574490993893155385885923941379818909252431766293760547864936684816199315212706821333337098636315314191283258167828828677622254532423310253627122263117777116627936013809198661905501115278075630606857678359604783012291683974396393170392777179986379375765253 / 1498727801041464571867440934514908845603568416912268749559660173810938042224187236522325445563953703133597989646505433198191925297660915618858774023996090303445224054537301306180727469951940695133174050216596402153905521340049890595790822821615742881737248142586201350515754288727686295786471313386181375889290467182511840171622792415980287299248249982427191749831705348382156017465723817145121532344428209594338226123907894614117127189979480996992300345727350801727375772847545268799443271805803550438969148291401885690669142722385459945521801997137069344591781930397755131670095515447733284984219230374959190734532452735018646352195050513182598119494748193392344969112159217532759014262156523791076742226643740511156610057282759717569351196289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_105 : (10246950765959 / 1000000000000 : ℝ) ≤ Real.sqrt 105 ∧ Real.sqrt 105 ≤ (256173769149 / 25000000000 : ℝ) := by
  constructor
  · calc (10246950765959 / 1000000000000 : ℝ) = Real.sqrt ((10246950765959 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 105 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 105 ≤ Real.sqrt ((256173769149 / 25000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (256173769149 / 25000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_105 : (0 : ℝ) ≤ primeTerm 105 ∧ primeTerm 105 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_105
  have hl := PsiOmega.Num.log_bound_105
  have hc := PsiOmega.Num.theta_105_cos
  have hs := PsiOmega.Num.theta_105_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_105
  have hqpos : (0 : ℝ) < Real.sqrt 105 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 105)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 105) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 105) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 105) = 2028 / 5 - 169 / 2 * Real.log 105 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (49583163431498243812952987521063216510913670334944132203432415117776827683282846081109250693751471492595924390272704285479005077162490226700000475044761311216297254336961638319229787217796867920207866959174921186775217056789026805989473826838405305011620640275380304207127930832215591366186846049864623379976427875851723529684336292903246418955948439854277399031476815869109619431 / 679037015305294686029795864331678945213813369687933444091772477100128467096262534910214819993403454764694293864194505236534679060661747213738938203572565851487217529108960008951923189656601070707087037831560044669014486903988357938044284704451681554517304460602154980816878207780545105407112258381625262547361095402363959784471213681938960899651580887151446532274553112500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 105) / 2 ∧ (2 * (12 / 5) - Real.log 105) / 2 ≤ (446248477056995982796762077106144686337372565236278547538851297240190885364243706761030426890029777061616595080474731149924732743231901492247765881138960918018683973248628375613606444158996486272403873060052061831177607405623921810833119605063709094821394254996444201234090934618910557403450672142455317238803018494463352471507853834019243241861852086393687868698894951252745064721 / 6111333137747652174268162778985110506924320327191400996825952293901156203866362814191933379940631092882248644777750547128812111545955724923650443832153092663384957761980640080567308706909409636363783340484040402021130382135895221442398562340065133990655740145419394827351903870024905948664010325434627362926249858621275638060240923137450648096864227984363018790470978012500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-94682513933901029231984498367728202656767517699011299915607937017172668743695308526315683621692383489429907657825495258623917704394482697190335646096765724359724693777673662375527190148255098042131088740157117779812235014780194061021609696776287332957203953861678437500459692018068127054176686055039755264550798454490809137548817179428512337361119436664642914725846885763182091696307209463877005302858173177106331585321019793888166574413080739172850852440606196813729366566024640290573966257026716957460095474042868291476088886791826402455662817205438946679924760514471971651965317529282673760524146306466659504284537417572034853354133620349476688602027641846314941541750210432826962376712510334909981995780612292828520020572912591275653593989007840712757289295643121497818151650969406223768548793396069201284276810814025998003086599358801697125178339553458964971928005914689014431 / 1498727801041464571867440934514908845603568416912268749559660173810938042224187236522325445563953703133597989646505433198191925297660915618858774023996090303445224054537301306180727469951940695133174050216596402153905521340049890595790822821615742881737248142586201350515754288727686295786471313386181375889290467182511840171622792415980287299248249982427191749831705348382156017465723817145121532344428209594338226123907894614117127189979480996992300345727350801727375772847545268799443271805803550438969148291401885690669142722385459945521801997137069344591781930397755131670095515447733284984219230374959190734532452735018646352195050513182598119494748193392344969112159217532759014262156523791076742226643740511156610057282759717569351196289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 105) / 2 * Real.cos (169 / 2 * Real.log 105) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 105) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 105)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 105) / 2 * Real.cos (169 / 2 * Real.log 105) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 105) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 105)) / (2 * (169 / 2)) ≤ (-1314802482962371277109119737752534616173172395132751673675510634482829465544242876163978851994925531792734896385247075592123521315429996099060266760430660331909235020685777479585976609194415609923751739693310721028567283087192081857916445552939992631266067235876278088277157375534389187166519203280188495120588736011034852706118649989233016893246586116835827909618617059864198220701958675983936920090810279527313557535557636372544810883510488607737953007438206279003239786454597746536985877803785945765736554158838072411305128209886091259797303919077378242521529024852811483356508976721205756621337734785865080834919891512015587287393078696604733079274874641362691844160189554829444042479507017776606271815553117497411449365881500922754535704635920375389775207178155815086053617852541691376977954058211364112334957658308871045052953601342376057286459709674310346785770406585699103 / 20815663903353674609270012979373733966716228012670399299439724636263028364224822729476742299499356987966638745090353238863776740245290494706371861444390143103405889646351407030287881527110287432405195141897172252137576685278470702719316983633551984468572890869252796534941031787884531885923212685919185776240145377534886669050316561333059545822892360867044329858773685394196611353690608571460021282561502911032475362832054091862737877638603902736004171468435427801769107956215906511103378775080604867207904837380581745703738093366464721465580583293570407563774749033302154606529104381218517847003044866318877649090728510208592310447153479349758307215204836019338124571002211354621652975863285052653843642036718618210508473017816107188463211059570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_106 : (10295630140987 / 1000000000000 : ℝ) ≤ Real.sqrt 106 ∧ Real.sqrt 106 ≤ (2573907535247 / 250000000000 : ℝ) := by
  constructor
  · calc (10295630140987 / 1000000000000 : ℝ) = Real.sqrt ((10295630140987 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 106 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 106 ≤ Real.sqrt ((2573907535247 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2573907535247 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_106 : (-471217815757 / 50000000000000 : ℝ) ≤ primeTerm 106 ∧ primeTerm 106 ≤ (-941922749637 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_106
  have hl := PsiOmega.Num.log_bound_106
  have hc := PsiOmega.Num.theta_106_cos
  have hs := PsiOmega.Num.theta_106_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_106
  have hqpos : (0 : ℝ) < Real.sqrt 106 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 106)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 106) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 106) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 106) = 2028 / 5 - 169 / 2 * Real.log 106 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (435549182717886532093782155931105229018502466985652303863235454175939014254567881451558866001279126514532908427263090341333422667603085908685396934767877764391867664967467906363216692753014130024266013625897355238358584011106928161200394936549948494377779039448368929535300359421705370980012490867800025814667258731788084295251498662999723799232192911224244550796012961685510483871073261 / 6378826868223882215230566293617153125491343041725938306390468317577686911038060610831649214195452509221159432653966552771145454203001267665305837497624637101827168850440061805853748760934024152748496844384064681977639927976470259273290285457974489357108296408888862341100077519294103862582139464491159384226794362294224275102097452814390544903024874894819475274376424994660237500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 106) / 2 ∧ (2 * (12 / 5) - Real.log 106) / 2 ≤ (3919942702591794191335319011281013759554307292395601944780168408140638928202879620859109522452687496565634156643887246973706040961186522802405064964907701719400057789329733401249337590875083225061645068296084467831299339926987230321450537557919580655381987196305403388169688524703554892043768150974397231023798866289748595372064905322218737565463358782953855260184323712562800698579608251 / 57409441814014939937075096642554378129422087375533444757514214858199182199342545497484842927759072582990434893885698974940309087827011408987752537478621733916444519653960556252683738848406217374736471599456582137798759351788232333459612569121770404213974667679999761069900697673646934763239255180420434458041149260648018475918877075329514904127223874053375277469387824951942137500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-93866961337981504699856479204787955884170213547780226450257425243706393710273295637434507829391358677842317484714460972214167517053280357134375542144487547791070122560586754254431783721413568203852721706440760487514181164877545060667358653193036300804710448211179970179538805706316565060582128590169718611233429404747959785868275915137926971972843526281630827607358885213742373928326123538113437020335795618254075982045329418940220849775780541015759686489807541720548355990893070171687768555931632307141270352631088821460957891186240699854880223851764430823518777836155966091320561542945311880816022711701516361527305937070948180262704917027086306268368233756162881518299887953732697431813676447601843457689611135755373492436279919647995516314445708508292240834840852070435038071897514209002305957163350986694349817692820907417119501466315097145513196768538831170050851175225821401 / 4875508889640187866113070099556249205549180415128107922684515177229214127018402445766327461430840742356584676313009061605366971163769100742379910145512907088637867844841525413340360703193248871044696402922010348465237776143162869432800275975511114157624592207401831985696211018964004567566564207780790185258775339762380403404494195607462786217002375045491861422276927009960291405744707997435411473869843096837346580935453471912480877113630080542874144171004792901191982528894505850621947061276094286324509882617274615564024199841295433150419994809056512187550062727822572094752323037838048618278468344855577652179133303003279161730226567796104001395005194474523430704305187771275522253110151950639523757280254950160687408256104685183800142398569745664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 106) / 2 * Real.cos (169 / 2 * Real.log 106) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 106) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 106)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 106) / 2 * Real.cos (169 / 2 * Real.log 106) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 106) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 106)) / (2 * (169 / 2)) ≤ (-260599661498477817740482564892103177662214497485964864772055274107488477554433902041919452748803555683781616773549058131588384144013793961088639482331205284234321310005453359248893526295466227934867742305274272425959055396980692874987849298334880739402935909138695059501940922665740277402331822396261672707898626444879720531988612437881358859966369648117242409901566389592254768336843232620425973464778814613836006228901953103968297326208797345362945448498128330197743763445159504438261743388198611826391693473578846755159225373421749930847676837240268551533785845878953911945036150849485321869623734479981210289403971719749458717245447808340693128958635758625393569425429005986841788317366462493826928157160788768090817939696914466215231633083219588551217968695199860315683781456528680691232494445086510469428777542412110214834727088829860254478381300346210298802197934498292542479751067449 / 13543080249000521850314083609878470015414390042022522007456986603414483686162229016017576281752335395434957434202802948903797142121580835395499750404202519690660744013448681703723224175536802419568601119227806523514549378175452415091111877709753094882290533909449533293600586163788901576573789466057750514607709277117723342790261654465174406158339930681921837284102575027667476127068633326209476316305119713437073835931815199756891325315639112619094844919457758058866618135818071807283186281322484128679194118381318376566733888448042869862277763358490311632083507577284922485423119549550135050773523180154382367164259175009108782583962688322511114986125540207009529734181077142432006258639310973998677103556263750446353911822513014399444839996027071289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_107 : (2586020108197 / 250000000000 : ℝ) ≤ Real.sqrt 107 ∧ Real.sqrt 107 ≤ (10344080432789 / 1000000000000 : ℝ) := by
  constructor
  · calc (2586020108197 / 250000000000 : ℝ) = Real.sqrt ((2586020108197 / 250000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 107 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 107 ≤ Real.sqrt ((10344080432789 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (10344080432789 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_107 : (5881016549 / 1562500000000 : ℝ) ≤ primeTerm 107 ∧ primeTerm 107 ≤ (188256891641 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_107
  have hl := PsiOmega.Num.log_bound_107
  have hc := PsiOmega.Num.theta_107_cos
  have hs := PsiOmega.Num.theta_107_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_107
  have hqpos : (0 : ℝ) < Real.sqrt 107 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 107)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 107) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 107) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 107) = 2028 / 5 - 169 / 2 * Real.log 107 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (405601418691647239351142337557505535579521741186034974324628760649422491365415905771916779951426930628779016433666176118493816878552882294303945328707522288600057876976769644141946966399170515599420999005598449671434439548233245030945325757928169315273268511402295116167457326952497445999352681983371027486704945922715540328449676481902589674203218868381174056903182400466896421371073261 / 6378826868223882215230566293617153125491343041725938306390468317577686911038060610831649214195452509221159432653966552771145454203001267665305837497624637101827168850440061805853748760934024152748496844384064681977639927976470259273290285457974489357108296408888862341100077519294103862582139464491159384226794362294224275102097452814390544903024874894819475274376424994660237500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 107) / 2 ∧ (2 * (12 / 5) - Real.log 107) / 2 ≤ (3650412826486587353586206982781177680627058240498083657022661386137694120978126243741125159721383205795311190549688757664422427784645086976990538594408178372144736929644971319716609548815835050893488301671164282603807149808642659231875198011026019656071700558435142880972694687627335171210522568123737361370188354470037277432503803972174524747298163254151043282208164383948450698579608251 / 57409441814014939937075096642554378129422087375533444757514214858199182199342545497484842927759072582990434893885698974940309087827011408987752537478621733916444519653960556252683738848406217374736471599456582137798759351788232333459612569121770404213974667679999761069900697673646934763239255180420434458041149260648018475918877075329514904127223874053375277469387824951942137500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (59189239279137379028925077298551401735201053926548261377051037134575748508601205711781162301768775073691819291892932376889504953215571982462661543514420852838107534328794933461253103513303638600481660366295831300045175319603589958414563582271042188654925067420249613771896160702120028196766097287699435355466723689911530741281321150792001079531182790759578136715951202346132877808391344377409067252743627833591743450792507113415042776137352881459277345396301839494439989577032301616858782999777643021377232297853762994853483211072852084295584004248874745510435808294436805060473677707082978524135657618188938836831477823475673627451977785395721589043303816949987667101578814811720015648126320006395077843188651623934539464242428633743384174698536435009574505187303015026625724922127673193587565541763517548146661272353264375768842961722663860592324185295011636054537231377483959290306736414134131 / 2018076218515712298499656261485587062748430675569552482285646588119042468989227565529581350349237828766548251241863213316171935516831403284594379425675052358308545353032452121931794907977700594003290104750962037371776905383982124193178397075795098376615425036765565468907443607418075438823370555945895688922361921834606430350283034811194897615662206810999190402642276142190020699362253148288946794912981944298308169235559582674040097790306674334271974104562067696283253749581884117019651276070249695879100876805382725084831399984366129318219090008510695641053245600653428209636080197922905542071688649081346745366492744536565062788719339418785440174657931954713095684972565940384865739738838519751828477316538058287852095339076670169747596978549222840229049324989318847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 107) / 2 * Real.cos (169 / 2 * Real.log 107) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 107) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 107)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 107) / 2 * Real.cos (169 / 2 * Real.log 107) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 107) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 107)) / (2 * (169 / 2)) ≤ (8526165414445854667143795177445138497604649115857192303629154146312137723999799696980274649607313185023206386275758102819302931106613537944500343713551285661521202751256841194345854760174487930982083595166541055174220886124522175668340202079470796516314202978956722812150498098528563335156653750343236820536296562622320278113051304570819811147634834976345521326204998072525048501615732884560873734668464560497996160174332963797640318558842855548574572066186922943576203449744881167828124733533631936141364089892496509339589424370923149228686483690530840582660459163385105664223630467008417632626932890714088587870856593335819451896176283281788812256889081288599577046609701099354077992291144921382985573664519892254190711174916415510415587663957794989851058922849188812863990498224265820334408863354258809044126854898335259326607329363592527010550797227133372209784725112819 / 290602975466262570983950501653924537035774017282015557449133108689142115534448769436259714450290247342382948178828302717528758714423722072981590637297207539596430530836673105558178466748788885536473775084138533381535874375293425883817689178914494166232621205294241427522671879468202863190565360056208979204820116744183325970440757012812065256655357780783883417980487764475362980708164453353608338467469399978956376369920579905061774081804161104135164271056937748264788539939791312850829783754115956206590526259975112412215721597748722621823548961225540172311667366494093662187595548500898398058323165467713931332774955213265369041575584876305103385150742201478685778636049495415420666522392746844263300733581480393450701728827040504443653964911088088992983102798461914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_108 : (10392304845413 / 1000000000000 : ℝ) ≤ Real.sqrt 108 ∧ Real.sqrt 108 ≤ (5196152422707 / 500000000000 : ℝ) := by
  constructor
  · calc (10392304845413 / 1000000000000 : ℝ) = Real.sqrt ((10392304845413 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 108 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 108 ≤ Real.sqrt ((5196152422707 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (5196152422707 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_108 : (-879356450127 / 100000000000000 : ℝ) ≤ primeTerm 108 ∧ primeTerm 108 ≤ (-439603296237 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_108
  have hl := PsiOmega.Num.log_bound_108
  have hc := PsiOmega.Num.theta_108_cos
  have hs := PsiOmega.Num.theta_108_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_108
  have hqpos : (0 : ℝ) < Real.sqrt 108 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 108)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 108) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 108) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 108) = 2028 / 5 - 169 / 2 * Real.log 108 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (375932242553971829138637090992989657882000103973682252527592024046897361806919414176148963151218797510489289894659327097344323521169264150328817491815867252119664940411026453469319559369922228836018454060585648083659754407107092479797028369854211298157745267865199747953520991518617182978341465149832267251161435906023606332579589852390225881611840851718000132028347405370594065121073261 / 6378826868223882215230566293617153125491343041725938306390468317577686911038060610831649214195452509221159432653966552771145454203001267665305837497624637101827168850440061805853748760934024152748496844384064681977639927976470259273290285457974489357108296408888862341100077519294103862582139464491159384226794362294224275102097452814390544903024874894819475274376424994660237500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 108) / 2 ∧ (2 * (12 / 5) - Real.log 108) / 2 ≤ (3383390241372477122261876593356250871114244278158852277473085750963411611993977197261889936731376719170861970586851332329166503046328590428584802549787022245091878348386880531940366109670717242376537427390870606674513519415726818460627543250714579319169636555175332738767033998611586878180492777827705257902457985576074075528553168269711569826104745552289123535826258354272723098579608251 / 57409441814014939937075096642554378129422087375533444757514214858199182199342545497484842927759072582990434893885698974940309087827011408987752537478621733916444519653960556252683738848406217374736471599456582137798759351788232333459612569121770404213974667679999761069900697673646934763239255180420434458041149260648018475918877075329514904127223874053375277469387824951942137500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (883607868947939199707093095724863980520266752162593764496827155108099406741726896154121415942289693420128306884562303280165457507526068727898641617080712938554574802525790567113663004571745562799251771076994521045695966656871637775995898914087329295027107733913442285375479679497411715254072363474484952795141043645434537811014530558427394546452992972513596880319569139728318977015610052124546954231221539130789494742279572613382194736698111066340779471560623598586326364036473819832835976659903884172812755231207670406559182500210378655239088727358436303870199940081608340834567055449801572546881423513740527542135992612087972371699457978654260429503559092289938092975943643485003360336074802478326091653198989336651443066411618046406154645824421961735644976991704705995571313906715519881107942283100989433358611430007801721558438355191811627360851267081554082048085922277353287094260581989 / 16144609748125698387997250091884696501987445404556419858285172704952339751913820524236650802793902630132386009934905706529375484134651226276755035405400418866468362824259616975454359263821604752026320838007696298974215243071856993545427176606360787012923400294124523751259548859344603510586964447567165511378895374676851442802264278489559180925297654487993523221138209137520165594898025186311574359303855554386465353884476661392320782322453394674175792836496541570266029996655072936157210208561997567032807014443061800678651199874929034545752720068085565128425964805227425677088641583383244336573509192650773962931941956292520502309754715350283521397263455637704765479780527523078925917910708158014627818532304466302816762712613361357980775828393782721832394599914550781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 108) / 2 * Real.cos (169 / 2 * Real.log 108) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 108) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 108)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 108) / 2 * Real.cos (169 / 2 * Real.log 108) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 108) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 108)) / (2 * (169 / 2)) ≤ (127261220458612284074727241843424362648400824285965030037067199680074643979418353473210424338881458700324619515480454255558158838766154912907324849836799504245339704066329707769678553731326583725984094284297201791007787425072014211184487621290311024109019843689025184514672247766164378943697140844821822004245986458792739850124716858470493475621069294591869387221476242286798238697501380769303727149760592025711821404052661295331975957441478027413523791935577144154841972632359432375706175771659826032200350317777085081555400439943314705113460060318386237031286347839202462728736890982899276342974735325301756918478062031361065589537306595934754702393356122891120007526531946088146500734057620632663231782378428073084147133702867732857770724784904675155695477172421285645685054552098917484505307699006065152768896574000104817428357855069725908485182119001831525956058363 / 2324823803730100567871604013231396296286192138256124459593064869513136924275590155490077715602321978739063585430626421740230069715389776583852725098377660316771444246693384844465427733990311084291790200673108267052286995002347407070541513431315953329860969642353931420181375035745622905524522880449671833638560933953466607763526056102496522053242862246271067343843902115802903845665315626828866707739755199831651010959364639240494192654433288833081314168455501986118308319518330502806638270032927649652724210079800899297725772781989780974588391689804321378493338931952749297500764388007187184466585323741711450662199641706122952332604679010440827081205937611829486229088395963323365332179141974754106405868651843147605613830616324035549231719288704711943864822387695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_109 : (1044030650891 / 100000000000 : ℝ) ≤ Real.sqrt 109 ∧ Real.sqrt 109 ≤ (10440306508911 / 1000000000000 : ℝ) := by
  constructor
  · calc (1044030650891 / 100000000000 : ℝ) = Real.sqrt ((1044030650891 / 100000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 109 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 109 ≤ Real.sqrt ((10440306508911 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (10440306508911 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_109 : (-1054310936361 / 50000000000000 : ℝ) ≤ primeTerm 109 ∧ primeTerm 109 ≤ (-42164454861 / 2000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_109
  have hl := PsiOmega.Num.log_bound_109
  have hc := PsiOmega.Num.theta_109_cos
  have hs := PsiOmega.Num.theta_109_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_109
  have hqpos : (0 : ℝ) < Real.sqrt 109 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 109)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 109) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 109) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 109) = 2028 / 5 - 169 / 2 * Real.log 109 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (346536518934145032591497221637978984445380371131041194191912349241849196645430487252956973741035617025319556051405407525728690553528970585232438845667911353125266408509211098089574309192750054839737916713797922250203164092940528776921308539339887019817743195395817893078243209183752391468794036531636315596516090733810053345587660640330229315504817698848324861895945471562790158871073261 / 6378826868223882215230566293617153125491343041725938306390468317577686911038060610831649214195452509221159432653966552771145454203001267665305837497624637101827168850440061805853748760934024152748496844384064681977639927976470259273290285457974489357108296408888862341100077519294103862582139464491159384226794362294224275102097452814390544903024874894819475274376424994660237500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 109) / 2 ∧ (2 * (12 / 5) - Real.log 109) / 2 ≤ (3118828728913350632562101795158140873583758262859103722305368140936913693634501005926500595695054035062637427827544425119471269784923429983643717347675547317449442511131562559828135632890559581123508286804029691889377096990993890259949259453943877493193085978649370437983374577238712667596244572315776692818098917898489583383385046203715943102585750383524565932317555262242073098579608251 / 57409441814014939937075096642554378129422087375533444757514214858199182199342545497484842927759072582990434893885698974940309087827011408987752537478621733916444519653960556252683738848406217374736471599456582137798759351788232333459612569121770404213974667679999761069900697673646934763239255180420434458041149260648018475918877075329514904127223874053375277469387824951942137500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (86182106101770091491783807648258780786225060256275535036081321476159454385179664395869141304291892935055034534510033483589187512198866380272098342504549172273417783196596967917665182242129391600672915003478502287725719001435823741844854000710512843685071803679988467996773850760657810134608705227199504564801917553819271809525238438674250391190277752037622752742240860531811584684267772913223854995933211336409497175620330036730564838305228925198494506777055834654882143180032958589640737217343746712412162146404193568982736510349642924012607084672825345088195124443196911541129037463625557602106241906008848424125035284261655959380575553058456581544099739404854113966351187232341097972005601618304908603875648440436466045212967542214680437404583303462908672361101055168712144315577252074711954001979587109784046824641732155761734553259901004275940454243792361172716221147695985074085881062583 / 1836897820231190572145464899343325468670571566029530437209335205541243989551083579646481158006772921472840363797038160387342277305986983967488572917236669879918178170226871975873918209572591474008328059791097890016621823211731284598946380982768160655692617989020390257921086447996541554982339066034308609294665429296566208603279846797034289029722755355078374197605058461868961063241730865642561349325238676410193391375300455696192942344243586238484001318285828729772490524063866076291664805951942834293510486976632809321659869852436370152761198372191068743500909773394764877037640997931604688961252601474932504226923173693726777151687647613187813990088642063667742205699473353736980015548951683756330987353008863721564929446412898003396923827586137056350708007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 109) / 2 * Real.cos (169 / 2 * Real.log 109) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 109) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 109)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 109) / 2 * Real.cos (169 / 2 * Real.log 109) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 109) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 109)) / (2 * (169 / 2)) ≤ (6206286391135672426291141528616095186610265416714818674189193757200420686246878227882292194239632482637834018723152239549812114946508769900987636786233367436600191661969776864995051880422999630698905247446273672018933765840761998386970248164142293629547752747929214350020056901491086701516284175242143394003514090650982369389976376853846166488242657525624203803791803065130941214893824989196489113734104985855028518165007630410376191260771080250385101203703748452480034227306534327761447317879800574451173228383556146203722896820645881663223969772996136960072067285493344599057048283718154293506196305732214802530026037482959480846126832818060888838083485226566284918822817291717011810935535684524994446908428382937857184260413784009216896547587931491848167776923879461933215444192864743403115123662936402541238373504969327616562997112969449721907274362302077694025653079834877251503791631271813 / 132256643056645721194473472752719433744281152754126191479072134798969567247678017734546643376487650346044506193386747547888643966031062845659177250041040231354108828256334782262922111089226586128599620304959048081196771271244652491124139430759307567209868495209468098570318224255750991958728412754470219869215910909352767019436148969386468810140038385565642942227564209254565196553404622326264417151417184701533924179021632810125891848785538209170848094916579668543619317732598357492999866028539884069132755062317562271159510629375418650998806282797756949532065503684423071146710151851075537605210187306195140304338468505948327954921510628149522607286382228584077438810362081469062561119524521230455831089416638187952674920141728656244578515586201868057250976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_110 : (10488088481701 / 1000000000000 : ℝ) ≤ Real.sqrt 110 ∧ Real.sqrt 110 ≤ (5244044240851 / 500000000000 : ℝ) := by
  constructor
  · calc (10488088481701 / 1000000000000 : ℝ) = Real.sqrt ((10488088481701 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 110 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 110 ≤ Real.sqrt ((5244044240851 / 500000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (5244044240851 / 500000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_110 : (0 : ℝ) ≤ primeTerm 110 ∧ primeTerm 110 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_110
  have hl := PsiOmega.Num.log_bound_110
  have hc := PsiOmega.Num.theta_110_cos
  have hs := PsiOmega.Num.theta_110_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_110
  have hqpos : (0 : ℝ) < Real.sqrt 110 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 110)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 110) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 110) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 110) = 2028 / 5 - 169 / 2 * Real.log 110 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (317409253160506898856188567445646374858590186011456439947199691963608089191713911787630417623491332701322648139330846750548393006283852077591828596165628911565292791074081260184254271198678085710220708786422468258651745637688588795568035476578749473898293407190135816126030045026247998548130087771060256784248963855818183382916977384676472156478125174923087163537215605946640471371073261 / 6378826868223882215230566293617153125491343041725938306390468317577686911038060610831649214195452509221159432653966552771145454203001267665305837497624637101827168850440061805853748760934024152748496844384064681977639927976470259273290285457974489357108296408888862341100077519294103862582139464491159384226794362294224275102097452814390544903024874894819475274376424994660237500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 110) / 2 ∧ (2 * (12 / 5) - Real.log 110) / 2 ≤ (2856683337064572510424556020783010606409431290511509970396586621418529920201063417529506515306308245079515495193356966451163003184593585958902477783878071661641398600203728828233583556269449012349717275683591149871455931193050627916007678085510335335321616174131668678281115477511819029939230281678136470628412240388440132360024973136144840336489315552094404102663616250170423098579608251 / 57409441814014939937075096642554378129422087375533444757514214858199182199342545497484842927759072582990434893885698974940309087827011408987752537478621733916444519653960556252683738848406217374736471599456582137798759351788232333459612569121770404213974667679999761069900697673646934763239255180420434458041149260648018475918877075329514904127223874053375277469387824951942137500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (3213661424728025105149148093122177057788970158616994490274790174932058216190481607087130094306911112746703236796474059224085101921841248545622533112687933961635858353017793769195870296999835388138128256518352009445275871607332415143433092433569175526162591812344145384486145401975649988521730071373976591197083015021448190043316620279603275717625104656221249991078314629218594053874748649382799566840835832586163492166890351231593035855110581965860903690558371997822364874106414249340092697918328762341277381550892844531066817637438370726758418290875852320297200553246749285366754490590646730434083100044165028698589375537795607942088764405146526857711757514184923265839620033087779102575109446821558321460624131089284639091217889261167324752944627786825077831794515831340698879514929735661616525087447821217999556617392678564058414896129107704115902575019063399076445505566439306257 / 201807621851571229849965626148558706274843067556955248228564658811904246898922756552958135034923782876654825124186321331617193551683140328459437942567505235830854535303245212193179490797770059400329010475096203737177690538398212419317839707579509837661542503676556546890744360741807543882337055594589568892236192183460643035028303481119489761566220681099919040264227614219002069936225314828894679491298194429830816923555958267404009779030667433427197410456206769628325374958188411701965127607024969587910087680538272508483139998436612931821909000851069564105324560065342820963608019792290554207168864908134674536649274453656506278871933941878544017465793195471309568497256594038486573973883851975182847731653805828785209533907667016974759697854922284022904932498931884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 110) / 2 * Real.cos (169 / 2 * Real.log 110) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 110) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 110)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 110) / 2 * Real.cos (169 / 2 * Real.log 110) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 110) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 110)) / (2 * (169 / 2)) ≤ (4630058271557992482282439238274377912022435289247721607657921695889819063717050767036875422251516173422751311329862936135683446476768792806969871425167058012008604780012791856222400562786032658227286514710584972692497240371643781025118729274285472545364979655279274503560256300843526674531896520185620367844527631375530669183967994442402438517319078689874275016142696639787320885907686955259450741455601549507202996513780054188171694463961061277867388285668556933268264377558801526665743773478373710015077578715127732716830556208318741924757481575157536038977849487121146446283294431442716051286932934458008424506845758579456770501935440240883520747120930830773224369819234005957785385460009016710616879605338515086071897209787105667002896118364820599809850680087569788409322173294736279798046505587466799334151174775666157017532851900690247755560526978097484648603867524601 / 290602975466262570983950501653924537035774017282015557449133108689142115534448769436259714450290247342382948178828302717528758714423722072981590637297207539596430530836673105558178466748788885536473775084138533381535874375293425883817689178914494166232621205294241427522671879468202863190565360056208979204820116744183325970440757012812065256655357780783883417980487764475362980708164453353608338467469399978956376369920579905061774081804161104135164271056937748264788539939791312850829783754115956206590526259975112412215721597748722621823548961225540172311667366494093662187595548500898398058323165467713931332774955213265369041575584876305103385150742201478685778636049495415420666522392746844263300733581480393450701728827040504443653964911088088992983102798461914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_111 : (2633913438213 / 250000000000 : ℝ) ≤ Real.sqrt 111 ∧ Real.sqrt 111 ≤ (10535653752853 / 1000000000000 : ℝ) := by
  constructor
  · calc (2633913438213 / 250000000000 : ℝ) = Real.sqrt ((2633913438213 / 250000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 111 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 111 ≤ Real.sqrt ((10535653752853 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (10535653752853 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_111 : (-851286730073 / 100000000000000 : ℝ) ≤ primeTerm 111 ∧ primeTerm 111 ≤ (-53181988359 / 6250000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_111
  have hl := PsiOmega.Num.log_bound_111
  have hc := PsiOmega.Num.theta_111_cos
  have hs := PsiOmega.Num.theta_111_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_111
  have hqpos : (0 : ℝ) < Real.sqrt 111 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 111)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 111) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 111) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 111) = 2028 / 5 - 169 / 2 * Real.log 111 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (288545586167097220586138345961395193134459637263976232232568344161583987969789246255800390438665122896358920800408484066091865460112058568438287290750499727751069992978952870987178579118804770302473947640775434741414680173669919492852365981906501186468100247717453913779349405684889658401671665202763515284851539086551258635512329778281628140028810596145842442907694348799647033871073261 / 6378826868223882215230566293617153125491343041725938306390468317577686911038060610831649214195452509221159432653966552771145454203001267665305837497624637101827168850440061805853748760934024152748496844384064681977639927976470259273290285457974489357108296408888862341100077519294103862582139464491159384226794362294224275102097452814390544903024874894819475274376424994660237500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 111) / 2 ∧ (2 * (12 / 5) - Real.log 111) / 2 ≤ (2596910334232786150278420130500758571324072988830808861385022461078290316331899049114488968908191440501120100428631963457820959073137854480595149423756901212983187023648718637892727392720438063915976813871122740246181422060454517514986323691625444448206911985422170288687063518225781547792391795552985524841419017905549463946268377463055546282757064385689205222920010705523073098579608251 / 57409441814014939937075096642554378129422087375533444757514214858199182199342545497484842927759072582990434893885698974940309087827011408987752537478621733916444519653960556252683738848406217374736471599456582137798759351788232333459612569121770404213974667679999761069900697673646934763239255180420434458041149260648018475918877075329514904127223874053375277469387824951942137500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-10487796723420510064933281655607614674772155605411157934019815996039738763981124085197074434478494371624344804067123886326971706102228020100371970578624354953522744168656121333638437930445814362058269668282190131704501762585532385291186565758688590849834680286897173818901168503876212348095606389346021631715274692587818784791448224991411877249495485336525317972967375130357015653141843084410403942251983259749347711218717121382447541712918770297081199699792968935273800115956692570832467570436887796743143318357403214474978435241097808576447901991084693751251265302182246465593025840502017119391962495360788272022208792218622248634440785703018294026677261192419104484854633361351282066501871746666174510731626266768673524479655544629831491234973190815961856135657740063713802273842281181810591253338372354017569957363458912861384652516181171328390792739105593150923972231664321 / 595154893754905745375130627387237451849265187393567861655824606595363052614551079805459895194194426557200277870240363965498897847139782805466297625184681041093489727153506520183149499901519637578698291372315716365385470720600936210058627438416884052444408228442606443566432009150879463814277857395115989411471599092087451587462670362239109645630172735045393240024038941645543384490320800468189877181377331156902658805597347645566513319534921941268816427124608508446286929796692608718499397128429478311097397780429030220217797832189383929494628272589906272894294766579903820160195683329839919223445842877878131369523108276767475797146797826672851732788720028628348474646629366610781525037860345537051239902374871845787037140637778953100603320137908406257629394531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 111) / 2 * Real.cos (169 / 2 * Real.log 111) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 111) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 111)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 111) / 2 * Real.cos (169 / 2 * Real.log 111) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 111) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 111)) / (2 * (169 / 2)) ≤ (-291199382866711083319708030257922313099288753678189466478341342486427826849447533339953700093257146127656533630796169836869933932482334871672482206885376283985337121316527637490326909559596865507938951940777125352826340487187691311796508226166218585432585322089989996567892932016079810853953676969101209006242794107961879927036691910739233724299826274951484268138923691938059704157219375023163614270228349566268503199215457664899114937171929283615990282748933378330210691923234110170704267419375011824016486220840302793994955660137453771082508834383128757188673226262162368459736266854778492308774607173195845848156266534983635856603629376366915868581989825683403900655636400103391913546225672092995785681133674921210539066777833979328882975557563590744228931929772216311501101599739857151461674591142977000842354679938592377767978872511351912593734640235103969495636793973130063808849496027194341449 / 16532080382080715149309184094089929218035144094265773934884016849871195905959752216818330422060956293255563274173343443486080495753882855707397156255130028919263603532041847782865263886153323266074952538119881010149596408905581561390517428844913445901233561901183512321289778031968873994841051594308777483651988863669095877429518621173308601267504798195705367778445526156820649569175577790783052143927148087691740522377704101265736481098192276146356011864572458567952414716574794686624983253567485508641594382789695283894938828671927331374850785349719618691508187960552883893338768981384442200651273413274392538042308563243540994365188828518690325910797778573009679851295260183632820139940565153806978886177079773494084365017716082030572314448275233507156372070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_112 : (5291502622129 / 500000000000 : ℝ) ≤ Real.sqrt 112 ∧ Real.sqrt 112 ≤ (10583005244259 / 1000000000000 : ℝ) := by
  constructor
  · calc (5291502622129 / 500000000000 : ℝ) = Real.sqrt ((5291502622129 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 112 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 112 ≤ Real.sqrt ((10583005244259 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (10583005244259 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_112 : (-39687984537 / 100000000000000 : ℝ) ≤ primeTerm 112 ∧ primeTerm 112 ≤ (-39680136471 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_112
  have hl := PsiOmega.Num.log_bound_112
  have hc := PsiOmega.Num.theta_112_cos
  have hs := PsiOmega.Num.theta_112_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_112
  have hqpos : (0 : ℝ) < Real.sqrt 112 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 112)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 112) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 112) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 112) = 2028 / 5 - 169 / 2 * Real.log 112 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (2882630802620495293400948425109324997158758133860770071798377697253138700387292259472790249820705599456850702321449474981009348778948408106714588808869557027084123372627507033185845947919598364986376447992459980109528436773070285397744935649643365174581848871762585599576691152681546039001801465581862638792203943731641463838330889322294103727690471246843108916025983915560917826690512852267987 / 70738427936568912825907785361009091934395656581203588486583626569155036704979612693878499681317821696326165346098149902714653181129614158859342660421020753991398211387268044880156139085544843421522689905085659023124730483170241363718523931035333784016439379282232434485406163355405757489063428594818832899061779275884073811771141543514522511868602852812718523960040748198759345992162500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 112) / 2 ∧ (2 * (12 / 5) - Real.log 112) / 2 ≤ (25943677876017121990407155518700438206065178665402478680361575816544252843761950183165159842566132321426625928433702990882592255580908078137455167555976674633916147372904693976985012023869934593245779006210435467858984937369827487313723447341254810758543762751494245916972417823775179300454718239749613769116999582171938258784432427486424615385257985120989298864620384083305274636146170533217317 / 636645851429120215433170068249081827409560909230832296379252639122395330344816514244906497131860395266935488114883349124431878630166527429734083943789186785922583902485412403921405251769903590793704209145770931208122574348532172273466715379318004056147954413540091910368655470198651817401570857353369496091556013482956664305940273891630702606817425675314466715640366733788834113929462500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-2337479199863817038057435359099946270312628984068084245768504412072649465878247934754247519544985066346652747198835944974114684845057172153192315935463392226825513879776311192776811279568598549586065580010588889768064191268291950061091122765260118679059566640167877351935866674965350343921275224792019254536213517822504607832635761921734544396673593065601942669993502212915492055342374935104258538231123622457052329560386838529544763977855716832112518505118566584910246331653814307154855603309304438894103747443489377252429055876849990383524789565613237602484525446034654335368879811049852645535003106040021897900296906363823072880215976090129494006075647503257902464772428272564498817876849875377089367274529962243257124590911328006957932764518771519985007158136703766694500553474587662760187123346587681405881181189582091866624422331988836072557603090769803906095827859528501727895209 / 65058892327388791723111456334901844679764498819148380145080974464202493196609925367265833501576108898935940068870384612264504697205551218198829837667228737451309411747533575166054706857465350866684969862623666017085098646243932546200671267459591704784315257599386942932214142829729853377696286087542804241986278672458288786133869300641324197225676997567515353253664569306053390361140680251750303578010975918143754052448178062381682531070207053113793486427160949057928798717971510011529955799905487449494454441143186000445807848894394124894700323883449559801341556397336669434710365110420137474204097300680135533437824842341262630718595649333653188848700513228390017369900396992929941908336104179806126946443131448876878597416677841184062229624072625319938724463233947753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 112) / 2 * Real.cos (169 / 2 * Real.log 112) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 112) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 112)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 112) / 2 * Real.cos (169 / 2 * Real.log 112) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 112) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 112)) / (2 * (169 / 2)) ≤ (-64917139226635204193312304566148043449577492835528413846174189480526825583368557396913660262328510993118146164716109928227251380888099023055195681853299995313052743507870455881692716621652492318456115053019271485102433604659009111431097188936564382203679678348754460573397325182493797766550248271698638997165000755728589508590590006496909183814107245002670330501598148633991139268919406885518976906975157030021057320537081226824214563990279526994709941304983713595477939951932489650761629850261406437413962720967830301892869904693657020441181515289662686739870160662920125744729978004057571696040832644279760822755043349852902150578832274924333793340490326728203152291122657562180527290370363857593315302772547332639924608214004387409374899155985130922206864896972481537813052509578271285288417086530700082720433219510768454274856392252304274825700031096482471868498391502612269916166533738298216899390292407 / 1807191453538577547864207120413940129993458300531899448474471512894513699905831260201828708377114136081553890801955128118458463811265311616634162157423020484758594770764821532390408523818481968519026940628435167141252740173442570727796424096099769577342090488871859525894837300825829260491563502431744562277396629790508021837051925017814561034046583265764315368157349147390371954476130006993063988278082664392882057012449390621713403640839084808716485734087804140498022186610319722542498772219596873597068178920644055567939106913733170135963897885651376661148376566592685262075287919733892707616780480574448209262161801176146184186627656925934810801352792034121944926941677694248053941898225116105725748512309206913246627706018828921779506378446461814442742346200942993164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_113 : (5315072906367 / 500000000000 : ℝ) ≤ Real.sqrt 113 ∧ Real.sqrt 113 ≤ (2126029162547 / 200000000000 : ℝ) := by
  constructor
  · calc (5315072906367 / 500000000000 : ℝ) = Real.sqrt ((5315072906367 / 500000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 113 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 113 ≤ Real.sqrt ((2126029162547 / 200000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2126029162547 / 200000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_113 : (417350025883 / 100000000000000 : ℝ) ≤ primeTerm 113 ∧ primeTerm 113 ≤ (417433841501 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_113
  have hl := PsiOmega.Num.log_bound_113
  have hc := PsiOmega.Num.theta_113_cos
  have hs := PsiOmega.Num.theta_113_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_113
  have hqpos : (0 : ℝ) < Real.sqrt 113 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 113)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 113) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 113) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 113) = 2028 / 5 - 169 / 2 * Real.log 113 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (2568235719368952033051117674190480280720491409973658059635399788591195844505181664113596383666081380753874392653670313089973657464899663512812538130460653234303511760201890074891727660078709626727816336022769517570496612384851523694387684063610716769525676872368692922198992865573472953011491901114876093764813813454339362427521280700767637352319168012257708590265866512053070764989245814767987 / 70738427936568912825907785361009091934395656581203588486583626569155036704979612693878499681317821696326165346098149902714653181129614158859342660421020753991398211387268044880156139085544843421522689905085659023124730483170241363718523931035333784016439379282232434485406163355405757489063428594818832899061779275884073811771141543514522511868602852812718523960040748198759345992162500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 113) / 2 ∧ (2 * (12 / 5) - Real.log 113) / 2 ≤ (23114122127857295763747713000975041176500530174491696469994267209119201886170382470902972907889635073571157236916599421598723108838589387111039621641480424946160402252864471008301925596279822029759443519257404475320096623463795927845446366702592133219441014526212051159466430277236089963984858873490070048194423308445737213388796834251774641126807041417605743033850303774252494538854141733217317 / 636645851429120215433170068249081827409560909230832296379252639122395330344816514244906497131860395266935488114883349124431878630166527429734083943789186785922583902485412403921405251769903590793704209145770931208122574348532172273466715379318004056147954413540091910368655470198651817401570857353369496091556013482956664305940273891630702606817425675314466715640366733788834113929462500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-537419128500587146696996569607903719753940980673480478504609972452091891881639142951483972338881926447550502877440783436244968541231782361446217410128820427015661449126360096779945828406627317370935105442992916983721883542549691547381442029564219143345698170473317420003126328572020289906575751424010719033133953178772790271665956503314842656486713275299422529381839610275176254450335133653761943910232763552503735357113841258669682065804368084299919964031158938505670402356324329628645129390801365575131680377098554740866982827356995901086084448457198729775770759919782951604056844828839457327394432733618059905374490314751338924671881970556435985748708192562179951303955196100076705607202311845402848475183197158172207347240654624044956597114778123782662167417492517340236640743982784966688702693281920359670132892213545910960443528919908425260281669237886597690768485964341739135832409564526127748496298211 / 16264723081847197930777864083725461169941124704787095036270243616050623299152481341816458375394027224733985017217596153066126174301387804549707459416807184362827352936883393791513676714366337716671242465655916504271274661560983136550167816864897926196078814399846735733053535707432463344424071521885701060496569668114572196533467325160331049306419249391878838313416142326513347590285170062937575894502743979535938513112044515595420632767551763278448371606790237264482199679492877502882488949976371862373613610285796500111451962223598531223675080970862389950335389099334167358677591277605034368551024325170033883359456210585315657679648912333413297212175128307097504342475099248232485477084026044951531736610782862219219649354169460296015557406018156329984681115808486938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 113) / 2 * Real.cos (169 / 2 * Real.log 113) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 113) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 113)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 113) / 2 * Real.cos (169 / 2 * Real.log 113) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 113) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 113)) / (2 * (169 / 2)) ≤ (-7462655854674694903350308458409692194159032905467074476048368626706604564485332304402856511715480182451429565786758653280815214094016761771873553076551932124961852590747130430293918782425798375129841861150475136140541379680489453864821747756700750670917085374909707800809647008949670647159705868759880427741429040005670798485599977925705324390522847479804096024052366396354247184232015850834457905121667997805619422908905506233505140215756256905087619867170570608268428066605303542350670957808894813058097373506318205695866834420482289016836625447059081667379902466126542315842444311490107605983840120851977377598615962778614694820480664225811219204986194373048798820704878327291893551667673211794706081360821363403879140334999315317780721927195172971027682928437454314509373882814027484422350232944218176623186719950300921444605218334703974382324811287735635603692734531612483623964509261394986103098759767 / 225898931692322193483025890051742516249182287566487431059308939111814212488228907525228588547139267010194236350244391014807307976408163952079270269677877560594824346345602691548801065477310246064878367578554395892656592521680321340974553012012471197167761311108982440736854662603228657561445437803968070284674578723813502729631490627226820129255822908220539421019668643423796494309516250874132998534760333049110257126556173827714175455104885601089560716760975517562252773326289965317812346527449609199633522365080506945992388364216646266995487235706422082643547070824085657759410989966736588452097560071806026157770225147018273023328457115741851350169099004265243115867709711781006742737278139513215718564038650864155828463252353615222438297305807726805342793275117874145507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_114 : (10677078252031 / 1000000000000 : ℝ) ≤ Real.sqrt 114 ∧ Real.sqrt 114 ≤ (20853668461 / 1953125000 : ℝ) := by
  constructor
  · calc (10677078252031 / 1000000000000 : ℝ) = Real.sqrt ((10677078252031 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 114 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 114 ≤ Real.sqrt ((20853668461 / 1953125000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (20853668461 / 1953125000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_114 : (-183 / 100000000000000 : ℝ) ≤ primeTerm 114 ∧ primeTerm 114 ≤ (29 / 10000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_114
  have hl := PsiOmega.Num.log_bound_114
  have hc := PsiOmega.Num.theta_114_cos
  have hs := PsiOmega.Num.theta_114_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_114
  have hqpos : (0 : ℝ) < Real.sqrt 114 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 114)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 114) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 114) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 114) = 2028 / 5 - 169 / 2 * Real.log 114 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (26395762339031085865830692580528508186735138978720541365226987038072889282689443971294370801151475212084489136479840107475612389445205568157873471770307156129153163474594368607039404985771091724073485285270883051275205882139538671277601249463827066517047191635844429779027989799002720597359734062511742023609792632546546062466500119033738359423058473639349911862342898424600031583766472844931269681921 / 827433262863565308544407915713908312111256549869834614425413066420411704206193042988150402687848109761127951125033785558495223575887130574152916424385494704159966164648419464210911411843162133723554890203049075703188891814272416361448763058806575204344364783932753211467858181479739644027446516538169258383456254317695909754413419639237481526695532663387152030398085315062988567096042111987500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 114) / 2 ∧ (2 * (12 / 5) - Real.log 114) / 2 ≤ (237561868708108455416311091862421117058081283716308555409437984077028044913843350802533290524129738034097924860696265120709698480209619283187716481061498504516441956359337727569400581072640950742785632117423812941190204264878804647266639791015985960404258768223862795265835166724187159188039893087652287808943682571923287573955236153593781856361244755014334443997814475274995262243314371097206813986311 / 7446899365772087776899671241425174809001308948828511529828717597783705337855737386893353624190632987850151560125304070026457012182984175167376247819469452337439695481835775177898202706588459203511994011827441681328700026328451747253038867529259176839099283055394778903210723633317656796247018648843523325451106288859263187789720776753137333740259793970484368273582767835566897103864379007887500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-574044495581540408489805117163133776321627666704818882246626724751096271157278951762235439670872452637227031119057210000301567072894165722376696694857660834303000920657968143702339581599752559806705169750345729795865992228735933927500127984273195114140234133695915217242071663605906389047743196112532118797050260734701595863786943460027624837814268099071086088697341740130615253041689139698955145299438497708448617370275676880129718628282268408626140486070632873163856562026569229789207862401588718390335306819682886535671236369750315594645683317983612305701337982685972780611487981479888957101933451168977490659086770227571703122908780200532584539688654341594569532614257204122505356270397432286076931949869402122101489346541074069486808592061269935314257217125327128643481678510391119636122017464367610612143966439510829290340495029096465171903882395650034758458118592942138546996688288553056845929 / 37335477717206577602151319922413094356567414127208235257655497045841246968253483343498465513863823167446947072576653530201573337945944244348536200037280779557772956930730904087789721737451599128378671149444743516414714104563532655085629914143783053488494802828986434363357841525258865345787835395069715570682723902164381364134066200452475958933701014172398559848763895214086693410594490240796502131978772718303189721048926590777876683147522446247907270596123623451809777483374213545031492396244491155986999786150169772227237262527540125458328173535159470862793982731178005859371013768002760688415246789065155712087175187286717848646225082184384126970626110224902882511197425015083435780076465874363949799767921583466721098434774547923779943767248306938723887330900403655500774560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 114) / 2 * Real.cos (169 / 2 * Real.log 114) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 114) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 114)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 114) / 2 * Real.cos (169 / 2 * Real.log 114) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 114) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 114)) / (2 * (169 / 2)) ≤ (-318788461144738014289407176107751080033926545033767956254369998703132737585620414308066861018986766607429283160491082719469353098106586260247254557730269229290300182644746203944412001951428603140026524582328018992612246008523745914496079132243098694256109312191975572374076879727463215166956687547797391859209570478710573714618001470582860669351146446339097772011586307974298472774621288127090366376540507695939176087417640505455432209706243605771606722778066255061377625752143329760591717960457952131843673733533808946658978416724190658154188488884112450751530107560671037986890152249337935498201215127361423352724504773462415306342091241788528731433876593734072888991335155589000477021538572822618300576933248625460430877999630434903074485577122082731639818681209257769088072991149073395075880178253166044152685637183726217097978783967510914768028239039234691203771857924524759149287987535135502997198698041 / 20741932065114765334528511068007274642537452292893464032030831692134026093474157413054703063257679537470526151431474183445318521081080135749186777798489321976540531628183835604327623187473110626877039527469301953563730058090851475047572174524323918604719334904992463535198800847366036303215464108372064205934846612313545202296703444695819977185389452317999199915979941785603718561441383467109167851099318176835105400582736994876598157304179136804392928108957568584338765268541229747239717997913606197770555436750094317904020701404188958587960096408421928257107768183987781032983896537779311493564025993925086506715097326270398804803458378991324514983681172347168268061776347230601908766709147707979972110982178657481511721352652526624322190981804614965957715183833557586389319200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_115 : (10723805294763 / 1000000000000 : ℝ) ≤ Real.sqrt 115 ∧ Real.sqrt 115 ≤ (2680951323691 / 250000000000 : ℝ) := by
  constructor
  · calc (10723805294763 / 1000000000000 : ℝ) = Real.sqrt ((10723805294763 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 115 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 115 ≤ Real.sqrt ((2680951323691 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2680951323691 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_115 : (0 : ℝ) ≤ primeTerm 115 ∧ primeTerm 115 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_115
  have hl := PsiOmega.Num.log_bound_115
  have hc := PsiOmega.Num.theta_115_cos
  have hs := PsiOmega.Num.theta_115_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_115
  have hqpos : (0 : ℝ) < Real.sqrt 115 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 115)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 115) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 115) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 115) = 2028 / 5 - 169 / 2 * Real.log 115 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (273594716011344064947117864106345239307102834771486194771278374938766707582007858191647132262964433881887296403428527820993096339079089512925929009798146776939729839783906997104800223398107004226204865905573767214227365348893381195001689838457576573698577576507388605532026559910655283729188956519966714116623439165117152127551486909989606518859736635049591197287126052465815040114195636967160683053722787869 / 9936636951962664291091400671321252067152646683564795316454026835098993531283425985121225316223938383792178192653068355400327996475369216306566057658364737661815287911635058213094728824799003789102699717344624116579762666719787491088058219636814514756644228902235810056232182754950197107989520915195192704065083940082412685585743457899986884041789858103757011474378272169652964009382131666394655637500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 115) / 2 ∧ (2 * (12 / 5) - Real.log 115) / 2 ≤ (2462352536194876006097149029958479974234436520899862979878240191178630391204245404625560136180689210564184523226543534338072333580595434874645071885536173157742614222396322986303376033824512459841880836817275799591025342277316870447228261718882217310304360564951608447133758631374573949359498020347239538904682170362886895400855106966939844150324224347070676262199824935297281239342624418369310209886654949579 / 89429732567663978619822606041891268604373820152083157848086241515890941781550833866091027846015445454129603733877615198602951968278322946759094518925282638956337591204715523917852559423191034101924297456101617049217864000478087419792523976731330632809798060120122290506089644794551773971905688236756734336585755460741714170271691121099881956376108722933813103269404449526876676084439184997551900737500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (20741264632214168776457572797270681437531333754880834389891890230115318112319573030489718709462411862636020334805009499528412356606429845385252664731920737301243440540774331928748817181883425052292105201607748841739979431849880550456149760841961527214652265420247664543155607564616475043099699882228509013268828011152518705687411311613064548304078354044260195853727068154198692893859344764049047744416989562405087132579593139772497022228107352424142151101475091524680218262525786476248426123730733781199002502981917637277399735863691351001614606253557661445754659000884985829131382891117298117017345479818274340969618006704236422661149135348214777827246275657406312114092295160723779734678711643598566315168438933120204678486455315933294533483440726615775816102245528928465333807853700131161503778773598292698990257368551307238784876597590787659267468686108014296414830959082951985181511762227358656894947654386191174648147947853886486650811 / 4457406215108380178167615657799012113944754207920261751225553143734294328334786043107088913354661090025495995809771902204850026066546904126609596705277664260023205070163321822611105007083465257096980148940500049288260028698730864427508616424431541519645461811776233070949315473052236006623408177165807719729534476933328313704814542231340130510550944602124570289248250395132726743791782243698808179420720776628767278957661793008956318538085140227387297011225093231277963107933889796747579313463966333148774132201175298713019727923554845917198545829225149969923585808444285540594992733021817072842410015297215413614647916377074096687874241852798998749369410033686209786115248011560290844598631610322549430005461970239306754955895351372211199295188089985247706886889211798423354635931036332284212112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 115) / 2 * Real.cos (169 / 2 * Real.log 115) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 115) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 115)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 115) / 2 * Real.cos (169 / 2 * Real.log 115) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 115) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 115)) / (2 * (169 / 2)) ≤ (747567000697838739975244658626627653246728392920066387086352364655222948754539772988576251109711515074214164013303226702962606045036291134497369424826191838160134834360010234211662464688562950130656161695454790268980709353135180660563939947539618498735447266547915941821969013114273933772133786578299652450542905783400622002694506354320412651881931026789073366793398492842609786335196054255459256360976704261539407761340808885229452976456581921272641748743140236966854471185682338188864678972788258528451261140047042146171432179122031525070983598877001710106573480289186087322370867697541717734259283003631905973712504239573598789006232352818756594141957838027356185937995908803891200632749483814487346228778051114919951702555091285855808631362931358750521103846424116313298513947294561418735108357987999151743983318923070951082885944433698609639765904353270020831254794023769523472834600768978114189109028847895846459 / 160466623743901686414034163680764436102011151485129423044119913174434595820052297551855200880767799240917855849151788479374600938395688548557945481389995913360835382525879585613999780255004749255491285361858001774377361033154311119390310191279535494707236625223944390554175357029880496238442694377969077910263241169599819293373323520328244698379834005676484530412937014224778162776504160773157094459145947958635622042475824548322427467371065048185942692404103356326006671885620032682912855284702787993355868759242310753668710205247974453019147649852105398917249089103994279461419738388785414622326760550699754890127324989574667480763472706700763954977298761212703552300148928416170470405550737971611779480196630928615043178412232649399603174626771239468917447928011624743240766893517307962231636047363281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_116 : (10770329614269 / 1000000000000 : ℝ) ≤ Real.sqrt 116 ∧ Real.sqrt 116 ≤ (1077032961427 / 100000000000 : ℝ) := by
  constructor
  · calc (10770329614269 / 1000000000000 : ℝ) = Real.sqrt ((10770329614269 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 116 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 116 ≤ Real.sqrt ((1077032961427 / 100000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1077032961427 / 100000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_116 : (-93 / 50000000000000 : ℝ) ≤ primeTerm 116 ∧ primeTerm 116 ≤ (153 / 50000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_116
  have hl := PsiOmega.Num.log_bound_116
  have hc := PsiOmega.Num.theta_116_cos
  have hs := PsiOmega.Num.theta_116_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_116
  have hqpos : (0 : ℝ) < Real.sqrt 116 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 116)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 116) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 116) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 116) = 2028 / 5 - 169 / 2 * Real.log 116 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (230578702906436401093390611310663643678963199442338292339194396085746003563470621091436571416478265748328979365018716633124254968847373971363592334969812152696426980697806020147234684896022509012469699069260596531035154312208957110548036977095908467382960709746800985254385267243514284165485052564271563328000706004591684279963262801503417284122616309918403524604685595151237214964967209890573085709972787869 / 9936636951962664291091400671321252067152646683564795316454026835098993531283425985121225316223938383792178192653068355400327996475369216306566057658364737661815287911635058213094728824799003789102699717344624116579762666719787491088058219636814514756644228902235810056232182754950197107989520915195192704065083940082412685585743457899986884041789858103757011474378272169652964009382131666394655637500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 116) / 2 ∧ (2 * (12 / 5) - Real.log 116) / 2 ≤ (2075208418386672984537535404591300404175836816000402944875482344570490032733876592196485097057950133352293292340064159814116512208119986313126865759952051901848483032647550618385210067195077196290355516498117465149446766665241009623892206899834253933115700541206089401767956245872577293444057450713814663244591175975928145100144666486560428875014714618388086826687588306910255769240808931821028059886654949579 / 89429732567663978619822606041891268604373820152083157848086241515890941781550833866091027846015445454129603733877615198602951968278322946759094518925282638956337591204715523917852559423191034101924297456101617049217864000478087419792523976731330632809798060120122290506089644794551773971905688236756734336585755460741714170271691121099881956376108722933813103269404449526876676084439184997551900737500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (598228322600356724855964818512966765172432783744604752648693605136202946962987991868669094172238825823323623799066123151689610709218483864188349960957892738013345266821556740522856088893088824974311134182824455070036640100493621148859428209379681987738403886460282540648497663432923886314415190987965587909456789126089184294766447811956853556114190830753094785286408878448252375861630664310470637708732543273381983571322986787701206607379102777474368654474970700414836681679062797140454253280169959546265500060000542887165147279146500430949064494678542042310749332210458411320160478699081437230283647992823013777087801488262232573276143749519525102023963212993066736481900058398553552223065084164858649251482008241833031566298375861599041020706589718611040342887961603802224735755724109473587145230135020389318273495076986039178279907366105755364392233371401950315826007753412937883611446777409270464669977255565125089314615461332719071 / 35659249720867041425340925262392096911558033663362094009804425149874354626678288344856711306837288720203967966478175217638800208532375233012876773642221314080185640561306574580888840056667722056775841191524000394306080229589846915420068931395452332157163694494209864567594523784417888052987265417326461757836275815466626509638516337850721044084407556816996562313986003161061813950334257949590465435365766213030138231661294344071650548304681121819098376089800745850223704863471118373980634507711730665190193057609402389704157823388438767337588366633801199759388686467554284324759941864174536582739280122377723308917183331016592773502993934822391989994955280269489678288921984092482326756789052882580395440043695761914454039647162810977689594361504719881981655095113694387386837087448290658273696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 116) / 2 * Real.cos (169 / 2 * Real.log 116) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 116) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 116)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 116) / 2 * Real.cos (169 / 2 * Real.log 116) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 116) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 116)) / (2 * (169 / 2)) ≤ (21542610612771031411338835712210227513444504480036678897697548025161049010987554738926847522334481280477766353842874366294041258628337143625529244125729893889497502638828627848983347879262813267542088921658653010766503185438469081767032930379546143412859429793305677119366819279166445731143810204267545212411016149180527983398009002337508371472342723148801657058067228501300102219438822542168165085407377532469623948993969506881754787879976020761122401364350901827292313719357226714739934782190182220998668613938423492737879452173432601142049898310049547382496549523278518078787636722668037334839012026764876654140518800047176398112270216663357315458488075438528353493974467416078732529400229786251277203462446288490815058235287543216841669848752515315689858560194998172090991894054380028243531733898273980453703496317801750800926942031990391871821726430769837754154877222042622020191427702491565419436004613010193 / 1283732989951213491312273309446115488816089211881035384352959305395476766560418380414841607046142393927342846793214307834996807507165508388463563851119967306886683060207036684911998242040037994043930282894864014195018888265234488955122481530236283957657893001791555124433402856239043969907541555023752623282105929356798554346986588162625957587038672045411876243303496113798225302212033286185256755673167583669084976339806596386579419738968520385487541539232826850608053375084960261463302842277622303946846950073938486029349681641983795624153181198816843191337992712831954235691357907110283316978614084405598039121018599916597339846107781653606111639818390089701628418401191427329363763244405903772894235841573047428920345427297861195196825397014169915751339583424092997945926135148138463697853088378906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_117 : (10816653826391 / 1000000000000 : ℝ) ≤ Real.sqrt 117 ∧ Real.sqrt 117 ≤ (1352081728299 / 125000000000 : ℝ) := by
  constructor
  · calc (10816653826391 / 1000000000000 : ℝ) = Real.sqrt ((10816653826391 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 117 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 117 ≤ Real.sqrt ((1352081728299 / 125000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1352081728299 / 125000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_117 : (-120672169067 / 50000000000000 : ℝ) ≤ primeTerm 117 ∧ primeTerm 117 ≤ (-60321329311 / 25000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_117
  have hl := PsiOmega.Num.log_bound_117
  have hc := PsiOmega.Num.theta_117_cos
  have hs := PsiOmega.Num.theta_117_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_117
  have hqpos : (0 : ℝ) < Real.sqrt 117 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 117)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 117) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 117) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 117) = 2028 / 5 - 169 / 2 * Real.log 117 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (2377214322205939498399649077036728031788701278103388805588232886599753232310989593613330899039093246993974020838711027766171985112660245835840290282230362796432132643918468926469364995525784233346658109410019533069399203326576334866713645036568150880902714304971324443129340394386014746400869993523000048502167005511961324918140037301224850944034635176718532523184656174668259559062182959565436531973452710834492853 / 125691869452028552035881224893568752659360458342343457293848630444210597538024097800355364877848164083822599922919585711494518737951757416487649376082086435600893608546298072352053037828496556192636976334496895588944705351357276543157345095806084403648265840489520814869269829912953461435384842524852413293660516691390245833049111394522246391824521998336603404252277630151661514803545745226597574157687337500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 117) / 2 ∧ (2 * (12 / 5) - Real.log 117) / 2 ≤ (21394930068133257266926651748496457035637315362419595734721695886285540043832629261070739033755438575893704144005930348388595259795272542745875846715286964067458787883964334013361981073031083749521121285300294960403769157099044669657266178402302602975400559318250185558376004932497403135569661464191900294945330938685791827328692038637343644214237313337889216221604776916186137154481079270487113292857430259942779123 / 1131226825068256968322931024042118773934244125081091115644637673997895377842216880203198283900633476754403399306276271403450668641565816748388844384738777920408042476916682651168477340456469005733732787010472060300502348162215488888416105862254759632834392564405687333823428469216581152918463582723671719642944650222512212497442002550700217526420697985029430638270498671364953633231911707039378167419186037500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (27975261982595201540072158270724056191126295889678228366185109276525850181324054510405873718899185762610589270406821568372486199023480339843120735522661010454280310753561693104466524912947340267839726022416341581954866509951165499833340181829832661187563466813797276169118465227295384532735858207946118019895566246276582796705743660671216333576793359709484965037640323505392396325691321344390783623106807274775488647420836463292425220220743423051842813674100296438692950949616852195218515254599987717025298558837072970765680578195686976349762261235056898457452172507833961355480367087715403469341692740423841515895761901327220462718613959761985587150202406206299118231219715247924654716195703911841531789491300351440650343209968153684312506478745360152660236742365912167420915223225165460342385994274700675728362687018407525402424297637251683674844424338569606517316398263655301584917976720054356222125348204758174047537591888606883231836317089343 / 1567112958831460151011667601640475188998369773962412508167439843812567723103059915758203869724124147888202581795024716950180078560544279492866430314641593670803971577376322228933930220562911832915374765138759743300225708585997554686642929437206495689203383851100835780621754223620671124946770135389608574182655649012312926644580719922433309924921083221305095399496224874492551815933230743266924788525257876178383219510559759163793351117726589390268245878732553436631410771812104262220783362991236126721971897703266472937865204523961392768568477737845971390705854029132352779774441138082670126193540436614813351611168756940060285569333755044244812393347076918327965551595553113427151087255025928053962176665366259572590338855290957341357234403805895784749531347582581433993597830241679620729412466174285512242931872606277465820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 117) / 2 * Real.cos (169 / 2 * Real.log 117) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 117) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 117)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 117) / 2 * Real.cos (169 / 2 * Real.log 117) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 117) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 117)) / (2 * (169 / 2)) ≤ (1007355779998902887481451193427260902498482084077321805000982868641114101570537496603632927880876364077337949581814434512550518702782927093542034412474887932937935657025968275067732284960462478849520129316277439388818568689299670884859371146681968608617108254997978646186124006630977713382098250369793548684771171222107125657976807924963556830053963886020335633937664068265519421253463595365600166056924993742606280182775413453638222993854279711742964532760015558139453029846974760125066428690759136399530366841986455728311221613083338768275274955584622591428558927062246401574572704136369308584057208116008519457847299630826409563595726198628927678426792498077449121623154937065279567144167241890218705374866483202313043217690666420529066582048454841295658553595100868265944566287788904545938299606017385654924289548062405514232189147258991608715006210635177596005824726772351705898273864887303566504480608427691243392917809584196506592237470386837 / 56416066517932565436420033659057106803941311862646850294027834377252438031710156967295339310068469323975292944620889810206482828179594061743191491327097372148942976785547600241621487940264825984953491544995350758808125509095911968719145459739433844811321818639630088102383152050344160498083724874025908670575603364443265359204905917207599157297158995966983434381864095481731865373596306757609292386909283542421795902380151329896560640238157218049656851634371923718730787785235753439948201067684500561990988317317593025763147362862610139668465198562454970065410745048764700071879880970976124542967455718133280658002075249842170280496015181592813246160494769059806759857439912083377439141180933409942638359953185344613252198790474464288860438537012248250983128512972931623769521888700466346258848782274278440745547413825988769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_118 : (6789237807 / 625000000 : ℝ) ≤ Real.sqrt 118 ∧ Real.sqrt 118 ≤ (10862780491201 / 1000000000000 : ℝ) := by
  constructor
  · calc (6789237807 / 625000000 : ℝ) = Real.sqrt ((6789237807 / 625000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 118 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 118 ≤ Real.sqrt ((10862780491201 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (10862780491201 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_118 : (-59 / 100000000000000 : ℝ) ≤ primeTerm 118 ∧ primeTerm 118 ≤ (37 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_118
  have hl := PsiOmega.Num.log_bound_118
  have hc := PsiOmega.Num.theta_118_cos
  have hs := PsiOmega.Num.theta_118_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_118
  have hqpos : (0 : ℝ) < Real.sqrt 118 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 118)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 118) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 118) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 118) = 2028 / 5 - 169 / 2 * Real.log 118 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (1842352074722886135024011885754150443210407230179688029524264536766048350075148020570349338141679797724327617162136608171769123213102607901014128375359588593716070976545558496626766077976160714013244338667842504002302703384579710339098703431707049603195877606425920752876560893061348066081282848859014748141061685344464519702096623078497501252752263659702047171793163845914375858076225164645534699368143873334492853 / 125691869452028552035881224893568752659360458342343457293848630444210597538024097800355364877848164083822599922919585711494518737951757416487649376082086435600893608546298072352053037828496556192636976334496895588944705351357276543157345095806084403648265840489520814869269829912953461435384842524852413293660516691390245833049111394522246391824521998336603404252277630151661514803545745226597574157687337500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 118) / 2 ∧ (2 * (12 / 5) - Real.log 118) / 2 ≤ (16581169842364181269408570132946862822657408413941645077017950312189233454878039909461555997664621142511568841077764077176035602741503255770772188058124119078287529225012122013709016524842571660191090669842654705679323975482300445684357754004756277480934764712675270437615214354534875909016280613286621482002418536610081350389383119558018016587545075988612441957042894022490519082972705622375589712267617059942779123 / 1131226825068256968322931024042118773934244125081091115644637673997895377842216880203198283900633476754403399306276271403450668641565816748388844384738777920408042476916682651168477340456469005733732787010472060300502348162215488888416105862254759632834392564405687333823428469216581152918463582723671719642944650222512212497442002550700217526420697985029430638270498671364953633231911707039378167419186037500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (60883633746191940982775522266295278931963021367621037152701954352011178280715587081657235405698287885764373348013755479727626753876483857036538423215429292921245750190616152708984023796381169554790898823949286374807214778613740819401416454150435367410052258268726130955803774756950080280740077172936886100989466971180007287703064150745162498804540256498831378329189977914913442269959397202036178341431799199215825730535680243068177687702403679068214336184354198836510020527847446942387937173759210392656140571256603021744113669543974455909551333686289222737139000661279368224916755733871684869048236639540267567988341426150572041607514306333719323490300875658353780100487568099452033716601318615389340705393709075782200104703220728658270053509319519658705903368964533855804629663204247328049885144873920635547895637177802273033122812643266466245903436281539380199839797942567653737865391486909315686378588306556847373619537064665295127176146311047 / 5258358521342902909783073174584841317693294669127714106125380485329942441025645293523438018879498247987263713306559480322406483381444090923238112107537995919862224962300654264085199407862322681955430431136448437090487912340067110089924148408154362956166807760166111934403956981719260305638990212756141440902887455419952125981657193514833377241068959231562277483590891180786886441420810751525948566568514568869197960900815072079788086213188083828767731809721171047581498180683676924359744434022074921003578894739521104407343823036535492427822272359806647350338501102244755034895246050579756512779257141964206479932905249526978092803679076893676954880532174485480527379935547844687962811102483416112356618749001891192283158897681826832547210951056547130846478663432809311140066683019198239955086099619736336914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 118) / 2 * Real.cos (169 / 2 * Real.log 118) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 118) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 118)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 118) / 2 * Real.cos (169 / 2 * Real.log 118) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 118) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 118)) / (2 * (169 / 2)) ≤ (21925563054711666678682739258085976360401550800525154912585703975411958023288876667146564212404237613979564315515829765535614454152423677505384914041175055009143446048974934807714484360698547580821609698824050555613946660388148232309936625526786749985191544321971040292604770189743423425834417614451801508981116871171353997042772468197370957994935546804318217028746428964933148546647169319109543934426296544263635443408607166695264315159420081074812507971291495728102744626500683606264261898968977974258715041008546919065439531664148155202497266541104343104879676689015848329357780957844446760280910094795416091574289794701315286047791095971150453674383729960211760953364090926443002390623392275207693450069775326398065094035392773287755004317910246813154977596053739598231393599091477775992445858121063453000787565164124032197022126685604296461129476185711086680115198379570596045228132302411507353850516184356905284690338175050162137129 / 1893009067683445047521906342850542874369586080885977078205136974718779278769232305668437686796619369275414936790361412916066334017319872732365720358713678531150400986428235535070671786830436165503954955209121437352575648442424159632372693426935570664220050793659800296385424513418933710030036476592210918725039483951182765353396589665340015806784825323362419894092720825083279118911491870549341483964665244792911265924293425948723711036747710178356383451499621577129339345046123692769507996247946971561288402106227597586643776293152777274016018049530393046121860396808111812562288578208712344600532571107114332775845889829712113409324467681723703756991582814772989856776797224087666611996894029800448382749640680829221937203165457659716995942380356967104732318835811352010424005886911366383830995863105081289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_119 : (2181742422927 / 200000000000 : ℝ) ≤ Real.sqrt 119 ∧ Real.sqrt 119 ≤ (2727178028659 / 250000000000 : ℝ) := by
  constructor
  · calc (2181742422927 / 200000000000 : ℝ) = Real.sqrt ((2181742422927 / 200000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 119 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 119 ≤ Real.sqrt ((2727178028659 / 250000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (2727178028659 / 250000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_119 : (-41082519837 / 20000000000000 : ℝ) ≤ primeTerm 119 ∧ primeTerm 119 ≤ (-205261874239 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_119
  have hl := PsiOmega.Num.log_bound_119
  have hc := PsiOmega.Num.theta_119_cos
  have hs := PsiOmega.Num.theta_119_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_119
  have hqpos : (0 : ℝ) < Real.sqrt 119 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 119)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 119) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 119) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 119) = 2028 / 5 - 169 / 2 * Real.log 119 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (1312003486508987542673696035331876123389647773718585529387052690134805369717943241042162693965635203610226554476685953903764339267254024976957310172349514755012594376896047324586847382649451820580368992883874258534299807492816013219405718118314151577638578856468785777122173201476300759035575585134645898976255627419333102240455082680891794435837042075094792758507865226028359200389167715017193890552751685834492853 / 125691869452028552035881224893568752659360458342343457293848630444210597538024097800355364877848164083822599922919585711494518737951757416487649376082086435600893608546298072352053037828496556192636976334496895588944705351357276543157345095806084403648265840489520814869269829912953461435384842524852413293660516691390245833049111394522246391824521998336603404252277630151661514803545745226597574157687337500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 119) / 2 ∧ (2 * (12 / 5) - Real.log 119) / 2 ≤ (11808032549952013008105312075523529988918650286772617587042096470811114083672704863362592488842254276911624489636705312820338168958425302564568572192523173583951971774425139921037115361647616451349403003445878141936249693248032307839423263268257931803533544874711545352087628076376586902905691425237753934835618716935508041936786139317294509478558982056510977267018868674575472800513669490989205352282667059942779123 / 1131226825068256968322931024042118773934244125081091115644637673997895377842216880203198283900633476754403399306276271403450668641565816748388844384738777920408042476916682651168477340456469005733732787010472060300502348162215488888416105862254759632834392564405687333823428469216581152918463582723671719642944650222512212497442002550700217526420697985029430638270498671364953633231911707039378167419186037500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (1001822437457621885958477096586143407845912817969631657102638343177747373087047580608963682140038347025385780760446411555754547142176336136645210974152369402257008529937346472135335064027744257322415761750134775906969861001457073165666077122076877060275396628511225042328921437755213655793973670757495662788629530196423226646641745817471502394635452465344882188861027651346594136623149243088125623607106382907212979733755360069609049271815581205987443847506872811708684187607301017612336882844277484472029523226152807341946190923243676275596458267619917302625397253200972568154393545784381583720514614260900186912249353991262858501792536251522551628813431883232050682466716393325595629909278306255177767102754278989325792981764309664538935924334589001170563556648406195051467306884391819901423057248391601899675050434581597344512881349200513797431414105074467400752488922673813433608941546373740827637772162583486757016644774831235559 / 231080208457451788027576457867497909468943613389401498804338009609225986177884802938041709814040450351002799901167164662605753664223617276900112348475790836322070432913602970589681614603324727234369501368300956708078082085256855423873619803092721028347174169147924840867361390798209681400150937084010121914677671380759614911303294636882326148289163247480764147228115335093173720570250472479167661616780425389759676016149099847256312382415491965131394464294387399551921306768325646090027831573235714301915088147732861033525851598285251132082033453311815557387922411719740211494419992457118206127994698621473917575176500223353529468911678183804163056273386574068968488376073879893513990722277103247125046722368247171535881006245783405727172356247602168836026894389137127930959961656117110154276244612195444493293762207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 119) / 2 * Real.cos (169 / 2 * Real.log 119) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 119) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 119)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 119) / 2 * Real.cos (169 / 2 * Real.log 119) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 119) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 119)) / (2 * (169 / 2)) ≤ (27848835579820371649164667294187341706163270611087651303078730861047800095899176476771761498141273636222966455884141195392073030195629480208453318377869601898016155098978338854825322594459469342991115014995274214280317670878308582137427743606045404828681999942837410460077174779103456469832250106484790446898559172567925604494041595674012642779042416861315965844708183532641096353417969770409284354505897879806392208360746754812377749492262913445687921049183270646258442473161560856994428295494612840691936600495991589657877654718873193287218978328831923745668414457308359145665385294385823249118913775236204574758701805758133396625791199528794087419102234426237976121789636964672926092966529349305169115258781594309105697006908188006130099911050535745700689755521795131070454599857869610720092421801551533817533938054678954444918432946025648599051495704615082027142154875003357696017037659345645309773898364043877247944458139972453535760410232156159975471 / 6418894679373660778543790496319386374137322594150041633453833600256277393830133414945603050390012509750077775032421240627937601783989368802780898568771967675613067580933415849713378183425686867621375038008359908557724502368245983996489438974797806342977060254109023357426705299950268927781970474555836719852157538354433747536202628802286837452476756874465670756336537085921492238062513124421323933799456260826657667115252773534897566178208110142538735119288538876442258521342379058056328654812103175053196892992579473153495877730145864780056484814217098816331178103326116985956110901586616836888741628374275488199347228426486929691991060661226751563149627057471346899335385552597610853396586201309029075621340199209330027951271761270199232117988949134334080399698253553637776712669919726507673461449873458147048950195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_120 : (10954451150103 / 1000000000000 : ℝ) ≤ Real.sqrt 120 ∧ Real.sqrt 120 ≤ (1369306393763 / 125000000000 : ℝ) := by
  constructor
  · calc (10954451150103 / 1000000000000 : ℝ) = Real.sqrt ((10954451150103 / 1000000000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 120 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 120 ≤ Real.sqrt ((1369306393763 / 125000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (1369306393763 / 125000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_120 : (0 : ℝ) ≤ primeTerm 120 ∧ primeTerm 120 ≤ (0 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_120
  have hl := PsiOmega.Num.log_bound_120
  have hc := PsiOmega.Num.theta_120_cos
  have hs := PsiOmega.Num.theta_120_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_120
  have hqpos : (0 : ℝ) < Real.sqrt 120 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 120)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 120) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 120) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 120) = 2028 / 5 - 169 / 2 * Real.log 120 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (10731678151078662530323362078302504714940727465664450524934155309824683792578711865259136357528029399751533459489053095736606714235451771704753134882285852842943750003262729733498360842650901298209109834179136752996798305700870177810011841721498797279165049504101899405940056457852488757790121988853763208950692434594671964106784534494881704764856233457708287232387028160138919508409094457175948369403303359817271960234907 / 1715935220717668178081135575867784232236623569092547149155580701085297096530704403218529612527828030371055344517104427646880538754499618157538653782673181369822115871491769033606367556138570876920828397323468524331730412935596079427784079502991903985769429744829858513409267307115417706285497603977040633239576587369007633502873991779994751439230636535009444409976349772342440715515307426628146727997240758875662500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 120) / 2 ∧ (2 * (12 / 5) - Real.log 120) / 2 ≤ (96585119370976073100369813256784566810632374554214514069164920487374079260541104819151890046900140795620539651363064699899278108197641724405013774469186791540117421549954813154053444587541514770704362063645671230472422512507018963382025541860791012849019585943488430753754114001208906998689499513053945605342622691577289751565723719249689250480167296589080166961321055177013742590931335028723861249855637096256965222087037 / 15443416986459013602730220182810058090129612121832924342400226309767673868776339628966766512750452273339498100653939848821924848790496563417847884044058632328399042843425921302457308005247137892287455575911216718985573716420364714850056715526927135871924867703468726620683405764038759356569478435793365699156189286321068701525865926019952762953075728815084999689787147951081966439637766839653320551975166829880962500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (3865283956994557278529759491839215879560388537841725566450708648621051514946419121680574796965863126369008335433495760418382453770792218690574031039569686758870844223126983580170404454104804563057473988604228974090314239589745681654287526648074897636906092832970726205831032515675796257313825702358566637818295889894059713220755670214294198193743370291369084228142279518861157435218013766945696097011230774012025926603660935462531894928414615866562696919828555146469255200112955170034162112627430269375892115248235540272925523288856748234253203245176594600927511315310182627094606390562791127048450007381195468430725665336554738888951411471947486129746889205677580210559594834531950792574627142352862777918471071987734411164017323193730899292349793871048365238372829531435864663395414586451662372223583474073048426908566710237468872466218539975373498863405781508779924422487564751019590013061727083115569074378403196373658744167 / 8411630660741667815730013444612334079247658407009374212140518057910314193674194420745428604466270227728249541017113890806596769187382941673953863828755031617063002399389372238357803372624893953808122164280971453695959057696472730957423433645113869752985932344854984680502136832430618005754186251729360164170093841445618896123148468218012197690724288795946732643867325755716619690839500378189343005043526751075713640819654327410864746729916432706539927883768692471206117168247681318253239625059205784775567977687330089230316410290063355122318491863635052102444397077837324596727581981709575592329364880211236360980489353816911530182340032461245616491727884411593172604471226295080828337362500569621256013417918173824262559151142066665661538054575227198089689738857445885883893575855261999117413321385465286214008026642204262316226959228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 120) / 2 * Real.cos (169 / 2 * Real.log 120) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 120) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 120)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 120) / 2 * Real.cos (169 / 2 * Real.log 120) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 120) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 120)) / (2 * (169 / 2)) ≤ (270100375370984455005444367896946152134702479548439721333634890587782644662342832150622227374034176094671256280766692121478349034580405805471849540941642023625650519716467104034145293818149301076084738319353424345683546792375664976323868999143856541658834150136387295658091575442575814687700409384420169047808843246322010325398594011807474139940121792371299694510855754453290519985734645025513597278010212603641654873002515410827303793357709993612086473556477983773353362386144509404025397655083594973658840019142031676450320476131623858869916218689462392942683246262458115208025286498002065825737681628911882119374176765345630457400118555526742592193797028801538749511225067776969333095107595204359985834708258859470366674333810727309769318339955660344956734253795242432664647498804684837191730807103840094833458557928028344990292343200908084200988426627217217362562031857453035473992592796993668803143455678880252237492348466714339003348967345649 / 584141018107060264981250933653634311058865167153428764731980420688216263449596834773988097532379876925572884792855131306013664526901593171802351654774654973407152944402039738774847456432284302347786261408400795395552712340032828538709960669799574288401800857281596158368203946696570694844040711925650011400700961211501312230774199181806402617411408944162967544713008733035876367419409748485371042016911579935813447279142661625754496300688641160176383880817270310500424803350533424878697196184667068387192220672731256196549750714587732994605450823863545284891972019294258652550526526507609416133983672236891413956978427348396634040440280032030945589703325306360636986421612937158390856761284761779253889820688762071129344385495976851782051253789946333200672898531767075408603720545504305494264813985101755987083890739041962660849094390869140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem sqrt_bounds_121 : (11 : ℝ) ≤ Real.sqrt 121 ∧ Real.sqrt 121 ≤ (11000000000001 / 1000000000000 : ℝ) := by
  constructor
  · calc (11 : ℝ) = Real.sqrt ((11 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 121 := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt 121 ≤ Real.sqrt ((11000000000001 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = (11000000000001 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)

theorem primeTerm_bounds_121 : (-973338007 / 100000000000000 : ℝ) ≤ primeTerm 121 ∧ primeTerm 121 ≤ (-928914643 / 100000000000000 : ℝ) := by
  unfold primeTerm
  push_cast
  have hf := fDH_bounds_121
  have hl := PsiOmega.Num.log_bound_121
  have hc := PsiOmega.Num.theta_121_cos
  have hs := PsiOmega.Num.theta_121_sin
  have hc2 := PsiOmega.Num.twoOmegaA_cos
  have hs2 := PsiOmega.Num.twoOmegaA_sin
  have hq := sqrt_bounds_121
  have hqpos : (0 : ℝ) < Real.sqrt 121 := Real.sqrt_pos.2 (by norm_num)
  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)
  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log 121)) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 121) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 121) := by
    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log 121) = 2028 / 5 - 169 / 2 * Real.log 121 by ring, Real.sin_sub]
  rw [hsin, div_eq_mul_inv (fDH _)]
  have p1 := PsiOmega.Num.mul_bounds hs2 hc
  norm_num at p1
  have p2 := PsiOmega.Num.mul_bounds hc2 hs
  norm_num at p2
  have hlin : (50553084722510620879906898930487728104510556788126293365808997201543353066912588072367240557995782739739210410949607955563722078644500478067946203569478919263737048360588578597449215193342078780340958850033221709150281239592334947406103680880649295361302391102204177098623754814958744609082385113148950978716042267146650699091704956733213946234544987556304004866087661014208695564683576892594731296803194530737894592427400665547 / 24018839286635195393722434927056403014201015377467879663795373130636168899927562028843835840480135939507484977040404085180190925707422249652128614634697292360893833175639338375054835600768324759687710828931594462172407421404677769308075636308798738870791294011280585968475000725961508767503084707118309781624271312806019099116782260294303913160411058742161933326976565441708533106680541525683443016222665464418022232662500000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 121) / 2 ∧ (2 * (12 / 5) - Real.log 121) / 2 ≤ (454977986886556251655253406983401779122214974583597942815536415945629387441400411966051361705279103717732709451172145088489685420119667789108897244297388523695561676874709635699815600381021259740166022987792270946659471825039750795893706097974837324676195934280882522301265921585259172659172508391335973449050724651853538144401673169255413117738492720300321112408840388386299859102408089886413455626486870854643082142432964235277 / 216169553579716758543501914343507627127809138397210916974158358175725520099348058259594522564321223455567364793363636766621718331366800246869157531712275631248044498580754045375493520406914922837189397460384350159551666792642099923772680726779188649837121646101525273716275006533653578907527762364064788034618441815254171892051040342648735218443699528679457399942789088975376797960124873731150987146003989179762200093962500000000000 : ℝ) := by
    constructor <;> linarith [hl.1, hl.2]
  have p3 := PsiOmega.Num.mul_bounds hlin hc
  norm_num at p3
  have hbr : (-3014175627693024720844865417408668042501888399141882573315547635482326583572719130336174873954342791179403090218768850819594555544494346551981131601302841983131195302295676530794724121788659254993833928243975107191382380433172231293086476544344524638709855939161436464127671147225119751647334037025598910713409857814990067286792704578761413827689203364479895550233479848385766851107767266846407059725071625992717531902127980089295141252498627601686127650236480008920651059721301984343402439360220810196043190395287825258702707824743051862531633426337083984149888130423479775065747848571245620979073314994474523575656022446155842205736584132012742639989444271757633174816164361279127188013671150880679042919636784474196204113806131101490919980828950341049919202018469037538317532412672551327927287501157179790662195631619985554151595703925443402032088315689909886699327555293598322706355076820816663279023701907043155356388498503775120962321230036878803231 / 67506003685012415718014688731892514868072417919561692746826715518649276233881598442303744409817221543751270864598418648533307617204923505665118096939606488446480185301116726145767165421674335923182433861957362299489547172706064596652968039497128645063482299544177745038530056796746577211394238204430813873911966721115936661861377408990907914603927561762980634871537841560197690037676464218818576136280450178649714148265999846552885531173505591693278070548719064097994540438038733900807016479549722578434012737503261200375475101033524203345752440847208715583153159547459452887260525385019823402795691554672703210459468967173611334146467460356540509401762373111815619847991174785863909283197660534602567314691267538464704591692512123522740956033311065653335826216034583308421253957179183393942217859735667809071679916975163309581065997352600097656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 121) / 2 * Real.cos (169 / 2 * Real.log 121) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 121) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 121)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 121) / 2 * Real.cos (169 / 2 * Real.log 121) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 121) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 121)) / (2 * (169 / 2)) ≤ (-79905777342468854467233537064016579136127950501525311448530034564496438839463083744057846676853237152373355779662882398260446579261858385648766950131086262813552531082628778035169676067996141420952654848114926398024866398530097137250444505836580039484292944434197301529149188744362973101907984762975314715250232960211633947876287661648360954445747634930183410519444600062150904042326695775740315695800697948644953078910205770127004444948061814283266640715532948458504504286100997149414346504395927715870228271760645212574975604681423512750187857691553391446655138678947634297094728777597060747065775080322433863567398317756754377710758282246138728607709607744028211468118667512444491164497401842632639472448259686170108346177641113215845565784486511335273072571460546667482334033343198312490058031769092428722685608352132692423243792589179002565494569173260775746069039114799382086639478097644253919343832851368043303985567793247875191981516514076069775121011403617255943492257 / 1875166769028122658833741353663680968557567164432269242967408764406924339830044401175104011383811709548646412905511629125925211589025652935142169359433513567957782925031020170715754595046509331199512051721037841652487421464057349907026889986031351251763397209560492917736946022131849366983173283456411496497554631142109351718371594694191886516775765604527239857542717821116602501046568450522738226007790282740269837451833329070913486977041821991479946404131085113833181678834409275022417124431936738289833687152868366677096530584264561204048678912422464321754254431873873691312792371806106205633213654296463978068318582421489203726290762787681680816715621475328211662444199299607330813422157237072293536519201876068464016435903114542298359889814196268148217394889849536345034832143866205387283829437101883585324442138198980821696277704238891601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem partial_2 : (-1239253117129 / 10000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 2, primeTerm n := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  exact primeTerm_bounds_2.1

theorem partial_3 : (-4365321811651 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 3, primeTerm n := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_2
  have h2 := primeTerm_bounds_3
  linarith [h1, h2.1]

theorem partial_4 : (11798257640347 / 20000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 4, primeTerm n := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_3
  have h2 := primeTerm_bounds_4
  linarith [h1, h2.1]

theorem partial_5 : (11798257640347 / 20000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 5, primeTerm n := by
  rw [show (5 : ℕ) = 4 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_4
  have h2 := primeTerm_bounds_5
  linarith [h1, h2.1]

theorem partial_6 : (78380377156049 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 6, primeTerm n := by
  rw [show (6 : ℕ) = 5 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_5
  have h2 := primeTerm_bounds_6
  linarith [h1, h2.1]

theorem partial_7 : (85623457593461 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 7, primeTerm n := by
  rw [show (7 : ℕ) = 6 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_6
  have h2 := primeTerm_bounds_7
  linarith [h1, h2.1]

theorem partial_8 : (171991567015873 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 8, primeTerm n := by
  rw [show (8 : ℕ) = 7 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_7
  have h2 := primeTerm_bounds_8
  linarith [h1, h2.1]

theorem partial_9 : (8323942643883 / 3125000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 9, primeTerm n := by
  rw [show (9 : ℕ) = 8 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_8
  have h2 := primeTerm_bounds_9
  linarith [h1, h2.1]

theorem partial_10 : (8323942643883 / 3125000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 10, primeTerm n := by
  rw [show (10 : ℕ) = 9 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_9
  have h2 := primeTerm_bounds_10
  linarith [h1, h2.1]

theorem partial_11 : (66920838022881 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 11, primeTerm n := by
  rw [show (11 : ℕ) = 10 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_10
  have h2 := primeTerm_bounds_11
  linarith [h1, h2.1]

theorem partial_12 : (289806791066151 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 12, primeTerm n := by
  rw [show (12 : ℕ) = 11 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_11
  have h2 := primeTerm_bounds_12
  linarith [h1, h2.1]

theorem partial_13 : (62467199911459 / 20000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 13, primeTerm n := by
  rw [show (13 : ℕ) = 12 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_12
  have h2 := primeTerm_bounds_13
  linarith [h1, h2.1]

theorem partial_14 : (98601451673289 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 14, primeTerm n := by
  rw [show (14 : ℕ) = 13 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_13
  have h2 := primeTerm_bounds_14
  linarith [h1, h2.1]

theorem partial_15 : (98601451673289 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 15, primeTerm n := by
  rw [show (15 : ℕ) = 14 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_14
  have h2 := primeTerm_bounds_15
  linarith [h1, h2.1]

theorem partial_16 : (386450567743249 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 16, primeTerm n := by
  rw [show (16 : ℕ) = 15 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_15
  have h2 := primeTerm_bounds_16
  linarith [h1, h2.1]

theorem partial_17 : (401819294139891 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 17, primeTerm n := by
  rw [show (17 : ℕ) = 16 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_16
  have h2 := primeTerm_bounds_17
  linarith [h1, h2.1]

theorem partial_18 : (51938383782887 / 12500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 18, primeTerm n := by
  rw [show (18 : ℕ) = 17 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_17
  have h2 := primeTerm_bounds_18
  linarith [h1, h2.1]

theorem partial_19 : (466649870397759 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 19, primeTerm n := by
  rw [show (19 : ℕ) = 18 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_18
  have h2 := primeTerm_bounds_19
  linarith [h1, h2.1]

theorem partial_20 : (466649870397759 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 20, primeTerm n := by
  rw [show (20 : ℕ) = 19 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_19
  have h2 := primeTerm_bounds_20
  linarith [h1, h2.1]

theorem partial_21 : (105122457831129 / 20000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 21, primeTerm n := by
  rw [show (21 : ℕ) = 20 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_20
  have h2 := primeTerm_bounds_21
  linarith [h1, h2.1]

theorem partial_22 : (131403072288069 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 22, primeTerm n := by
  rw [show (22 : ℕ) = 21 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_21
  have h2 := primeTerm_bounds_22
  linarith [h1, h2.1]

theorem partial_23 : (32370104015757 / 6250000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 23, primeTerm n := by
  rw [show (23 : ℕ) = 22 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_22
  have h2 := primeTerm_bounds_23
  linarith [h1, h2.1]

theorem partial_24 : (517612643314159 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 24, primeTerm n := by
  rw [show (24 : ℕ) = 23 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_23
  have h2 := primeTerm_bounds_24
  linarith [h1, h2.1]

theorem partial_25 : (517612643314159 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 25, primeTerm n := by
  rw [show (25 : ℕ) = 24 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_24
  have h2 := primeTerm_bounds_25
  linarith [h1, h2.1]

theorem partial_26 : (269450923863827 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 26, primeTerm n := by
  rw [show (26 : ℕ) = 25 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_25
  have h2 := primeTerm_bounds_26
  linarith [h1, h2.1]

theorem partial_27 : (539063198444039 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 27, primeTerm n := by
  rw [show (27 : ℕ) = 26 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_26
  have h2 := primeTerm_bounds_27
  linarith [h1, h2.1]

theorem partial_28 : (272228641989197 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 28, primeTerm n := by
  rw [show (28 : ℕ) = 27 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_27
  have h2 := primeTerm_bounds_28
  linarith [h1, h2.1]

theorem partial_29 : (276983241609699 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 29, primeTerm n := by
  rw [show (29 : ℕ) = 28 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_28
  have h2 := primeTerm_bounds_29
  linarith [h1, h2.1]

theorem partial_30 : (276983241609699 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 30, primeTerm n := by
  rw [show (30 : ℕ) = 29 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_29
  have h2 := primeTerm_bounds_30
  linarith [h1, h2.1]

theorem partial_31 : (28580648570247 / 5000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 31, primeTerm n := by
  rw [show (31 : ℕ) = 30 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_30
  have h2 := primeTerm_bounds_31
  linarith [h1, h2.1]

theorem partial_32 : (571601227479061 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 32, primeTerm n := by
  rw [show (32 : ℕ) = 31 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_31
  have h2 := primeTerm_bounds_32
  linarith [h1, h2.1]

theorem partial_33 : (5716012274767 / 1000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 33, primeTerm n := by
  rw [show (33 : ℕ) = 32 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_32
  have h2 := primeTerm_bounds_33
  linarith [h1, h2.1]

theorem partial_34 : (608354868041791 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 34, primeTerm n := by
  rw [show (34 : ℕ) = 33 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_33
  have h2 := primeTerm_bounds_34
  linarith [h1, h2.1]

theorem partial_35 : (608354868041791 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 35, primeTerm n := by
  rw [show (35 : ℕ) = 34 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_34
  have h2 := primeTerm_bounds_35
  linarith [h1, h2.1]

theorem partial_36 : (599665647905841 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 36, primeTerm n := by
  rw [show (36 : ℕ) = 35 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_35
  have h2 := primeTerm_bounds_36
  linarith [h1, h2.1]

theorem partial_37 : (147594798354919 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 37, primeTerm n := by
  rw [show (37 : ℕ) = 36 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_36
  have h2 := primeTerm_bounds_37
  linarith [h1, h2.1]

theorem partial_38 : (295189596708949 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 38, primeTerm n := by
  rw [show (38 : ℕ) = 37 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_37
  have h2 := primeTerm_bounds_38
  linarith [h1, h2.1]

theorem partial_39 : (594469551087797 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 39, primeTerm n := by
  rw [show (39 : ℕ) = 38 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_38
  have h2 := primeTerm_bounds_39
  linarith [h1, h2.1]

theorem partial_40 : (594469551087797 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 40, primeTerm n := by
  rw [show (40 : ℕ) = 39 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_39
  have h2 := primeTerm_bounds_40
  linarith [h1, h2.1]

theorem partial_41 : (623705640667153 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 41, primeTerm n := by
  rw [show (41 : ℕ) = 40 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_40
  have h2 := primeTerm_bounds_41
  linarith [h1, h2.1]

theorem partial_42 : (625435371611621 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 42, primeTerm n := by
  rw [show (42 : ℕ) = 41 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_41
  have h2 := primeTerm_bounds_42
  linarith [h1, h2.1]

theorem partial_43 : (126558975286483 / 20000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 43, primeTerm n := by
  rw [show (43 : ℕ) = 42 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_42
  have h2 := primeTerm_bounds_43
  linarith [h1, h2.1]

theorem partial_44 : (632794876427691 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 44, primeTerm n := by
  rw [show (44 : ℕ) = 43 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_43
  have h2 := primeTerm_bounds_44
  linarith [h1, h2.1]

theorem partial_45 : (632794876427691 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 45, primeTerm n := by
  rw [show (45 : ℕ) = 44 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_44
  have h2 := primeTerm_bounds_45
  linarith [h1, h2.1]

theorem partial_46 : (603364397110969 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 46, primeTerm n := by
  rw [show (46 : ℕ) = 45 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_45
  have h2 := primeTerm_bounds_46
  linarith [h1, h2.1]

theorem partial_47 : (604646912103317 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 47, primeTerm n := by
  rw [show (47 : ℕ) = 46 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_46
  have h2 := primeTerm_bounds_47
  linarith [h1, h2.1]

theorem partial_48 : (302026004294349 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 48, primeTerm n := by
  rw [show (48 : ℕ) = 47 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_47
  have h2 := primeTerm_bounds_48
  linarith [h1, h2.1]

theorem partial_49 : (77215260422039 / 12500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 49, primeTerm n := by
  rw [show (49 : ℕ) = 48 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_48
  have h2 := primeTerm_bounds_49
  linarith [h1, h2.1]

theorem partial_50 : (77215260422039 / 12500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 50, primeTerm n := by
  rw [show (50 : ℕ) = 49 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_49
  have h2 := primeTerm_bounds_50
  linarith [h1, h2.1]

theorem partial_51 : (31797837877467 / 5000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 51, primeTerm n := by
  rw [show (51 : ℕ) = 50 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_50
  have h2 := primeTerm_bounds_51
  linarith [h1, h2.1]

theorem partial_52 : (631309167136837 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 52, primeTerm n := by
  rw [show (52 : ℕ) = 51 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_51
  have h2 := primeTerm_bounds_52
  linarith [h1, h2.1]

theorem partial_53 : (79538303125283 / 12500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 53, primeTerm n := by
  rw [show (53 : ℕ) = 52 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_52
  have h2 := primeTerm_bounds_53
  linarith [h1, h2.1]

theorem partial_54 : (1984768535101 / 312500000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 54, primeTerm n := by
  rw [show (54 : ℕ) = 53 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_53
  have h2 := primeTerm_bounds_54
  linarith [h1, h2.1]

theorem partial_55 : (1984768535101 / 312500000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 55, primeTerm n := by
  rw [show (55 : ℕ) = 54 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_54
  have h2 := primeTerm_bounds_55
  linarith [h1, h2.1]

theorem partial_56 : (633913224532617 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 56, primeTerm n := by
  rw [show (56 : ℕ) = 55 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_55
  have h2 := primeTerm_bounds_56
  linarith [h1, h2.1]

theorem partial_57 : (633913224531867 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 57, primeTerm n := by
  rw [show (57 : ℕ) = 56 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_56
  have h2 := primeTerm_bounds_57
  linarith [h1, h2.1]

theorem partial_58 : (633913224531017 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 58, primeTerm n := by
  rw [show (58 : ℕ) = 57 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_57
  have h2 := primeTerm_bounds_58
  linarith [h1, h2.1]

theorem partial_59 : (624236429160529 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 59, primeTerm n := by
  rw [show (59 : ℕ) = 58 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_58
  have h2 := primeTerm_bounds_59
  linarith [h1, h2.1]

theorem partial_60 : (624236429160529 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 60, primeTerm n := by
  rw [show (60 : ℕ) = 59 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_59
  have h2 := primeTerm_bounds_60
  linarith [h1, h2.1]

theorem partial_61 : (310268160310539 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 61, primeTerm n := by
  rw [show (61 : ℕ) = 60 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_60
  have h2 := primeTerm_bounds_61
  linarith [h1, h2.1]

theorem partial_62 : (620536320619739 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 62, primeTerm n := by
  rw [show (62 : ℕ) = 61 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_61
  have h2 := primeTerm_bounds_62
  linarith [h1, h2.1]

theorem partial_63 : (619446220179247 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 63, primeTerm n := by
  rw [show (63 : ℕ) = 62 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_62
  have h2 := primeTerm_bounds_63
  linarith [h1, h2.1]

theorem partial_64 : (614472953243549 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 64, primeTerm n := by
  rw [show (64 : ℕ) = 63 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_63
  have h2 := primeTerm_bounds_64
  linarith [h1, h2.1]

theorem partial_65 : (614472953243549 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 65, primeTerm n := by
  rw [show (65 : ℕ) = 64 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_64
  have h2 := primeTerm_bounds_65
  linarith [h1, h2.1]

theorem partial_66 : (614472953240703 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 66, primeTerm n := by
  rw [show (66 : ℕ) = 65 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_65
  have h2 := primeTerm_bounds_66
  linarith [h1, h2.1]

theorem partial_67 : (305161012362747 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 67, primeTerm n := by
  rw [show (67 : ℕ) = 66 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_66
  have h2 := primeTerm_bounds_67
  linarith [h1, h2.1]

theorem partial_68 : (305066384082171 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 68, primeTerm n := by
  rw [show (68 : ℕ) = 67 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_67
  have h2 := primeTerm_bounds_68
  linarith [h1, h2.1]

theorem partial_69 : (595750522539063 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 69, primeTerm n := by
  rw [show (69 : ℕ) = 68 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_68
  have h2 := primeTerm_bounds_69
  linarith [h1, h2.1]

theorem partial_70 : (595750522539063 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 70, primeTerm n := by
  rw [show (70 : ℕ) = 69 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_69
  have h2 := primeTerm_bounds_70
  linarith [h1, h2.1]

theorem partial_71 : (589720104025299 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 71, primeTerm n := by
  rw [show (71 : ℕ) = 70 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_70
  have h2 := primeTerm_bounds_71
  linarith [h1, h2.1]

theorem partial_72 : (585063950289163 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 72, primeTerm n := by
  rw [show (72 : ℕ) = 71 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_71
  have h2 := primeTerm_bounds_72
  linarith [h1, h2.1]

theorem partial_73 : (586240278426921 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 73, primeTerm n := by
  rw [show (73 : ℕ) = 72 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_72
  have h2 := primeTerm_bounds_73
  linarith [h1, h2.1]

theorem partial_74 : (576539179441453 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 74, primeTerm n := by
  rw [show (74 : ℕ) = 73 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_73
  have h2 := primeTerm_bounds_74
  linarith [h1, h2.1]

theorem partial_75 : (576539179441453 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 75, primeTerm n := by
  rw [show (75 : ℕ) = 74 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_74
  have h2 := primeTerm_bounds_75
  linarith [h1, h2.1]

theorem partial_76 : (288269589720623 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 76, primeTerm n := by
  rw [show (76 : ℕ) = 75 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_75
  have h2 := primeTerm_bounds_76
  linarith [h1, h2.1]

theorem partial_77 : (576539179440253 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 77, primeTerm n := by
  rw [show (77 : ℕ) = 76 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_76
  have h2 := primeTerm_bounds_77
  linarith [h1, h2.1]

theorem partial_78 : (285432101780293 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 78, primeTerm n := by
  rw [show (78 : ℕ) = 77 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_77
  have h2 := primeTerm_bounds_78
  linarith [h1, h2.1]

theorem partial_79 : (285143240439523 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 79, primeTerm n := by
  rw [show (79 : ℕ) = 78 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_78
  have h2 := primeTerm_bounds_79
  linarith [h1, h2.1]

theorem partial_80 : (285143240439523 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 80, primeTerm n := by
  rw [show (80 : ℕ) = 79 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_79
  have h2 := primeTerm_bounds_80
  linarith [h1, h2.1]

theorem partial_81 : (574334363454089 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 81, primeTerm n := by
  rw [show (81 : ℕ) = 80 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_80
  have h2 := primeTerm_bounds_81
  linarith [h1, h2.1]

theorem partial_82 : (574334363454027 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 82, primeTerm n := by
  rw [show (82 : ℕ) = 81 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_81
  have h2 := primeTerm_bounds_82
  linarith [h1, h2.1]

theorem partial_83 : (576632077360779 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 83, primeTerm n := by
  rw [show (83 : ℕ) = 82 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_82
  have h2 := primeTerm_bounds_83
  linarith [h1, h2.1]

theorem partial_84 : (566363520071863 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 84, primeTerm n := by
  rw [show (84 : ℕ) = 83 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_83
  have h2 := primeTerm_bounds_84
  linarith [h1, h2.1]

theorem partial_85 : (566363520071863 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 85, primeTerm n := by
  rw [show (85 : ℕ) = 84 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_84
  have h2 := primeTerm_bounds_85
  linarith [h1, h2.1]

theorem partial_86 : (143381664066711 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 86, primeTerm n := by
  rw [show (86 : ℕ) = 85 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_85
  have h2 := primeTerm_bounds_86
  linarith [h1, h2.1]

theorem partial_87 : (573526656266337 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 87, primeTerm n := by
  rw [show (87 : ℕ) = 86 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_86
  have h2 := primeTerm_bounds_87
  linarith [h1, h2.1]

theorem partial_88 : (17922708008313 / 3125000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 88, primeTerm n := by
  rw [show (88 : ℕ) = 87 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_87
  have h2 := primeTerm_bounds_88
  linarith [h1, h2.1]

theorem partial_89 : (578194066871867 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 89, primeTerm n := by
  rw [show (89 : ℕ) = 88 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_88
  have h2 := primeTerm_bounds_89
  linarith [h1, h2.1]

theorem partial_90 : (578194066871867 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 90, primeTerm n := by
  rw [show (90 : ℕ) = 89 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_89
  have h2 := primeTerm_bounds_90
  linarith [h1, h2.1]

theorem partial_91 : (287113270812219 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 91, primeTerm n := by
  rw [show (91 : ℕ) = 90 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_90
  have h2 := primeTerm_bounds_91
  linarith [h1, h2.1]

theorem partial_92 : (114710176127047 / 20000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 92, primeTerm n := by
  rw [show (92 : ℕ) = 91 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_91
  have h2 := primeTerm_bounds_92
  linarith [h1, h2.1]

theorem partial_93 : (143387720158643 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 93, primeTerm n := by
  rw [show (93 : ℕ) = 92 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_92
  have h2 := primeTerm_bounds_93
  linarith [h1, h2.1]

theorem partial_94 : (568225616202993 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 94, primeTerm n := by
  rw [show (94 : ℕ) = 93 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_93
  have h2 := primeTerm_bounds_94
  linarith [h1, h2.1]

theorem partial_95 : (568225616202993 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 95, primeTerm n := by
  rw [show (95 : ℕ) = 94 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_94
  have h2 := primeTerm_bounds_95
  linarith [h1, h2.1]

theorem partial_96 : (284099240746601 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 96, primeTerm n := by
  rw [show (96 : ℕ) = 95 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_95
  have h2 := primeTerm_bounds_96
  linarith [h1, h2.1]

theorem partial_97 : (566742625467277 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 97, primeTerm n := by
  rw [show (97 : ℕ) = 96 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_96
  have h2 := primeTerm_bounds_97
  linarith [h1, h2.1]

theorem partial_98 : (282940793482329 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 98, primeTerm n := by
  rw [show (98 : ℕ) = 97 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_97
  have h2 := primeTerm_bounds_98
  linarith [h1, h2.1]

theorem partial_99 : (565881586964197 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 99, primeTerm n := by
  rw [show (99 : ℕ) = 98 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_98
  have h2 := primeTerm_bounds_99
  linarith [h1, h2.1]

theorem partial_100 : (565881586964197 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 100, primeTerm n := by
  rw [show (100 : ℕ) = 99 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_99
  have h2 := primeTerm_bounds_100
  linarith [h1, h2.1]

theorem partial_101 : (8902816306469 / 1562500000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 101, primeTerm n := by
  rw [show (101 : ℕ) = 100 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_100
  have h2 := primeTerm_bounds_101
  linarith [h1, h2.1]

theorem partial_102 : (284439173517783 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 102, primeTerm n := by
  rw [show (102 : ℕ) = 101 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_101
  have h2 := primeTerm_bounds_102
  linarith [h1, h2.1]

theorem partial_103 : (142330636086513 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 103, primeTerm n := by
  rw [show (103 : ℕ) = 102 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_102
  have h2 := primeTerm_bounds_103
  linarith [h1, h2.1]

theorem partial_104 : (569035878741549 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 104, primeTerm n := by
  rw [show (104 : ℕ) = 103 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_103
  have h2 := primeTerm_bounds_104
  linarith [h1, h2.1]

theorem partial_105 : (569035878741549 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 105, primeTerm n := by
  rw [show (105 : ℕ) = 104 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_104
  have h2 := primeTerm_bounds_105
  linarith [h1, h2.1]

theorem partial_106 : (113618688622007 / 20000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 106, primeTerm n := by
  rw [show (106 : ℕ) = 105 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_105
  have h2 := primeTerm_bounds_106
  linarith [h1, h2.1]

theorem partial_107 : (568469828169171 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 107, primeTerm n := by
  rw [show (107 : ℕ) = 106 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_106
  have h2 := primeTerm_bounds_107
  linarith [h1, h2.1]

theorem partial_108 : (141897617929761 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 108, primeTerm n := by
  rw [show (108 : ℕ) = 107 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_107
  have h2 := primeTerm_bounds_108
  linarith [h1, h2.1]

theorem partial_109 : (282740924923161 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 109, primeTerm n := by
  rw [show (109 : ℕ) = 108 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_108
  have h2 := primeTerm_bounds_109
  linarith [h1, h2.1]

theorem partial_110 : (282740924923161 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 110, primeTerm n := by
  rw [show (110 : ℕ) = 109 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_109
  have h2 := primeTerm_bounds_110
  linarith [h1, h2.1]

theorem partial_111 : (564630563116249 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 111, primeTerm n := by
  rw [show (111 : ℕ) = 110 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_110
  have h2 := primeTerm_bounds_111
  linarith [h1, h2.1]

theorem partial_112 : (8821732423933 / 1562500000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 112, primeTerm n := by
  rw [show (112 : ℕ) = 111 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_111
  have h2 := primeTerm_bounds_112
  linarith [h1, h2.1]

theorem partial_113 : (113001645031519 / 20000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 113, primeTerm n := by
  rw [show (113 : ℕ) = 112 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_112
  have h2 := primeTerm_bounds_113
  linarith [h1, h2.1]

theorem partial_114 : (141252056289353 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 114, primeTerm n := by
  rw [show (114 : ℕ) = 113 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_113
  have h2 := primeTerm_bounds_114
  linarith [h1, h2.1]

theorem partial_115 : (141252056289353 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 115, primeTerm n := by
  rw [show (115 : ℕ) = 114 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_114
  have h2 := primeTerm_bounds_115
  linarith [h1, h2.1]

theorem partial_116 : (282504112578613 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 116, primeTerm n := by
  rw [show (116 : ℕ) = 115 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_115
  have h2 := primeTerm_bounds_116
  linarith [h1, h2.1]

theorem partial_117 : (141191720204773 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 117, primeTerm n := by
  rw [show (117 : ℕ) = 116 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_116
  have h2 := primeTerm_bounds_117
  linarith [h1, h2.1]

theorem partial_118 : (564766880819033 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 118, primeTerm n := by
  rw [show (118 : ℕ) = 117 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_117
  have h2 := primeTerm_bounds_118
  linarith [h1, h2.1]

theorem partial_119 : (70570183527481 / 12500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 119, primeTerm n := by
  rw [show (119 : ℕ) = 118 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_118
  have h2 := primeTerm_bounds_119
  linarith [h1, h2.1]

theorem partial_120 : (70570183527481 / 12500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 120, primeTerm n := by
  rw [show (120 : ℕ) = 119 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_119
  have h2 := primeTerm_bounds_120
  linarith [h1, h2.1]

theorem partial_121 : (564560494881841 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 121, primeTerm n := by
  rw [show (121 : ℕ) = 120 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := partial_120
  have h2 := primeTerm_bounds_121
  linarith [h1, h2.1]

end PsiOmega

#print axioms PsiOmega.partial_121
