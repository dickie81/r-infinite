import Mathlib
import DHPacket
import DHNumerics
import DHLogBounds
import DHTrigBounds
import DHCoeffs
import DHTerms

/-! # Generated (gen_oddterms.py): lower bounds for the prime terms of the sine packet and their partial sums

The prime term of `QDHu_sinPacket_eq` at `(a, ω) = (12/5, 169/2)`, from the autocorrelation
`f(u) = ½(2a − u)cos(ωu) − sin(ω(2a − u))/(2ω)` of `1_{[−a,a]}·sin(ω·)`. The atoms are those of `DHTerms`
(whose `sqrt_bounds_n` are reused); only the sign of the sidelobe term differs from `primeTerm`. -/

open Real Finset

namespace PsiOmega

/-- The prime term of `QDHu_sinPacket_eq` at `(a, ω) = (12/5, 169/2)`. -/
noncomputable def oddTerm (n : ℕ) : ℝ := fDH n / Real.sqrt n * ((2 * (12 / 5) - Real.log n) / 2 * Real.cos (169 / 2 * Real.log n)
    - Real.sin (169 / 2 * (2 * (12 / 5) - Real.log n)) / (2 * (169 / 2)))

theorem oddTerm_bounds_2 : (-12556182038667 / 100000000000000 : ℝ) ≤ oddTerm 2 ∧ oddTerm 2 ≤ (-31389020199 / 250000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-546665495109976492930043164376255998867210717412726298431545765509965927228672326429616698154275729199723540516057315765806696779840258745752571439644352058599923 / 606196912340301476973536409786902368068695068359375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 2) / 2 * Real.cos (169 / 2 * Real.log 2) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 2) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 2)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 2) / 2 * Real.cos (169 / 2 * Real.log 2) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 2) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 2)) / (2 * (169 / 2)) ≤ (-571421542786676907312651168075486270604571110197478285370321653355567281747452995408397270247518433861466653741588088149481657213617683116689 / 633677839033061810596336727030575275421142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_3 : (-329912195097 / 6250000000000 : ℝ) ≤ oddTerm 3 ∧ oddTerm 3 ≤ (-5277566987723 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (19012293759838426492959246234217983364465430449607116661676760508188518083673415771854218173825430792134854060002163259199203 / 64911819721754310252848085838195402175188064575195312500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 3) / 2 * Real.cos (169 / 2 * Real.log 3) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 3) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 3)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 3) / 2 * Real.cos (169 / 2 * Real.log 3) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 3) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 3)) / (2 * (169 / 2)) ≤ (318666521942214535130497907055507406902414106047429682623921508079234063975430829061859438535433751199998419620050981259044048300148350368475984343 / 1087780103930960902284055813460383888013893738389015197753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_4 : (3039728802969 / 4000000000000 : ℝ) ≤ oddTerm 4 ∧ oddTerm 4 ≤ (75997994476189 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-137321153172125704673459252225259080291871182369396488779872479523056789627573500105838098428165990183837751383826390552047875348596991772576651758025973762111436634599232830385527 / 130298804535854832909302946636644299804687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 4) / 2 * Real.cos (169 / 2 * Real.log 4) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 4) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 4)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 4) / 2 * Real.cos (169 / 2 * Real.log 4) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 4) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 4)) / (2 * (169 / 2)) ≤ (-5492501052427675701909180417483884280212180125197049747598763335692877575301877155875808137872376990537444072934296644427347367048383984472029273228354864258286779463013 / 5211952181434193316372117865465771992187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_5 : (0 : ℝ) ≤ oddTerm 5 ∧ oddTerm 5 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-777593496588141275222796139311517637973883608483432899654652863719304271758484963472189544064302958517296717504681862496313522549388922877410819377451634628522130759030156998117546278054334157 / 795782533628096759969381194560402493400407105843715786933898925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 5) / 2 * Real.cos (169 / 2 * Real.log 5) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 5) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 5)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 5) / 2 * Real.cos (169 / 2 * Real.log 5) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 5) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 5)) / (2 * (169 / 2)) ≤ (-62202939843143738415879918960800724312090155727990112819613324738453508831546333496021146798995887163428848940952038264290975044090723855563146122004554788028143122928106920003814951 / 63662602690247740797550495564832199472032568467497262954711914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_6 : (97517529876947 / 100000000000000 : ℝ) ≤ oddTerm 6 ∧ oddTerm 6 ≤ (97523391224593 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (38430297166877928864251803281544159367133321859716668270373129324093454859962611057264411826857573726914822936094175356700018012017703123684811573547609523922064266659684167134885651769982557432227848092771857 / 31153055455948372511905772054173879460527857753392491571840350308906351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 6) / 2 * Real.cos (169 / 2 * Real.log 6) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 6) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 6)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 6) / 2 * Real.cos (169 / 2 * Real.log 6) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 6) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 6)) / (2 * (169 / 2)) ≤ (1847721492030271037244172864629196836471860984702184872909597841126236112393682202839621990061764031193692641214660415007675451057328579987924205458063446545045826121032677399803125952757528314325316349523273 / 1497743050766748678457008271835282666371531622759254402492324534082036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_7 : (14320896213223 / 100000000000000 : ℝ) ≤ oddTerm 7 ∧ oddTerm 7 ≤ (14322513604447 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (7894625284213912919968423464447269754925457776323598933641749864535231196354673989390034302255733112223485152813880283373206587757685432012424085330923992673546517302417838037965896240876656409212854954896151278621355269661999 / 11517926015496499277371506882584815308153369586361911721734882843974984088215535347833633422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 7) / 2 * Real.cos (169 / 2 * Real.log 7) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 7) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 7)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 7) / 2 * Real.cos (169 / 2 * Real.log 7) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 7) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 7)) / (2 * (169 / 2)) ≤ (986939611971245214836765670505612745734833265582710061551037880393812980331344979090173668032309538979086139431548172584911976873989754201450163284731606381711960741405317503785189203966385005273133894574603975950016435269182956998297091 / 1439740751937062409671438360323101913519171198295238965216860355496873011026941918479204177856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_8 : (374066185861 / 50000000000000 : ℝ) ≤ oddTerm 8 ∧ oddTerm 8 ≤ (187044097289 / 25000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (3067500704331005237605846152563586403590453963993077822871733598985012449512838789319305587421419995582683672506162655216174854388605159540833823653924158897715101859084245244378981893152800053093159 / 2303585203099299855474301376516963061630673917272382344346976568794996817643107069566726684570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 8) / 2 * Real.cos (169 / 2 * Real.log 8) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 8) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 8)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 8) / 2 * Real.cos (169 / 2 * Real.log 8) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 8) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 8)) / (2 * (169 / 2)) ≤ (7669202836625117567757569783786717061537881522390127211199361737867074755654960311275174360825144891662931535394430438175365291381531820884693905019822382220666688781293021077839078781627804837226296164106368330141194753 / 5758963007748249638685753441292407654076684793180955860867441421987492044107767673916816711425781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_9 : (11799422463129 / 12500000000000 : ℝ) ≤ oddTerm 9 ∧ oddTerm 9 ≤ (94401399869859 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-300341107386401444606340481150867222071187429448067778161375992497978375223474388917199980636025966841746588315401063523545383065951656769776917388524919283941125570379155361022368843468868717719816722701423694533777106380132328520562914414106720673 / 242420418620160171519549426905389761305778006275069270750104458623460996723011526625296178903894686080217361450195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 9) / 2 * Real.cos (169 / 2 * Real.log 9) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 9) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 9)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 9) / 2 * Real.cos (169 / 2 * Real.log 9) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 9) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 9)) / (2 * (169 / 2)) ≤ (-2402575632774938643683727283916044166532645435254134093208862178517146370087984510628416670074117181569039866453788867186799018036262529239189587433672479801022721442369983611815427254955153955057515375496073035670486673767968730673498206538276547253 / 1939363348961281372156395415243118090446224050200554166000835668987687973784092213002369431231157488641738891601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_10 : (0 : ℝ) ≤ oddTerm 10 ∧ oddTerm 10 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (777017249473452896201030244803636609731724781429706967455782962345093006333813539119478406418695621028297408601378485043580356607019341316831375985385243483676080603011866416205972042422455431110778141586003273896176856020640554725614613 / 634701529899969901883433710533400884716341721766383199293271300943897473731980281456053113795644365536966911066928754691406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 10) / 2 * Real.cos (169 / 2 * Real.log 10) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 10) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 10)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 10) / 2 * Real.cos (169 / 2 * Real.log 10) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 10) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 10)) / (2 * (169 / 2)) ≤ (7770678771215915381294797416292013003207241903552216780331403588563145570501342622534359138996978519946429569917309903641790968392359488522470585285116693153593516496085541216050406783071220110264759745928564720875456952393337575273139244156622265770748734979 / 6347015298999699018834337105334008847163417217663831992932713009438974737319802814560531137956443655369669110669287546914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_11 : (51203027601 / 10000000000000 : ℝ) ≤ oddTerm 11 ∧ oddTerm 11 ≤ (258889912753 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (2679238785566633378640426631032218890575824922104158911104746249056988340570104530914852145648656130481979729615774357970224647536468407766496762524840689957686525548514168564043420460808227586291565413227789687538163301553207603681739002848561118524997351 / 378311592280846775700708455165267517993653846839894771154684603776870652277457881841691204187658050976375884453611823732499033212661743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 11) / 2 * Real.cos (169 / 2 * Real.log 11) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 11) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 11)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 11) / 2 * Real.cos (169 / 2 * Real.log 11) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 11) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 11)) / (2 * (169 / 2)) ≤ (169332734754475810002633773159317832199186983514119933582035475184816577328768491771631292195009379112443554180919143714625040476246453739373464009942130769537168340321100239718960511419559591834746295093841867612490968333626310931582650011056507113875960140865064903 / 23644474517552923481294278447829219874603365427493423197167787736054415767341117615105700261728628186023492778350738983281189575791358947753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_12 : (4463732184999 / 20000000000000 : ℝ) ≤ oddTerm 12 ∧ oddTerm 12 ≤ (892817013971 / 4000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-2222530128375859101955982481281114404023574173175154797339776773228632573265535604476333350941868783398386520801514950932036021719803865588669558256760067722216062845377584672076466407349747646239356345128038134026967003544025864525085221604274834754912425135032546786320118769882899 / 2192852184493746904452622803170430613579563427940424894288401829483869364255858400763321829172869435171527397146146407211794745459326497056754305958747863769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 12) / 2 * Real.cos (169 / 2 * Real.log 12) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 12) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 12)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 12) / 2 * Real.cos (169 / 2 * Real.log 12) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 12) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 12)) / (2 * (169 / 2)) ≤ (-35557671027800501444329105239407424872674254909305640734117212397255608059720565627515316084819936569335713875094104582400766529245723772194296323338797696064901630637964301968297871888070344250567887701411413682015417303396540796294293177059147168452803641157 / 35085634951899950471241964850726889817273014847046798308614429271741909828093734412213149266765910962744438354338342515388715927349223952908068895339965820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_13 : (22614851418559 / 100000000000000 : ℝ) ≤ oddTerm 13 ∧ oddTerm 13 ≤ (22616446831549 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-490814532358535986749644849699234988288506932676658924871758130883804790716987227730137841061653454063019248433466088299364763211565411504873078177042540649006718870973636962935623197914417020783236338195292351815680818689951873041977984066069035571730692262745599367699845302188211 / 438570436898749380890524560634086122715912685588084978857680365896773872851171680152664365834573887034305479429229281442358949091865299411350861191749572753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 13) / 2 * Real.cos (169 / 2 * Real.log 13) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 13) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 13)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 13) / 2 * Real.cos (169 / 2 * Real.log 13) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 13) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 13)) / (2 * (169 / 2)) ≤ (-7852478549222288115047913900184462652335941713318590997375457426931996169003554485566464241858149073497932539961751830714949374777564746322869561862797012089611793454517715807052839145269553048520046462858213413116363126796296993526570960639656796162665384557 / 7017126990379990094248392970145377963454602969409359661722885854348381965618746882442629853353182192548887670867668503077743185469844790581613779067993164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_14 : (82410497041613 / 100000000000000 : ℝ) ≤ oddTerm 14 ∧ oddTerm 14 ≤ (16483294613441 / 20000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-174809694926762103854993674677584807231681803459510620958701789925791859320005286672464404093621972982205412637915798440924852801096156827900070575506360999626183467270299068668333642689851972295200895002085318259224557103786867588856566901316635996899406978197013643705651538827235308663 / 161674605858354971771482974032149508277994052415191646606095290084186720487855928171478191821257317716326371936791082310911202993225223975000381469726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 14) / 2 * Real.cos (169 / 2 * Real.log 14) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 14) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 14)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 14) / 2 * Real.cos (169 / 2 * Real.log 14) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 14) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 14)) / (2 * (169 / 2)) ≤ (-233062692654096387084106783920311814937506502352749346623728753057213240432419106095065180797248964742581692073016297241380695168229879554354288888173448652762013057994962193320083539834231646228950878113481391444046771706889281781158937278662630390655382529834843 / 215566141144473295695310632042866011037325403220255528808127053445582293983807904228637589095009756955101829249054776414548270657633631966667175292968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_15 : (0 : ℝ) ≤ oddTerm 15 ∧ oddTerm 15 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-22113791786302593672158745492471476660997684611979470504419048013239828774677215156829262284492008801972056665745137153072853848501949632065371438371975355345287689594904515500846188404634918980468919285751016996952874347635717861584051370037758182606789595894190690982975182249558346756397899997 / 24053804993884279863155405587762706414761083841313052563187010985584941644749516242670995209600211438115025166012244257487940071078153119429506674779356707474522590637207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 15) / 2 * Real.cos (169 / 2 * Real.log 15) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 15) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 15)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 15) / 2 * Real.cos (169 / 2 * Real.log 15) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 15) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 15)) / (2 * (169 / 2)) ≤ (-2948252070413833968303775896718922515180694938012687266761391309528965302094925484559338952174843631791063535105964371945650956796456736317050022609825125092253358272761793738128685847265536665754059982064488019133309651784245192043356138826593357903630444266406824666779393 / 3207173999184570648420720745035027521968144512175073675091601464744658885966602165689466027946694858415336688801632567665058676143753749257267556637247560996603012084960937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_16 : (-1672405838797 / 20000000000000 : ℝ) ≤ oddTerm 16 ∧ oddTerm 16 ≤ (-261229767441 / 3125000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-145640952813744225788510398018501353518430654149039379401826618925428004405416237367800582455613330495392434448032486583604094952377387762349139644935869254541722818214215773052473171044244622799807246407928534297796244607946974650895793425778768190657002447884394867565018389369331574410509826977742082817124225241579581693 / 601659514847033959301424414294294878824923170857598848096818840899796752605247901837816105526330164148892520946659424244023381534330258879915878642716770704962590871581203560490394011139869689941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 16) / 2 * Real.cos (169 / 2 * Real.log 16) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 16) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 16)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 16) / 2 * Real.cos (169 / 2 * Real.log 16) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 16) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 16)) / (2 * (169 / 2)) ≤ (-776503115213318605427504475349522741925909338988003337205166552804209009207569887991195407479684482466947139644165783149518468996561944324883512399533463997754979803260642976888501299750865538768995981287949056132578813789390730481796345593545165932457951156539167963781508736014233528769521006201079 / 3208850745850847782940930209569572687066256911240527189849700484798916013894655476468352562807094208794093445048850262634791368183094714026218019427822777093133817981766418989282101392745971679687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_17 : (1529804917077 / 10000000000000 : ℝ) ≤ oddTerm 17 ∧ oddTerm 17 ≤ (7649778650987 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (1257365553973293966292950343413523783659647080988539976801639951339058330051380524893129207508995201879559630965363118816508627496539408649255899632342745057773261235984780740629884339622810801766706396638169938662043921515421416059406539303532284511598514638829225916061492526537816632064799433750099610718966454037741 / 1604425372925423891470465104784786343533128455620263594924850242399458006947327738234176281403547104397046722524425131317395684091547357013109009713911388546566908990883209494641050696372985839843750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 17) / 2 * Real.cos (169 / 2 * Real.log 17) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 17) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 17)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 17) / 2 * Real.cos (169 / 2 * Real.log 17) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 17) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 17)) / (2 * (169 / 2)) ≤ (943117131667285411426695257817558464529724791805066328125855746741664609127397932767854418105442649828671008697850518211718469454720136991345526896474641045145958476360630209810297747146692791875661704835350102295875884899454638743866074376118086249086677677182617383396059705851511806158343318803884414095600683199833 / 1203319029694067918602848828588589757649846341715197696193637681799593505210495803675632211052660328297785041893318848488046763068660517759831757285433541409925181743162407120980788022279739379882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_18 : (3478230711733 / 25000000000000 : ℝ) ≤ oddTerm 18 ∧ oddTerm 18 ≤ (13914514359753 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (89529391795432710806726214114073534085524746171246674276821238530920365642486114464896107004499530602509778170951687485969281871858319852278816844184460694332523770178093256391372333871926865085902518805415044793689964063225397039280489744153755697004043987477921923187288738414972480424859290993 / 134588955187251942593802753417184969996527496278437881544953581421940326327424090435731170275920464683219013129421728519701559747358268914190223437581947852528395452961948182324218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 18) / 2 * Real.cos (169 / 2 * Real.log 18) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 18) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 18)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 18) / 2 * Real.cos (169 / 2 * Real.log 18) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 18) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 18)) / (2 * (169 / 2)) ≤ (2686188992851750809432644264295959621830725074031357332626022177000225056748801568926816527153515115928113757781662944418252207104623194879357149792791430447738603749746409888233222636996841822188126911469142946656061190212328095441207422621350967409291360525263865171864341929919738025291546595489800689103284846971659 / 4037668655617558277814082602515549099895824888353136446348607442658209789822722713071935108277613940496570393882651855591046792420748067425706703127458435575851863588858445469726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_19 : (6364782084787 / 12500000000000 : ℝ) ≤ oddTerm 19 ∧ oddTerm 19 ≤ (795677432427 / 1562500000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-1454012122105789668282559640340103330493473113820144172848386002346616944926819132109412807677029238531235927658405838319857635378700750907086802533539265370076215795237327720273082218481320941676487034813438118050037486478168984134277116447450277014689128601844188008896630958284609441817591715002050472450189664685497583692113570939 / 1928753693739968195912954512516627102110410736205767320282161228229549825603389679494975222785895789144420526727493162674246293739676526858277388705820270139447398154675432002016133083091281296219676733016967773437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 19) / 2 * Real.cos (169 / 2 * Real.log 19) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 19) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 19)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 19) / 2 * Real.cos (169 / 2 * Real.log 19) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 19) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 19)) / (2 * (169 / 2)) ≤ (-1938488707990166227933402983105593692035248151487665286691953321743435077984472586369596019550153345375722724864577682156852565195073846304317361418671491666974477517026387400693492904594471771523050173232279757298136178305237417766238874857642446284672940469585341754683959821208524728598457290590797526367529954295120522711273463521 / 2571671591653290927883939350022169469480547648274356427042881637639399767471186239326633630381194385525894035636657550232328391652902035811036518274427026852596530872900576002688177444121708394959568977355957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_20 : (0 : ℝ) ≤ oddTerm 20 ∧ oddTerm 20 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-5247365331469837208883615716049576159211417510251507545228822245863392462463225898983792664211825115732051190956644651979406363730756683093980569819483856187903462328840885133298943007561924010769527272134748199518993812726459871661099820528413636897583103423727630002442451944633853377246695773280830331082302387240413224709111084038742961569 / 23700525388676729191378385049804313830732727126496468831627197172484708257014452381634255537593087457006639432427435982941138457473145162034512552417119479473529628524651708440774243325025664567947387695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 20) / 2 * Real.cos (169 / 2 * Real.log 20) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 20) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 20)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 20) / 2 * Real.cos (169 / 2 * Real.log 20) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 20) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 20)) / (2 * (169 / 2)) ≤ (-6994135161672180824343227646621251734362194682713901325774545871311069436316956500505691460835887761038384092713022064871056346466301049592642321374310487546938815382955996915684466446829109087708205402479240031905816605417446659984879742929320857301644925227352243281924417286904245799647694931465528615821961915195883 / 31600700518235638921837846733072418440976969501995291775502929563312944342685936508845674050124116609342185909903247977254851276630860216046016736556159305964706171366202277921032324433367552757263183593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_21 : (594986795213 / 1000000000000 : ℝ) ≤ oddTerm 21 ∧ oddTerm 21 ≤ (29751982994003 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (937338144531830061144352872856937623120920304908874663159964069051076290643630604532785651340553166150112090549677019528380116563948838675621235492965320403120210199594667130878114209447446862793389356517378858467700432884983304726658785861440153665009580485212755087963580800645685649761589644696837948338426175921398026624115197 / 1131107832049155738420492707651612245255899132864977327615185098392413730115316458979455902805355920087534640465850696362649767002443247737675993773698608113915192151710233627472886847263799210520438639447059631347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 21) / 2 * Real.cos (169 / 2 * Real.log 21) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 21) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 21)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 21) / 2 * Real.cos (169 / 2 * Real.log 21) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 21) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 21)) / (2 * (169 / 2)) ≤ (703066070228636324809460481966938197715363041567521440096467250728229758913875804042499333153223961546440854586228677915093126285414056343942377805452607538779069376121122476839767967209819681735594334772364191623815622535749784195989134872664420617065542508852820232837184713436210299208933167795165225514704891461885581109778507369632613332913159472873 / 848330874036866803815369530738709183941924349648732995711388823794310297586487344234591927104016940065650980349388022271987325251832435803256995330273956085436394113782675220604665135447849407890328979585294723510742187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_22 : (-3363 / 100000000000000 : ℝ) ≤ oddTerm 22 ∧ oddTerm 22 ≤ (2653 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-5308757435867818636327749033858405341894309065227960643412988088952720347009415884462951980768483173969180448242252032536267142313518998054706708151599730787006847085164271692870955126622571916934383361469699408941169712738117599555356438957342642089255292316069688830880337717724650928296855451870651404657682580892147247354310789619277904883890638795243673 / 6875132880022768141202551831213664372607940893166473357802307671272966415537067525813582773684644724563220099443236635956914006618604405906489232656892197393968396257440301742388639520800225852223231174650882417811038933945894241333007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 22) / 2 * Real.cos (169 / 2 * Real.log 22) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 22) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 22)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 22) / 2 * Real.cos (169 / 2 * Real.log 22) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 22) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 22)) / (2 * (169 / 2)) ≤ (-1415534954645932435703641909081880847662720086677702372731354320881399608676426111977990219995696115788918778648112363216504124092946913510357590417899597780980052919156576444603848199992886638578819785075258357102116099539531710032111085122219269166599992828944331937283349567455709056066985277006045799828520230239264393022787443123831379294734204071908939 / 1833368768006071504320680488323643832695450904844392895413948712339457710809884673550288739649238593216858693184863102921843735098294508241730462041837919305058239001984080464636970538880060227259528313240235311416277049052238464355468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_23 : (-3772770337147 / 50000000000000 : ℝ) ≤ oddTerm 23 ∧ oddTerm 23 ≤ (-150884040763 / 2000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (10167649085327166031139671612080799015960639158553292324027560182428605236713282478887342425223202469237671718705346914052628579274059443561836075094046938620836687713228351575251909703427411224138850899862039960479151162314614624386026968639843550707652979437675731013855426445525833038911054684203905083379067119717748743365803234918122443709211897910719 / 25031594912509562938991690933912150462401889687475444332051779752474729278257625409539942258677604259387510690950664231892906463208714352527093241744560391578395156507089311943843437757509088969516759903440012785203569309726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 23) / 2 * Real.cos (169 / 2 * Real.log 23) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 23) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 23)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 23) / 2 * Real.cos (169 / 2 * Real.log 23) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 23) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 23)) / (2 * (169 / 2)) ≤ (762708991600608849605015367665115423871748929354982820747037482531794755384805246388430352922416823001390584623050267055769385020072781347774192330657620965595938364181877961417179011576017194486515991112537630852627960442514990732919935260878885404441681285622019128817482335791547099519309056366427657279605862380711924416598248423959613721959223222704564625276907 / 1877369618438217220424376820043411284680141726560658324903883481435604695869321905715495669400820319454063301821299817391967984740653576439531993130842029368379636738031698395788257831813181672713756992758000958890267698229492187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_24 : (-247226316363 / 100000000000000 : ℝ) ≤ oddTerm 24 ∧ oddTerm 24 ≤ (-246824855749 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-1580210106285831877158658251092447745327732233280827447393898882405129221341033623951632255077057190738413983719310077689325263740178533327846436064743442464699566041207850514177311114057561430861201025292169368762341044830905363257664641669454201727096733550364332709667336989139341765094421690988284150447442831725749752688200618379053627263444978061517541990001310489992006329 / 36162602349522066844178819436228596981866046574954618874607998823361211895178062783464304363489074462401013229700362997141703472309503887170880816164182855594268677771064760731129301993728606046455601196284818506716714642937515659128273616909980773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 24) / 2 * Real.cos (169 / 2 * Real.log 24) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 24) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 24)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 24) / 2 * Real.cos (169 / 2 * Real.log 24) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 24) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 24)) / (2 * (169 / 2)) ≤ (-42070508719789235684786171546987508521841132454827254651878042303475676195018131024736991613979927418025291686169909321224009150214748449397916409240304313464050215696645115577733835297157827578321614953687756141800360645941483072578982495771871288909697482786205270669853586490533294034997387506206037996613186323465209666461210831809554064451451158369141901033453693 / 964336062653921782511435184966095919516427908665456503322879968622965650538081674225714783026375318997360352792009679923778759261586770324556821764378209482513831407228393619496781386499429494572149365234261826845779057145000417576753963117599487304687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_25 : (0 : ℝ) ≤ oddTerm 25 ∧ oddTerm 25 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-131174133605013103962455906355707271906545103029262316030699243391986677691341857149744562169522701056171329678363295300664488119275010891532001740063283216840709951212043296019601596087485769536339918755014835700571856325916773491619994933507192705692286085105629224898562931499919358885439045619718071130439007341669658593603733409404026666018663203555614711487776197904360975663 / 657793904784231323795735432872399487348339727304021268984943141246935045186147595513181010819409029179969606588208316627818994171493684683280313332291968537797741696905445873765153046292263862532410734207311516124113307213292785656963562667624151325540537982305977493524551391601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 25) / 2 * Real.cos (169 / 2 * Real.log 25) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 25) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 25)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 25) / 2 * Real.cos (169 / 2 * Real.log 25) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 25) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 25)) / (2 * (169 / 2)) ≤ (-11189593038027180350434905675220397544920618763703612217982988959658708962714907634430262309807246932960675128194782930959874946340158791955283409277971823820534080116254025731499731579012699608028883514323831173144412645725137853386091930635565508212776401806886902723751025001226512691981576613063183810162414472380571860137112433584192777091051757823973749 / 56131746541587739630569423605111422920391656729943148286715148053071790522551261483791446256589570490024073095527109685573887502634127759639920071022247981892073958135931381227959726616939849602765715985690582709257668882200984376060890680970594246446125907823443412780761718750000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_26 : (22103432697369 / 100000000000000 : ℝ) ≤ oddTerm 26 ∧ oddTerm 26 ≤ (22108238860077 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (75360782084740323507186995860876944848483326119650094280843467765218831700463662219954197353052802798864313157780778573710817546337958336712856514509765441473950753892355337689737039981201666082873272756438323406548923012181995837983450880977406143779033907001041071578410799372385119529412972941584024987110020227434083143232790267725585517608933237074668553556749 / 235433609046367622683455855704613261600690407389027466631562492339591223275898846246512398199798661864589929880861738262641298647848332598768755313568898799441853370905369536009956393188337278948278653621645953819770277623291117572449698026757687330245971679687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 26) / 2 * Real.cos (169 / 2 * Real.log 26) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 26) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 26)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 26) / 2 * Real.cos (169 / 2 * Real.log 26) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 26) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 26)) / (2 * (169 / 2)) ≤ (14133219092190348546271406375535276006963230848462143803039272010883631155046010328989385034545363178706046676181244169072393955343117221546951653893901425485423700509337371434146348046498515970059790838097906768387505475997540460136055609457460564123816883122366601814805669498416079435026079967072301118825326964113166990982492126091139026839383426502066395164568267597015539283430418663 / 44143801696193929253147972944614986550129451385442649993417967313673354364231033671221074662462249099610611852661575924245243496471562362269141621294168524895347507044756788001866823722813239802802247554058616341206927054367084544834318380017066374421119689941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_27 : (167036466007 / 100000000000000 : ℝ) ≤ oddTerm 27 ∧ oddTerm 27 ≤ (167069617557 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-21798955461491690878303231099357522924199438850867057154584361204702406440955040638150913712175875461732888250970543594926466581361918709824210925459322039789232739995283431781014055037537633164609285711259982020275567919331635626965265576990417919065026364270693419795935004180851571324552581304520050821032036577088380755551933249409128157995968423149260429292368484807377187275608728202052477227559286146699 / 63243860467418730240976923037864538611645643082300350529821099374715375741967655878428321513380292759338192141190555489288467872544665130002146410876696753640359556974146065477229585398396921630608442351070477444309757154169488301133638433823557271235468817949295043945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 27) / 2 * Real.cos (169 / 2 * Real.log 27) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 27) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 27)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 27) / 2 * Real.cos (169 / 2 * Real.log 27) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 27) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 27)) / (2 * (169 / 2)) ≤ (-29059506993023897635664753430387702656816504810852686687544654156544743420696545965804623895499460482499590845655165987558065407108870601437818227729397754689414328105338840235494463590361605720224952070614916076504860683378605152563828324313166176447889918950492031452115516330963939215621250982241801242868469574284239859246799987709714562078953084077391001995482588450463840840289953 / 84325147289891640321302564050486051482194190776400467373094799166287167655956874504571095351173723679117589521587407319051290496726220173336195214502262338187146075965528087302972780531195895507477923134760636592413009538892651068178184578431409694980625090599060058593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_28 : (5622406328353 / 100000000000000 : ℝ) ≤ oddTerm 28 ∧ oddTerm 28 ≤ (5623720251703 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (226887712638054364189808980691424137694470413502148197737692828921604562992843042686682521855832112089425797951000904364942110207141061527398663836563172543484321552529016385269087932553667194684041587371369041901737647460233404824790427161442966395190865536043431688251278008251456799845910869049796894490334229972113314644222210728880314610983152413309697769299047009 / 780164333967877657502489182714126861152979249236509734250810669311963012395195328076342494264665954331768404180282558589577262141851097378014667916681575023440443220674808560079416072952047440542566025208180578187753720724845669174553661921572934358498862082249015168812500409245558330439962446689605712890625000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 28) / 2 * Real.cos (169 / 2 * Real.log 28) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 28) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 28)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 28) / 2 * Real.cos (169 / 2 * Real.log 28) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 28) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 28)) / (2 * (169 / 2)) ≤ (166216358523282074765336717450795307139684751702148437551666278196962934857162667222500802331735456563373636015160595562582698883178451062496651412233558428744232505518076633986227645529934007876768743160923024111502452061857626899948273373913653538377673022908162000976307303329958098919579590984314575952848997090364247924893947385904124732188536763940357580293798360815161384261584474107 / 571409424292879143678580944370698384633529723561896778015730470687472909469137203180914912791503384520338186655480389591975533795301096712413086853038262956621418374517682050839416069056675371491137225494272884414858682171517824102456295352714551532103658751647227906845093073177899167802706870133988559246063232421875000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_29 : (2561134124997 / 25000000000000 : ℝ) ≤ oddTerm 29 ∧ oddTerm 29 ≤ (10248729050317 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-6285140988673819476973530425071445833816656218194169101908756548945470182642413683154822474329385829360223594641752692995217871438893075160877005973549677524925088075003182564899655743562203655492116556443145490997403181361583494108985070311238035727403656922832177682193974439675840199655044055462819149995633261930797131514930179523688304881687050096598805453529160463505359853725443906898462419 / 38346637343189122621562348308764763479391236058472926457895846018021605985248640765608386278096860987315080602269248319794901588796265138324176957440732775552144665182608190345023458817739035797548205271032491779084470881067614331267661590769152869588936069066703593577472020115237683057785034179687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 29) / 2 * Real.cos (169 / 2 * Real.log 29) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 29) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 29)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 29) / 2 * Real.cos (169 / 2 * Real.log 29) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 29) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 29)) / (2 * (169 / 2)) ≤ (-536112628419168138620663738425559439646347878881134498318325152410720591936805609901245738245903598302812525305546635525255781698629396450719774668346964206217448875925889832487805719880274679432515438292459871999048146821542296791379088415606993182826371379995277836874416594136598489693545717334178274730526054833180618892483574574397024663443928900860024570594164554961057 / 3272246386618805130373320389014593150241385476989689724407112193537843710741217345331915629064265470917553544726975856622498268910614625136996433701609196847116344762249232242775335152447064388057446849794772631815208181851103089601507122412301044871589211227025373318610945716500282287597656250000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_30 : (0 : ℝ) ≤ oddTerm 30 ∧ oddTerm 30 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-288470129444928314576368625423458304096222974072066068140465101812330237673034525247696292772904572349980016333106112976950510507338665319492496109176055104971890808298378194087981818285928450313611218668561537448514517705749258416933672161724415189058669766004419216351611399855728584953042940772084568025334091147536693897753778707556894431937180017475063226429399044393034869211906100895267738603637750899971009429 / 8826879079302716486375919442420418909470780078829843247205778956116339573769319394757349920805016247556352315952612473265129168794357094554101764455790880920751651984652585447941072221000193950202605879836714351643007274039654848087708863058692482213361845723398184364826745117187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 30) / 2 * Real.cos (169 / 2 * Real.log 30) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 30) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 30)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 30) / 2 * Real.cos (169 / 2 * Real.log 30) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 30) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 30)) / (2 * (169 / 2)) ≤ (-3838552997086225479385542586874427131257572632899752486526035241508352476434389486131896899569754752719225784239025606071974875506434518437685098328887587912038387494363284045070946732866226127953264314332142984299336419061037825897809821266236504055327367757664308480213412473216008954452000838575091599749012277921692629491624679913872801770793387034644422004373324318865439230237963525043569517646341839 / 117691721057369553151678925898938918792943734384397909962743719414884527650257591930097998944066883300751364212701499643535055583924761260721356859410545078943355359795367805972547629613335919336034745064489524688573430320528731307836118174115899762844824609645309124864356601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_31 : (3423482098243 / 20000000000000 : ℝ) ≤ oddTerm 31 ∧ oddTerm 31 ≤ (4280363523903 / 25000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (17065766947708142580920092842016596577446057072073774435769710801321583151351318925347707073901441495680485944800100054162455430550610427983504259917767790251649654861527581773174932506483408459886970110626471617299722560141996314833320475255446226558623236850415543504649895169004259353318091491250376092417395940199119391147636482547467685751863103361096594346686350008741909440750429787635026782495518723193303375682149452796375477 / 61490152571542814369138283068477822797650866729422500857316157272545152957798531003949257280753590164106622867486748408250961573064539416153287740312071393011790550699415357126404700563432048169800501028546932450005420960632494180151125063842074085849552249935559559513741322099447784184158201217651367187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 31) / 2 * Real.cos (169 / 2 * Real.log 31) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 31) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 31)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 31) / 2 * Real.cos (169 / 2 * Real.log 31) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 31) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 31)) / (2 * (169 / 2)) ≤ (6401174380935081738452900647458911258887938718284120238983723953228066537743564500242819602661585612962507327633090423576208312704445304409762801240319855201861724032733843051893538743592211976494853267068153621239514718253258282262330813123507286817810935640998744036414905347756570295021771148376535386267438495966019233437095163924134855455488612893308751384245314412580671040788125045395032144728497891875739437137260411882155027427241621927 / 23058807214328555388426856150679183549119075023533437821493558977204432359174449126480971480282596311539983575307530653094110589899202281057482902617026772379421456512280758922401762711287018063675187885705099668752032860237185317556671898940777782193582093725834834817652995787292919069059325456619262695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_32 : (-5825712903 / 50000000000000 : ℝ) ≤ oddTerm 32 ∧ oddTerm 32 ≤ (-1164996373 / 10000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-3950463957439712117671903752354400688033599827374671800938074561358354877392964847810845835809521855352827313926602872833976588115090349738133934487326988131979540142510036459829350033082982193539595214785671945254181218751302468056979368513084533519527302078843537743753029857504598934409890226029455351508018753386676237796362187948900570068761782450903473528997953273121052133217697895166212534397532858246877466715728175020919952555771 / 7686269071442851796142285383559727849706358341177812607164519659068144119724816375493657160094198770513327858435843551031370196633067427019160967539008924126473818837426919640800587570429006021225062628568366556250677620079061772518890632980259260731194031241944944939217665262430973023019775152206420898437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 32) / 2 * Real.cos (169 / 2 * Real.log 32) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 32) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 32)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 32) / 2 * Real.cos (169 / 2 * Real.log 32) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 32) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 32)) / (2 * (169 / 2)) ≤ (-10533253198376079585924528147332661868586996192688055226053816414125671796305376874365173022423754006266270278343083123632230456140246153241446977585326275979355181903458903947444489241114763007232935946140369784577274651314260245448864688045912616084935766975730195939557803942597732120096644995411942719234216248254935824521024749956866622529630138944727016301635121967381201171515086414903264896520421015003745567599917848448302291745823 / 20496717523847604789712761022825940932550288909807500285772052424181717652599510334649752426917863388035540955828916136083653857688179805384429246770690464337263516899805119042134900187810682723266833676182310816668473653544164726717041687947358028616517416645186519837913774033149261394719400405883789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_33 : (-2369 / 100000000000000 : ℝ) ≤ oddTerm 33 ∧ oddTerm 33 ≤ (1013 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (4848736127979497287310741596194576048657676246030925155591448365523321736564435299158215103475641262625364420174401742436954753439596569448958702856315415145508674721128897853942661701457768557521785392678897269052538062440550036877371035868038373330462201361190019596596321141072267670446326942669249206070345286008933209994883854067442782852487491554751616135659101356097337763265382936211581915140255773070177501961478785246559072893 / 7506122140080909957170200569882546728228865567556457624184101229558734491918765991693024570404490986829421736753753467804072457649479909198399382362313402467259588708424726211719323799247076192602600223211295465088552363358458762225479133769784434307806671134711860292204751232842747092792749172076582908630371093750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 33) / 2 * Real.cos (169 / 2 * Real.log 33) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 33) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 33)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 33) / 2 * Real.cos (169 / 2 * Real.log 33) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 33) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 33)) / (2 * (169 / 2)) ≤ (3636906401337753714335088278251795798236246260974104289385260862123094889495744111643758005425243669226692796895004332890263996505630319607101531550207104614595764923264627410209369786932490224776728946336092794223081481450460994716043174133489475369816786102706067841021267543956092825963724054152845843344349701350591570255113043273933058948909135364522444304972033513577854484904366207345993647746973766065844462455637674784661680753 / 5629591605060682467877650427411910046171649175667343218138075922169050868939074493769768427803368240122066302565315100853054343237109931898799536771735051850444691531318544658789492849435307144451950167408471598816414272518844071669109350327338325730855003351033895219153563424632060319594561879057437181472778320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_34 : (7462597321003 / 20000000000000 : ℝ) ≤ oddTerm 34 ∧ oddTerm 34 ≤ (37317070462169 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-191994871339922117975287125673176844085145357966357691726001818064169811587425444354528097028697994465739653878233498459863134033291585498100105457658032452168214540038202302521437310084414853328368734050232108293109490824147455691136507298314677968991535020709238687791424206076064548347969743448732599053077308093868143505833713097420077948266188729638226959143268694388119328616460300563639253421829313701117290126846372926917361903264008974582395788775947 / 336259724145191856956175638108184768235219595996862749021011054387924023888746941330758998357671058038675550311576036474373104694305034078429132372114791627312072372633520946019766027073724713397055243172549462439623801435285051808449042434482493800983076807288481623202670115748753147483051695792392468452235116958618164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 34) / 2 * Real.cos (169 / 2 * Real.log 34) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 34) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 34)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 34) / 2 * Real.cos (169 / 2 * Real.log 34) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 34) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 34)) / (2 * (169 / 2)) ≤ (-255965146787974781704533669432223392246921618585237288001204369097723683738735285957558668637009862745330499000806451031549393568134746447378393810027034963085687786369302808788401721895065550691981826659155586103672083506809350822556127179836367645962777795915057805993093501252929501804630299763353466245399478900137193142053379506499018293079309377456523297738884091403406534362419501087947294238507948420621798312749787584690240567 / 448346298860255809274900850810913024313626127995816998694681405850565365184995921774345331143561410718234067082101381965830806259073378771238843162819722169749429830178027928026354702764966284529406990896732616586165068580380069077932056579309991734644102409717975497603560154331670863310735594389856624602980155944824218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_35 : (0 : ℝ) ≤ oddTerm 35 ∧ oddTerm 35 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (4688596793444781007874128362683561480121934697093613485133104933279254202467498997395132768164007700830487808623388323822717291576594421568253246496205250330550918764382565529261827854523232672927165036038999074809144240888964623400828103304455856565593792086477900978458891888670705533752682972633958273210184057905103485319322066759891213090074291712214350432991893103104859655146059405252318348878242522597784517369134476201520465709863 / 18681095785843992053120868783788042679734421999825708278945058577106890216041496740597722130981725446593086128420890915242950260794724115468285131784155090406226242924084497001098112615206928522058624620697192357756877857515836211580502357471249655610170933738248979066815006430486285971280649766244026025124173164367675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 35) / 2 * Real.cos (169 / 2 * Real.log 35) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 35) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 35)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 35) / 2 * Real.cos (169 / 2 * Real.log 35) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 35) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 35)) / (2 * (169 / 2)) ≤ (3517313151460199433702229963205050894875866282774033810128490322983549844892484804926887349935216223602126162899084909569331242154699066124354549713004352170790049749751499360419061492160499114784615414447881079007314164808763554930649220140831779621807325268248364317586312387181301640185650338191392753323789594614638646905198437496026829303583843918138397152089089179861344553007085440498659874751000314423121906556531618983849218169167513301076924392406132901 / 14010821839382994039840651587841032009800816499869281209208793932830167662031122555448291598236294084944814596315668186432212695596043086601213848838116317804669682193063372750823584461405196391543968465522894268317658393136877158685376768103437241707628200303686734300111254822864714478460487324683019518843129873275756835937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_36 : (-52022621733 / 625000000000 : ℝ) ≤ oddTerm 36 ∧ oddTerm 36 ≤ (-166423864889 / 2000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (6163820865453290598229284421732499489302360145420247892748497874767202623420268673638737478931034584724555299213798581469898419456797813079165853054590159758546127535321891925540970881414625539328578662464278431284411301821242904758470809899224251232864555344659975461867033322692905215771456820351447825235557567448496728740499526023831790256702889982710308191581154194652395588267508422187655352302396053646982540848717974071659199861804159917855360620002102487791 / 29693123331380138615906804185577406868098374413457126196016753322712920315034788180628854641505336919625545555270636725959150424999210628448354301266623689717363609662628190722515223469128831188193747245006567749050399994822159339532356032611468545317933189271166107314555111007357423686674332950234974383941644972518858683969175908714532852172851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 36) / 2 * Real.cos (169 / 2 * Real.log 36) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 36) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 36)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 36) / 2 * Real.cos (169 / 2 * Real.log 36) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 36) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 36)) / (2 * (169 / 2)) ≤ (1156053386637843059114201361012475644710116558084948493512817247036935280819341200595453393629325969315044715418005664152196573677422605077390796192432275829663178208441521742447395190591815458512268200221818427236414533072807462785773287280323465972620632939763267360255016572101305402158247202971959055781546615839461340197056175222922888336384182158850033158960623327978451137682114187358083672523429511283902578382299381292978740001689856711808430589857714425887819438164509 / 5567460624633775990482525784795763787768445202523211161753141248008672559069022783867910245282250672429789791613244386117340704687351992834066431487491941822005676811742785760471604400461655847786327608438731452946949999029154876162316756114650352247112472988343645121479083313879516941251437428169057696989058432347286003244220482883974909782409667968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_37 : (-9275777902303 / 100000000000000 : ℝ) ≤ oddTerm 37 ∧ oddTerm 37 ≤ (-9274772830049 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-107812741411129471130429461072816408890936062526591610344639104013561616009247211901838710973389890306208180878103658787285915413536668293715481644089547372281033199025385024595008622227154933311962939012418903574271914278368261065123592880114614682193910197943047550805297155268186075145864048392612646000495214711722793601559988814043357735552330522557056015906313169055878673747778056656083756928824619695871510747586029077107643932134714841202546703498139035639768749990679128616583128443891 / 196008858306835405786850688268315051301513886836462309571329688061714143483268858732622896274835602995615141249032017310668771940897503300322455184804289619974359619547195449597458384771826899507628204900333495604973215286697420250103589885439678533193470204860586260368043298805593452214300304040912543514662188294839679016783231665652802504657491445541381835937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 37) / 2 * Real.cos (169 / 2 * Real.log 37) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 37) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 37)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 37) / 2 * Real.cos (169 / 2 * Real.log 37) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 37) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 37)) / (2 * (169 / 2)) ≤ (-287469491828484048952340095435856533202782494449649504356552131089828134908249129899555344843763022766099750966655204884386173405911123455300062312408156017153314606451912474898723431173251058909337429490514394939961595487409088726583984209339220090519133141740379622914821565814583830352409560455364753050960513637729157478805599755728664368545713411781824456479457574463944533858613721405596545092394151997373329753010797733516683862244521491390220014545908113657691874381506101160060700956313 / 522690288818227748764935168715506803470703698230566158856879168164571049288716956620327723399561607988307043330752046161783391842393342134193213826144772319931625652125854532259889026058205065353675213067555988279928574097859787333609573027839142755182587212961563360981448796814915872571467477442433449372432502119572477378088617775074140012419977188110351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_38 : (-1809 / 100000000000000 : ℝ) ≤ oddTerm 38 ∧ oddTerm 38 ≤ (1707 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (1575429462626677836109821461969067171936142645486136783258477902254026763158618576243359964900602234930042255234888747559131995051571211784632905124937331460638216963239259196606895078715048436635919233793210136707756486188842310634694337385288734413324648903006487970873972510017754231074602209264990294915210619712973017734047333662806188390023443111013432067521396363886676132003501454303956413274863782087416070213191981439440011434025641264763963535024350723671013 / 3062638411044303215419542004192422676586154481819723587052026375964283491926075917697232754294306296806486582016125270479199561576523489067538362262567025312099369055424928899960287262059795304806690701567710868827706488854647191407868591959994977081147971950946660318250676543837397690848442250639258492416596692106869984637237994775825039135273303836584091186523437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 38) / 2 * Real.cos (169 / 2 * Real.log 38) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 38) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 38)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 38) / 2 * Real.cos (169 / 2 * Real.log 38) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 38) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 38)) / (2 * (169 / 2)) ≤ (295427104816906528851456532465253129171946596606672923172755664772275895747651126912829288402047662408472199173078895372465004496991855956655193896971322460680442748595221608274748427875279320310385933701457488291260615843544198872917227194373497881219849313610887529711672151199038646477951842852546910716408998881567298342348303256547533798020487544959609892871373843051502142929210517257734147871600252893674393341579471758673283352061238237800490882909515263473766818201317660368881958753 / 574244702070806852891164125786079251859903965341198172572254945493303154736139234568231141430182430651216234128023488214849917795598154200163442924231317246018631697892174168742553861636211619651254506543945787905194966660246348388975360992499058202715244740802498809672001851969512067034082921994860967328111879770038122119482124020467194837863744469359517097473144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_39 : (2412037717687 / 50000000000000 : ℝ) ≤ oddTerm 39 ∧ oddTerm 39 ≤ (965547467213 / 20000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-5466054137125332481436724547775618624964978849007582048723045685945499068341397563402780847564110252973440723746072610881261495987616896216116867409577800379965256756429273400433861490030446796202492332639823231675404615475267133414862985255456932136566117160689227658486865435599576221655244446263610250423765727357018163405311469438570613187177361219221727780262817406772144956451679527241566533944989140026533957023310871528201689208812426292907216325858189696926285839989160519998700540165709 / 71780587758850856611395515723259906482487995667649771571531868186662894342017404321028892678772803831402029266002936026856239724449769275020430365528914655752328962236521771092819232704526452456406813317993223488149370832530793548621920124062382275339405592600312351209000231496189008379260365249357620916013984971254765264935265502558399354732968058669939637184143066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 39) / 2 * Real.cos (169 / 2 * Real.log 39) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 39) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 39)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 39) / 2 * Real.cos (169 / 2 * Real.log 39) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 39) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 39)) / (2 * (169 / 2)) ≤ (-29130176351765882493243566024448351419795386191072472459282873032864320677165567511507592934832374396937370933016209391226516538084687703672674321477677466471900454228092547461262071710004114805040137286840685243536246275113938452013907534157993981116900673660476904412350630301083088329713835603855546304472239393309888891638022722521597226561191488796132514781578371906081550229756789794240596066647584244638770541646211738964296856591268764376790586933249154599020745543 / 382829801380537901927442750524052834573269310227465448381503296995535436490759489712154094286788287100810822752015658809899945197065436133442295282820878164012421131928116112495035907757474413100836337695963858603463311106830898925983573994999372135143496493868332539781334567979674711356055281329907311552074586513358748079654749346978129891909162979573011398315429687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_40 : (0 : ℝ) ≤ oddTerm 40 ∧ oddTerm 40 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-449510258385733220512815966316548469247855828269767516549052824824583591562053302696478148404773744116033040337621452345169879202612994020468400588879462333759002766506459495810737393081986501378070743675204077973915084208017772194503800821871275233140890356396837502374281288431918035976237113137448072756525260440653266305336056058934048814892782323535258837673695086903978097914552329317776133468470931663011023139834493497727574367903092463713331355896498295633066168730398363787348873235251 / 1056458976325653529314592190662505070705014965349654129807885963390897913631053360919674131875296026099724707059101526777026685401227802367919220184041989861049603885314646727825563749301705893740122655073633404337552417578799576611923922716151472268713337711444337596224386329513218306301543068544983633559026056341116495083029938415761366945130156449642464123765303021709044406506450286542531102895736694335937500000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 40) / 2 * Real.cos (169 / 2 * Real.log 40) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 40) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 40)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 40) / 2 * Real.cos (169 / 2 * Real.log 40) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 40) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 40)) / (2 * (169 / 2)) ≤ (-74908287568912569291895760292166421111710255914267705772482605454715333932735468715314335068672166936361389212824088501468302173282203591588168629289387077755385390564218995199449521133700202935526264896660867089490748503560095898354330459869346110071341959049853642041767870682999770243830175577818887038542632505089657090956691489165682272439383632045383430565505632159780617511707297572412984906403626445976322740764133770774651557060808364458405245851258890977002278230390936174230357934393 / 176076496054275588219098698443750845117502494224942354967980993898482985605175560153279021979216004349954117843183587796171114233537967061319870030673664976841600647552441121304260624883617648956687109178938900722925402929799929435320653786025245378118889618574056266037397721585536384383590511424163938926504342723519415847171656402626894490855026074940410687294217170284840734417741714423755183815956115722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_41 : (29676657525793 / 100000000000000 : ℝ) ≤ oddTerm 41 ∧ oddTerm 41 ≤ (1854995829013 / 6250000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (81153305532780942735408324431134551542393135131400721399110313177989376847533561155244147629716977568451608350377100020075190446374016387690733209635221494807816194349843292517912991253626302187146007431707460400901734293229658200018228089637219155976375854866818088512410018119596489657465111721879094694293237346061262789763731330020611247402252955135221191734885288455859460498440998976777561576387833669222296003919513517271344614141382409457941608065016730315384691478291 / 158595608403747629668172676184056995586146983455134849606133008762102867230545474842119718109414252694019071066663250267157225726893238497353467088436232543062253298732007594072183825883078141345766761704366851350783404389142527894683114334441598768517382911895165639945250139465012643112284348087837340851372556204007271659654642054711270771946140848692146271837234497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 41) / 2 * Real.cos (169 / 2 * Real.log 41) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 41) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 41)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 41) / 2 * Real.cos (169 / 2 * Real.log 41) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 41) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 41)) / (2 * (169 / 2)) ≤ (1826150924232109389409369685318547637670944429607001354249233496591234180720390200233854112944879066223529112162165106114784274279864434782732034971565109607113297107361584336064357231810000616373095400080943847402958388097478965260485619643032280342968127176097787799005226700562528455497478938588995479028150333611149537097967373130946018324876056875667676412930559904544614976753543298018871889833332711936780320995780065710985286578846834114909964700882335786880579561589859643340719542241935877 / 3568401189084321667533885214141282400688307127740534116137992697147314512687273183947693657461820685615429098999923131011037578855097866190453009489815232218900699221470170866624136082369258180279752138348254155392626598755706877630370072524935972291641115517641226898768128137962784470026397831976340169155882514590163612342229446231003592368788169095573291116337776184082031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_42 : (1068812899913 / 50000000000000 : ℝ) ≤ oddTerm 42 ∧ oddTerm 42 ≤ (1069796323527 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-836324330743975010293501126366371742749835342341322266705731125311987182195909941682136764770962934094030243209226801759756442092312409766456009678242985340857362484780616736766673188298008917290029610857212534269944869063921916017065041985358378692129719686989085052234081077946319752472563454659898502968936259338256246411996546132314616032807340841851919786296999751212729838825853984789755619963951819189893406894102784435312734017795824951059875848185414633312855618718768018768826532128542616295059848230436521949963192917619953 / 13841864955576669375400248116958433540444774274698121397898102147338030435485787981594367871539280953250379179178647144561338163093489934850703762104980060751085211227106659445429707156462032966764591312186221096790001435855356249783748094135579064297658133148687214787503105663306793784651785688747742697225918057483022217109477907049850138848772066296435212224239279121195920534526109695434570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 42) / 2 * Real.cos (169 / 2 * Real.log 42) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 42) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 42)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 42) / 2 * Real.cos (169 / 2 * Real.log 42) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 42) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 42)) / (2 * (169 / 2)) ≤ (-371358013106783023969502430110502562247962526170380137605164882809800346631136694404157791312750442921905933051308590450194032017403473814518927432974741310062928703850546599441870501750014634186638641612650844090156205871611696801798447678794425151291635718243908088610819082951253830790658663074571699879313365178621764373179041529440331862737632424280253574659016052039540715224207616104857779671206587859198447824453991557315063381228847456933549230653209774504327598852696527357161663865586402004683284233 / 6151939980256297500177888051981526017975455233199165065732489843261346860215905769597496831795235979222390746301620953138372516930439971044757227602213360333815649434269626420190980958427570207450929472082764931906667304824602777681665819615812917465625836954972095461112491405914130570956349194998996754322630247770232096493101292022155617266120918353971205432995235164975964682011604309082031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_43 : (732384507017 / 10000000000000 : ℝ) ≤ oddTerm 43 ∧ oddTerm 43 ≤ (3662367422453 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-691373287379186324085912411803067550732776259909159558677759259794893750521258354326593928755425879113773221426984271004147367598007377181821801144002264007839623443146144046293336938551405647206830286163085128897734505957769509699650581943281869821775997168569948810396977295283681169300521020359809873322233865982431297320604182323434385754744990996280102464540737509349135787534825612235187621084761523815283256100282466126276815063297245279234750676861579362852275657835162538605193248650091759700899068820121240764367616873 / 1537984995064074375044472012995381504493863808299791266433122460815336715053976442399374207948808994805597686575405238284593129232609992761189306900553340083453912358567406605047745239606892551862732368020691232976666826206150694420416454903953229366406459238743023865278122851478532642739087298749749188580657561942558024123275323005538904316530229588492801358248808791243991170502901077270507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 43) / 2 * Real.cos (169 / 2 * Real.log 43) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 43) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 43)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 43) / 2 * Real.cos (169 / 2 * Real.log 43) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 43) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 43)) / (2 * (169 / 2)) ≤ (-614479380168514607867182580610453868215631424788291336333595463354709764706629446375095109971156840671477878462970438860815063155753650815063371520285428146009581986078849983935514640089096810641479112082127675158615988424737387092541311737792119491956865015854519597246403189979721987996116283315719934250983720829395638757029169666648657048880160582528782209831605022403373940513561175629953904883249385266043052840068774917965813469601011037848783874947407405800466651785747674289198582297803342659733756000034676408754819581 / 1367097773390288333372864011551450226216767829599814459051664409613632635603534615466110407065607995382753499178137989586305003762319993565501606133825191185292366540948805871153551324095015601655762104907281095979259401072133950595925737692402870547916852656660465658024998090203140126879188709999777056516140055060051576998466953782701248281360204078660267873998941147772436596002578735351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_44 : (-2423 / 50000000000000 : ℝ) ≤ oddTerm 44 ∧ oddTerm 44 ≤ (4223 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (2189726970753372896096388109894690100616330136678148796788758230027273893228847124561881640736639457364036080923504574057127846883834179022789179145358447408967976901334278559198976566634750243605977185543160796698705589209526310378788817905320075289439837446349410522009977579901699442897407713511424555043944134779761187745369482254023342952483305065094355796002379959467886825645690245151267007163040119347818514872063328462289957732358698649753208741094976574035884956742331228773534164297138327123961 / 5468391093561153333491456046205800904867071318399257836206657638454530542414138461864441628262431981531013996712551958345220015049279974262006424535300764741169466163795223484614205296380062406623048419629124383917037604288535802383702950769611482191667410626641862632099992360812560507516754839999108226064560220240206307993867815130804993125440816314641071495995764591089746384010314941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 44) / 2 * Real.cos (169 / 2 * Real.log 44) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 44) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 44)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 44) / 2 * Real.cos (169 / 2 * Real.log 44) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 44) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 44)) / (2 * (169 / 2)) ≤ (4927547254957212063136794214770252852147819865603198839177830391987003586173057970918058708700963919912686790813937555545595940055157438711305230130812412104353659664131094662353139754639816848148908242967333253989437793645188987217277642375365912476085592560029340222930035454588188876603333702980265632748125516539387216374561055649503661411048482735272233434710309572069214965176840212058261474463510569266601277364983289713358543915431908688071099658829072054765502391974345452006757691531097137312011838533989127893799312247 / 12303879960512595000355776103963052035950910466398330131464979686522693720431811539194993663590471958444781492603241906276745033860879942089514455204426720667631298868539252840381961916855140414901858944165529863813334609649205555363331639231625834931251673909944190922224982811828261141912698389997993508645260495540464192986202584044311234532241836707942410865990470329951929364023208618164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_45 : (0 : ℝ) ≤ oddTerm 45 ∧ oddTerm 45 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (7068406746535002531916479083986981141191668705657144866385621896956552732052675991122116347416230214750959409462547289480454436609485000291619331582216833036418574868745520933878535600135082180653921626904721181028298575531076668776602854893577303470847873593843873082770468354235280449894515658349327008915029823720777445599332716154601123646386834673672894341466636398086731416195828223900074882608758251200079770100684666995532894053201429221611965570456705005405326484075052601783450580244040397133955984856919635419064380719526272503119 / 42628459886736347069402140297167223954039033482536991960697341684847832108007568860479510387211168086690369744450730620126565104541349991455950078362018776170329028585395411543646728754898966117967842864429301440620091257504030643295456642348352685633013309727869384343656807073281621355498979923247581268512412970683112263279233919124085021873337338318747621541966108982518831390804377006373386955347061157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 45) / 2 * Real.cos (169 / 2 * Real.log 45) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 45) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 45)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 45) / 2 * Real.cos (169 / 2 * Real.log 45) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 45) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 45)) / (2 * (169 / 2)) ≤ (7954492002010907565858757741744379762354547338813735813713049175118331059508558817093066374602652308762335696834962018999688483756305195682419954769758204674824864796006743932402146279661635440908065277947699279469155803293876231154817781906874079029591709063741219697756214104308283714766825343124710647859511348019906269559623047807060500368707652666466612233407683042620086475968111188279382278980623538615864783668473723805031278438601218894242000722702740639000114017785519052054884917372224615828583575427468603353459342736433534794542752305664911 / 47957017372578390453077407834313126948293912667854115955784509395453811121508514968039449185612564097526665962507071947642385742609018740387943838157271123191620157158569837986602569849261336882713823222482964120697602664692034473707388722641896771337139973443853057386613907957441824024936352413653528927076464592018501296189138159014595649607504505608591074234711872605333685314654924132170060324765443801879882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_46 : (-464227475203 / 1562500000000 : ℝ) ≤ oddTerm 46 ∧ oddTerm 46 ≤ (-29707378736561 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-1681605760441672925718440909953480449146914721228630243095182493837888124476536914844772595377049936396899386754534164659920357368851340084747552540435251441200685432570069335289051099056656178675146581365617671864089705608655089876959440862032043206035226976719953966330208740130074360180703001609608838833263945660729439092529472196457722884896238956083641033274173978578972495145462745159801585939838264715011100884717881711524731060394883095960895533165921535332295145014164386070328951222933170633932454807349361822719214273176009166650617392369 / 3452905250825644112621573364070545140277161712085496348816484676472674400748613077698840341364104615021919949300509180230251773467849349307931956347323520869796651315417028335035385029146816255555395272018773416690227391857826482106931988030216567536274078087957420131836201372935811329795417373783054082749505450625332093325617947449050886771740324403818557344899254827584025342655154537516244343383111953735351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 46) / 2 * Real.cos (169 / 2 * Real.log 46) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 46) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 46)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 46) / 2 * Real.cos (169 / 2 * Real.log 46) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 46) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 46)) / (2 * (169 / 2)) ≤ (-747300352143751300680184617372619258702496393773570657453258467866974696279136998643091149647639166436603165040286385009899188407462187856669181315952936693437783445051524299888481955563570473065523703072360203505380647439014083525259593322834087216033837921771894035755883143771089594857743385752066111295900663027305770609572961880246027051451142305198154395329797078989887538652187015068376613187752939033502652990240943653989089535064891579406671681246611310635508124964925319368454564919959329204084388405549427274032607 / 1534624555922508494498477050698020062345405205371331710585104300654521955888272478977262373939602051120853310800226302324556343763488599692414202821032675942131845029074234815571282235176362780246842343119454851862323285270145103158636439124540696682788479150203297836371645054638138368797963277236912925666446866944592041478052421088467060787440144179474914375510779923370677930068957572229441930392494201660156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_47 : (1469144332487 / 100000000000000 : ℝ) ≤ oddTerm 47 ∧ oddTerm 47 ≤ (293992345353 / 20000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (17664810077671107929105565515671069639462788230011049994593847178696831844369573165699372629026692155301073717565581597266514338976844136661732406815001742313858592989906093159204896950542728364486811084128271277084640874352515056995937246827585672754646401521498735892282771601310816345413963711397985250352794794430794951866741151282222902469522679854826556876751337811447872567365450633325709248152119213503750152124285776860613145480914371592501492675456272910636297329121960091231599691917665754524787376321430863919775316909 / 191828069490313561812309631337252507793175650671416463823138037581815244486034059872157796742450256390106663850028287790569542970436074961551775352629084492766480628634279351946410279397045347530855292889931856482790410658768137894829554890567587085348559893775412229546455631829767296099745409654614115708305858368074005184756552636058382598430018022434364296938847490421334741258619696528680241299061775207519531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 47) / 2 * Real.cos (169 / 2 * Real.log 47) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 47) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 47)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 47) / 2 * Real.cos (169 / 2 * Real.log 47) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 47) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 47)) / (2 * (169 / 2)) ≤ (39767936225567631853608979528298840037419600446598028513994940036258298090649102893269983338374525086597839547572416471923358236601234971918704139662495857494844496543467307916517414438116723660590581953021239583902947546930429946359486207170540354629060081646164046009607636057511721279778412170946739028330139078549300531025193831045880412810529674375052705247320018130401313489359077738626564580856163215082452035864398597104570538131198879008731199747788450017884282552546380441874166620446899286892174283258564114826174204671058480232278968150583101 / 431613156353205514077696670508818142534645214010687043602060584559084300093576634712355042670513076877739993662563647528781471683481168663491494543415440108724581414427128541879423128643352031944424409002346677086278423982228310263366498503777070942034259760994677516479525171616976416224427171722881760343688181328166511665702243431131360846467540550477319668112406853448003167831894317189530542922888994216918945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_48 : (-59398169207 / 10000000000000 : ℝ) ≤ oddTerm 48 ∧ oddTerm 48 ≤ (-593911740443 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (14981775630353254148881654406539694239679062439450932096028314856687241319059712653680261960974395372215711269724019633163845382142211480665706871619251357289121451811737773962861002597197072286595149380190357655938302700118545884540788213654947327855722688634922588996726837988840704015024615174078880565699373339746709067130084747679070041402095518519810150884663371647420506667128914320508283666228263476989846488278721462580749692786448079796809163192489578947771917167360840946336960876469952778686330437364574670130968331289463069279 / 34921234339214415519254233331439389863148776228894303814203262308227344062879800410504814909203388896616750894654038524007682133640273913000714304194165781438733540217155921136555400196013233043839256874540483740155978758147301902987638081411770520070564503329070599654323656354432304214424764353124418575165368705583605566078348426546450449918637947550718051567178636478479426675346945643621078593820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 48) / 2 * Real.cos (169 / 2 * Real.log 48) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 48) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 48)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 48) / 2 * Real.cos (169 / 2 * Real.log 48) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 48) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 48)) / (2 * (169 / 2)) ≤ (84282412526599677739445605757539315363616476717924256871040938391754248137443109387320983481837205303776572975228547637237635914191775001344385215895560278253343847418174279762720096834829215816772759708326300705909621607341827257201484430421803574443329242129208606350426238247436791836856003700362165760401238721549975653361446192824668793362561566200436809148001317701495246335261461439858212860109034776046438511001098727813592756576391531692854785435663894838180652555441584483398143190968573504145041453753383167929270894219615082153 / 196431943158081087295805062489346567980211866287530458954893350483778810353698877309089583864269062543469223782428966697543212001726540760629017961092182520592876163721502056393124126102574435871595819919290221038377380514578573204305464207941209175396925331226022123055570566993681711206139299486324854485305198968907781309190709899323783780792338454972789040065379830191446775048826569245368567090239257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_49 : (3584223212883 / 25000000000000 : ℝ) ≤ oddTerm 49 ∧ oddTerm 49 ≤ (1433974833047 / 10000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-7890765687061213668160716190610273723265772654621188419769248507291168187194430476348558794350973265678081461391293701127721159277803604826653456929497517954729812750467089590032328385278528537384243618860997238901180988406971236110914687074166707042156144887133155845904869952141641766153998743885089643988118700947191141819895714006996323117906035465505392111779579450652412013694739438257782038647702603568259770026267189723580562215545786118892734108666299630958779258794529985008750803503462869785975738403069615162439523003682543327017335838182233995703733949727284699 / 31828195498012673473689876609210448209587547516619676872166135056810469807588133437679336066863186153654021578785502962922544571802673910217379761180264135873067602415843517340174193387379169370840977793235267900211950145050704285065415035485470851559701245921051466813353434854618361103325985168347881855943480684677863771453703516449948607150986415282098636516760642344180420962704181542966304298915977637313683545982505083084106445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 49) / 2 * Real.cos (169 / 2 * Real.log 49) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 49) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 49)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 49) / 2 * Real.cos (169 / 2 * Real.log 49) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 49) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 49)) / (2 * (169 / 2)) ≤ (-3506308621147408160796393168767178937629973251665355622499120161583777934500328118972473087897929007773315856432155633687710160134758211390190207122294516925792438402515807986801396861024908276734125881961466889251362723616045858085778284057595527574025169609773227884394740774459548168635909377629844452157547062587595261503728101989834347554635348338850213197034168128327254553939650303079671228590522319475171085151693302296689732281608924255858872879803677897796479698830637661539521621853528835061762022716813003190021410549752610285356353695291 / 14145864665783410432751056270760199204261132229608745276518282247471319914483614861190816029716971623846231812793556872410019809690077293429946560524561838165807823295930452151188530394390741942595990130326785733427533397800313015584628904660209267359867220409356207472601526602052604934811548963710169713752658082079050565090534896199977158733771740125377171785226952152969075983424080685762801910629323394361637131547780036926269531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_50 : (0 : ℝ) ≤ oddTerm 50 ∧ oddTerm 50 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-1194833289860215615591489495596982922821355628174369965590155308362863057858406968529926294023042629738299898453176934194122399616533398609940358898825188329708086521247303044010104131855730856753624731656548568514726046650868572090685280304818578734998141409570540158125735214824405744766425379151477736554577411675470231539148249793380035487798367870823599067744003183283582497232419123179869763927599381388197962906058573897684432247036977060457496884142555679432240167529891620496455089021695214573570865345924168952648129807783709601161077166907740281316269607177 / 3536466166445852608187764067690049801065283057402186319129570561867829978620903715297704007429242905961557953198389218102504952422519323357486640131140459541451955823982613037797132598597685485648997532581696433356883349450078253896157226165052316839966805102339051868150381650513151233702887240927542428438164520519762641272633724049994289683442935031344292946306738038242268995856020171440700477657330848590409282886945009231567382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 50) / 2 * Real.cos (169 / 2 * Real.log 50) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 50) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 50)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 50) / 2 * Real.cos (169 / 2 * Real.log 50) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 50) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 50)) / (2 * (169 / 2)) ≤ (-1061920169217706371348634206317323587409007709293708009027314067583122012856698762009100000840317750126861624454068512280818669901922662018945575218928281420308461730256457142791898230381386233496494135040154867642906556926752214312728754861319175678100466745485658946765137563774669859596252386634076142277786898443791499511316876522857666767357922211745773350984362265898072223061685827683581344718568160382863480493587109846424388678875978279318852273811116137858742156178293721532221321617136448993051639349685166767490303638263661328236379104546985155636773381017 / 3143525481285202318389123615724488712058029384357498950337396054993626647663025524709070228825993694188051513954123749424448846597794954095543680116569297370179516287984544922486340087642387098354664473405952385206118532844514003463250867702268726079970493424301379438355894800456134429958121991935593269722812907128677903353452199155550479718615942250083815952272656033993127996316462374613955980139849643191474918121728897094726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_51 : (18863513869463 / 100000000000000 : ℝ) ≤ oddTerm 51 ∧ oddTerm 51 ≤ (1886636640841 / 10000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (3963155778988690235610014340203073459647598144231129948927768793192164679171034295990078282538270421611127503127710105160523394463507022957670754312217391295732960425529996778989057438945784772096875126426704054036998135800374618906691235672734914819764370343941059103091835335854352838489471521648414294457852555702469930096230400416758501660980483249569775301525685243837815995904062985524651553883676565496464183182060647424812265760877077605158674509460348130684743590594987405579323955142054276316720769214549353275065008492477310093230893236036386470360102433 / 12500668074317543176427104858870261408449701233899672726796336362394517992696027674090695347519638411447636939084307810299646845181103243952670233381576624039686399474952898417347552418996975619931558181780912536168181955263183550100511218720228469027387220844161368389932774805381111257001633090638693229302133203057751182535311859304912165850143253898043598689062572307895897271042988991780097178317776830349589891076416253473280896735724220275878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 51) / 2 * Real.cos (169 / 2 * Real.log 51) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 51) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 51)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 51) / 2 * Real.cos (169 / 2 * Real.log 51) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 51) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 51)) / (2 * (169 / 2)) ≤ (8918448944350421904995629647798035235213919013902830629868693004208050505945528849229330731856057324498979484728769666264426640305064883169955712810759161224838055806190543328049750390527647438516181788432314711760580574885465885429627439190646670940226799811308614514805303345008543047038443620289143829675720347767526737825780179680099015621352878691945702338840706823699058691101770634519377492755107492978647796152700160316289360330545117393401421267053021944521561704064615727017345730223373582254436049998239837452028077841937190971812512192572826588031517582192377417380207768416191 / 28126503167214472146960985932458088169011827776274263635291756815387665483566062266704064531919186425757183112939692573174205401657482298893508025108547404089294398818644021439031992942743195144846005909007053206378409399342162987726150242120514055311621246899363078877348743312107500328253674453937059765929799706879940160704451683436052373162822321270598097050390787692765768859846725231505218651214997868286577254921936570314882017655379495620727539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_52 : (-45457983643 / 1000000000000 : ℝ) ≤ oddTerm 52 ∧ oddTerm 52 ≤ (-568125714449 / 12500000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (113475748121304339099332011115004784402212699891157200374841721671568352895711247892379583119893829964329118007286247258174460466054191340833464329921463992436375390329574879376499469649792018729582012291330990614486323396302564050247069201502345935311009291810774312875394317292222083437065781414713519131273392582563429258296520365658585212420430294192942672386350075108372603373961303089712381302557918742519246529998775658117224379477219821639089215975380314235164056503897205378854340345448656948029292195432040299504016865219219412051968604158134734225651119623353163783483872211458104081139556671 / 419996314445487235674556398083920449083805181337958093061436667633572568607940402653554406125825424568249657785464003817231935971429573639262929439830381031634608828163844655031266812178015688932897107732984596769886744467533724718509352744083262781619883661025891058551502096592006460088205178309687283505811522650011367935146320772685876977686275735326326960183664022877104652745717576976825810033855995348376537522938688376641602762070586728542108785058092889785766601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 52) / 2 * Real.cos (169 / 2 * Real.log 52) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 52) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 52)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 52) / 2 * Real.cos (169 / 2 * Real.log 52) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 52) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 52)) / (2 * (169 / 2)) ≤ (127682480500456913715742349157495243404442109183756242839595501382400491412963922533264841524709783284457456229713256304724598606702608831363763503549552494376084386901103322118153244508148601507336926520708306940805745416459805726002607032182230152976134869015085067349301184783587337436831616272561926185168143737369624263157123173742152934105163696486237815140985749811853347207103698202698324175731307358433434183493908217659227291757400404236630228927702888982437155540735843183865669626181172200432792481695600780657505070822936157767663109345804395563136699333621258725018942949767355499280750123386556427943 / 472495853751173140133875947844410505219280829005202854694116251087769139683932952985248706891553602639280865008647004294385927967858270344170795619809178660588934931684325236910175163700267650049509246199607671366122587525975440308323021837093670629322369118654127440870439858666007267599230825598398193944037962981262788927039610869271611599897060202242117830206622025736742734338932274098929036288087994766923604713306024423721803107329410069609872383190354501008987426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_53 : (32194182727 / 625000000000 : ℝ) ≤ oddTerm 53 ∧ oddTerm 53 ≤ (2575894638643 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-139662518158640847296047298955812587907060571027809406707798928626886782924436440033504943319404790805875160773832813232848558062127814651528075674368814038818214434276055616233310056026728004746513329363729499189805768969040881489542009860369667436334829904769480731497041534640247198782652939226168942679469939727195972487123106214432884320922917934267036228031013088140539268401842120440599099231142038788428485909731979371596283149812224209986078931996841707145635807341131002908601389070411799047861748256265046081766291726741916034574816529509097717396006512166483432939660753909365044012916254208311887 / 419996314445487235674556398083920449083805181337958093061436667633572568607940402653554406125825424568249657785464003817231935971429573639262929439830381031634608828163844655031266812178015688932897107732984596769886744467533724718509352744083262781619883661025891058551502096592006460088205178309687283505811522650011367935146320772685876977686275735326326960183664022877104652745717576976825810033855995348376537522938688376641602762070586728542108785058092889785766601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 53) / 2 * Real.cos (169 / 2 * Real.log 53) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 53) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 53)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 53) / 2 * Real.cos (169 / 2 * Real.log 53) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 53) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 53)) / (2 * (169 / 2)) ≤ (-62063554764232640064233200946562604077790583086266273018724823943971542567714977826693908012687978331604311413887443964145254625661895795869671481173907135113679141215961747726719884000186001728652798605900640911332260972631156341142687005471038924344830001500605363492240336203129299028720022040672496609613541775492013569614740557158406467416856132394083800666491188335093596040681289093698214948938201937759001163466050646761293178727546418916577492096973631065294169646528824640021628085017487092340547408998813776415618374799523173482442142484898780186575715594045747436945623041 / 186665028642438771410913954703964644037246747261314708027305185614921141603529067846024180500366855363666514571317335029880860431746477173005746417702391569615381701406153180013896360968006972859065381214659820786616330874459433208226378997370339014053281627122618248245112042929780648928091190359861014891471787844449496860065031454527056434527233660145034204526072899056490956775874478656367026681713775710389572232417194834062934560920260768240937237803596839904785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_54 : (-287398512539 / 25000000000000 : ℝ) ≤ oddTerm 54 ∧ oddTerm 54 ≤ (-229875567791 / 20000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-306124791941283234612696725930981122177054239457935584111534164865012997022635982387060619955440631307037418377284197059980883455345701001066806399224329478120895063827043113024419839111437249439451985408518590011493506857231975861389463612557321658008611003638111794839420153367129690168423791052855308170346596674945284994185344609313955399445332002149652986904092111730959974915544967345549790955207031722301517181292385695718786529806260775459087453197250503885246652911307449090374849967692794033279571094220187794980296098975541883912301806876820804589187637939204897485037458050604910040138691069715530188029211402217876129 / 1260675537136925180695192544230801189261047381767353837196954635620697932649401779227969152760045669615354193130504625175782785537045525471651513739828425575796020536516633954855679411464598485646361999011916684214279912856286737832332981263398909456287819257721535743507381885236181274702231806606953052210439156351651717902157370086445619524033184789330367866360182805553496588583330770719158972022216800126882297739384233785537693860385045013103094656925138198645219376471163525857264176011085510253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 54) / 2 * Real.cos (169 / 2 * Real.log 54) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 54) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 54)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 54) / 2 * Real.cos (169 / 2 * Real.log 54) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 54) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 54)) / (2 * (169 / 2)) ≤ (-544119499935922242602857984877190497601429469184927431418434711308956899037443615361425428972315974438930429727921332763435904335584647845129536399029328059620722425039223574040192968934035933188899083347562711296327754988272244368962884690332997399115444144096728235654059309680081970906585245987276457407359951143237125673877483367710550538479212807711841536815889573446354453681606964702564058439742701103946619234358160681928745794170851511172552517627732436921138721181231043765132162931258662654773148906125975510321202692048384947724643321968062243412897875087199941419282885244273475381934902094477332207961871 / 2241200954910089210124786745299202114241862012030851266127919352214574102487825385294167382684525634871740787787563778090280507621414267505158246648583867690304036509362904808632318953714841752260199109354518549714275400633398645035258633357153616811178345347060507988457567795975433377248412100634583203929669611291825276270501991264792212487170106292142876206862547209872882824148143592389615950261718755781124084870016415618733677974017857801072168278978023464258167780393179601524025201797485351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_55 : (0 : ℝ) ≤ oddTerm 55 ∧ oddTerm 55 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (311362161545845173554042371592778615836556467866959603461834282827315742734389557897348728475348819687285645369426287944131814702356764200453882090674535721828431962693060973377183341402011680285937402130274958484677537701336288731106752284771260024038612243648307360137864190588956420854001661573185723114184292905660031039874137940956956075097025216023889678644314345646156531073773890250498569705494219538907223580182876818428530705342687057840084769495662800468588991889620854298420026687637891871991062779951905058514932995757677011670875620613626249517940698969163128938227435038452349901381964837514717933 / 988270664236566208755728956155377581903311629434530365736027044452682918548672540108810196199127940598552912008318244216516207525972019067935791063475276590389924173825631871994229438899550733887596443318987556695118863665192941101589118228958789517154889543160857183406367667916321833303208370222096752898021985041723978707393269496863358956225523175677139814955487964879052525334026567022963552523893873757842425009129152488206132038601290532642097034227852465090556637259842311718069560252026861326031526022717343948897905647754669189453125000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 55) / 2 * Real.cos (169 / 2 * Real.log 55) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 55) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 55)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 55) / 2 * Real.cos (169 / 2 * Real.log 55) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 55) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 55)) / (2 * (169 / 2)) ≤ (2736971120583612480434702246346687611862141029204575567527344362716444608073106545855331008538990024583073947349543725317848336540257325986417339334621021766378620344941869392687714942986388413821106165009516041714902856614915878364068549785454852241558446154561894739320825926635173659281793834450727212232025257072639164883301423813718519484012481012514380949072491047683353118456460403506806914742463255263460723478689844236800616273393217093381608657623612842065302234270683872979721757523335026439189246004091202914091027688215588574605124477665298571923281338302462774509370504325173490472591149458201264204566000310757996475011 / 8685972634891695194142149028709373278447074868076927042601800195384908463806692247050089615031397915416968953198109568309224480208738448839279413643825673157723942934014342624949282177828082622058953115108289072515693137682359833900685609434208110990619146375437221338532528331295797363016479816405147242267771352905777156607948657687275615826200887286224861654882218441319797585943592874225265598354535999824786938556799191790874207370519155072049680964893234556459970444666582817834595744402579835873323959184039155800860498857218772172927856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_56 : (-1185330048893 / 100000000000000 : ℝ) ≤ oddTerm 56 ∧ oddTerm 56 ≤ (-296280624423 / 25000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (71901493138833241162491045960345273274328856089145129424470421972091376611375312744125001511130138699842103349595026127450090603523148062168707364292222120613879113031627407490256097002135788705021977970460136550133937164496935632368725429203465859155667385343626247394446553370476322620857461347503763499655296984375791046846344120546534202617065577679685215648062299146895333935811269528383927408873676546422964445423562044010804399288709378256898384761995556243387692441162430644054813071730263593008016292581233205215632456603549097011900033484107908860051309040732402404261329041580204631926192083385560449148257570168959041839 / 284621951300131068121649939372748743588153749277144745331975788802372680542017691551337336505348846892383238658395654334356667767479941491565507826280879658032298162061781979134338078403070611359627775675868416328194232735575567037257666049940131380940608188430326868821033888359900687991324010623963864834630331692016505867729261615096647379392950674595016266707180533885167127296199651302613503126881435642258618402629195916603366027117171673400923945857621509946080311530834585774804033352583736061897079494542595057282596826553344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 56) / 2 * Real.cos (169 / 2 * Real.log 56) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 56) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 56)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 56) / 2 * Real.cos (169 / 2 * Real.log 56) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 56) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 56)) / (2 * (169 / 2)) ≤ (10112918196216408155550589352338598845127289385936657334552543471709395264603644304450878909918393576751170415595654703928306448130651670697220041953019528363099892104077438549271060146848646195280873337162928495056734667506854240730683198147133935713070228273891424702481993630372128464381203147176237988579646452911412528417310458395425677511202398812996929917617247750855336283771814588386194641859911054412376459342926884507331122062941320887414554677949619837380905418953911179035422776640076909076837560252458299312320448284632454050786851469649586031133113074051897646409238918173395630328801481106663512978774459271834911550899720391211 / 40024961901580931454607022724292792067084120992098479812309095300333658201221237874406812946064681594241392936336888890768906404801866772251399538070748701910791929039938090815766292275431804722447655954418996046152313978440314114614359288272830975444773026498014715927957890550611034248779938993994918492369890394189821137649427414622966037727133688614924162505697262577601627276028075964430023877217701887192618212869730675772348347563352266572004929886228024836167543809023613624581817190207087883704276803920052429930365178734064102172851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_57 : (-781 / 100000000000000 : ℝ) ≤ oddTerm 57 ∧ oddTerm 57 ≤ (797 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-246375861034762506360018636852223624067103879224281170246623262109974927320746452754212038677454104390615002385185471483666076641039011406655618028339159470656997426520267105819566813468501811205288288018253628961670507106654506509849060017423239579494310045735948332869758651640747722257314743523167725949445899826859212681733324880413995707401324126302489738426648286487682361174018073682479410124802511123158101883706762536199610100837474146556045874657914392120940939212668019086783558743427882611272597680733500396362572981563552650652238423885374370301831984020965904554626666237501369785449649961183313362950858724030016466466480084885778712470570251204082963837367 / 911790891236600498981152460631165852636750726749123304179715363013121433637015957379215210704838768307231685945265497976261976836803729957523961224501282821348324854442714595172730435241961112637690855116555317467326725583933162317748362654165434029596386070486349044898645541481534080244609668639239350598569086191799999011935329712328565923310215652441672400484440346352044954811281583553617045256245445696397760769583585488602148491955277393455860767867391824596909989252540304272083337719816071907432589569814741483791876817122101783752441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 57) / 2 * Real.cos (169 / 2 * Real.log 57) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 57) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 57)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 57) / 2 * Real.cos (169 / 2 * Real.log 57) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 57) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 57)) / (2 * (169 / 2)) ≤ (-437931714284152005033806138657785885667044654850902084216988357163854240907466300100022011126219497981303129507347499406289813193680598426029929658820423316034636670099193038329621271105716492630388936502279657987478655150612525781433850052721673558553279102573929944809797001938488836726339958475272739400836343484079199567898093954978439735625645700350603319204941792698959504951378791956745403595233347413728675405369916637816792111714331651597554393163589334868753899836956630520163110719381574882059817788979180194368290775876419605319590199462251802667675451585833101266342232527370790259352583682974220815955032975429093579354089180954691807 / 1620961584420623109299826596677628182465334625331774762986160645356660326465806146451938152364157810323967441680471996402243514376539964368931486621335613904619244185675937058084854107096819755800339297984987231053025289926992288564885978051849660497060241903086842746486480962633838364879306077580869956619678375452088887132329475044139672752551494493229639823083449504625857697442278370761985858233325236793596019145926374201959375096809382032810419142875363243727839980893404985372592600390784127835435714790781762637852225452661514282226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_58 : (-839 / 100000000000000 : ℝ) ≤ oddTerm 58 ∧ oddTerm 58 ≤ (911 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-127777864565006097250996559550683295820964092904381690045681549918171690863213269547069048113193532415955206153232143983855564512637343130367582759458437238175380695342930576802712112296158073778703640713449463224576749446728377800135315732055909657346216160202660470317935208860669084460209709625522700020793570644156481442449679026204641040508227082730983039557871608131062742811648080211029385646600687371952162893222049804322648085456905978974878950219613877010611243626079129935315417603755355824076369131698522882764847609697928362457020514205928038872580623973736126165153326777959431642300418130613049554944058348187370354920023898608336228337102732029097 / 445210396111621337393140849917561451482788440795470363369001642096250700018074197939069927101972054837515471652961668933721668377345571268322246691651017002611486745333356735924184782832988824530122487849880526107093127726529864412963067702229215834763860385979662619579416768301530312619438314765253589159457561617089843267546547711097932579741316236543785351799043137867209450591446085719539572879026096531444219125773235101856517818337537789773369515560249914353959955689716945445353192246003941361051069125886104240132752352110401261597871780395507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 58) / 2 * Real.cos (169 / 2 * Real.log 58) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 58) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 58)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 58) / 2 * Real.cos (169 / 2 * Real.log 58) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 58) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 58)) / (2 * (169 / 2)) ≤ (-28390895877889340176515344284707816331556451464493593631327883350812180018436972501292091649986419873574316691728322822825325365854457001965808037753952963744283600434370185074993785665220827333217444723906368341286067777869714055501247115585087500290085388649995236016734691669193692847977204198215197440379936366973951351674675517646538863367317367482830858437918001828068283015724760702478334415385012858432326147587870270151450594230566579278381804312910949392162410743230464582631430912523943149429412110130273092833373180254436081347282538406638659013723023080457939411168016311645559149281660133396050662319265979662131743582090735021435991432027607951301 / 98935643580360297198475744426124766996175209065660080748667031576944600004016488430904428244882678852781215922880370874160370750521238059627165931478003778358108165629634830205374396185108627673360552855529005801576250605895525425102903933828714629947524530217702804350981504067006736137652958836723019813212791470464409615010343935799540573275848052565285633733120697303824322353654685715453238417561354784765382027949607800412559515186119508838526559013388869856435545708825987876745153832445320302455793139085800942251722744913422502577304840087890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_59 : (-5145413812419 / 50000000000000 : ℝ) ≤ oddTerm 59 ∧ oddTerm 59 ≤ (-10288615555453 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (1464114714485762035630699550986208470095400143855808426996662129930818925004965090988083215978513306623674531459725672664860914378481043906633355977445647934951611410662053670074801310561830109750837567811862334131572308311162921521792872439672457345417866030528894402238707310738581434345313032187400898042619931946798377807897548585632975632503693689003425358379132754166103220388600954233280255403011782455476014707509062895562628113333871824021207306266601961214797527615202640228695332680304467920027886377978430296697100371108462525692783083513897209555260244130463765859140533678342293951373340976182425194362460793806114660013411402407 / 7554228508201952433142999881945958440252314311519515794991006154957802037707596203653277778015107289414508818344633795997683979248421198569407566735349389714000127072174806118303928800902910543369318132106248759060697984046603848774283908096428042690513067616760840976621370052776620876851925553801947980588603876524664697394086718328372451094130826176590056920575782878944726048681042155111644814590521082204807730542039527800861127562275531441938746947376341727356282381356813448631340704654963811685199289210927900176660156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 59) / 2 * Real.cos (169 / 2 * Real.log 59) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 59) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 59)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 59) / 2 * Real.cos (169 / 2 * Real.log 59) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 59) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 59)) / (2 * (169 / 2)) ≤ (131798655113869561915406527719694229693284556300314735642189050124211639509369606589232324467873880695482566053075376146381481499003990190413328640088509507963262501169638862057041637950094328665465581682881599189329476804866470401289816803773601613152083922779997191848085259071685312878817242839786392947119116643362971734902950515388341724111407998464061010029369207806476827954350851754505672605167461512767019354056259958546566984880890092997490221567493236266595902904057601030364676289460046332629057463297614905895986477045315320465795094492142696434985572230125893025280315527360523835283100275184397271167967444959348738040829395180060308217689632066612927 / 679880565738175718982869989375136259622708288036756421549190553946202183393683658328795000021359656047305793651017041639791558132357907871246681006181445074260011436495732550647353592081261948903238631889562388315462818564194346389685551728678523842146176085508475687895923304749895878916673299842175318252974348887219822765467804649553520598471774355893105122851820459105025344381293793960048033313146897398432695748783557502077501480604797829774487225263870755462065414322113210376820663418946743051667936028983511015899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_60 : (0 : ℝ) ≤ oddTerm 60 ∧ oddTerm 60 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (2157859173752555235462685301136433623006373424224557981686579878661664497930692488170382291534623416693109903972656292886650047244080193282503863644588223569344938308791574069932817009991968167191687243970817987141891116354916677868745431410187366617055193234777981684416898866149894227788531639580261686218279655223639849404865352421246370566243480451190407119287546932912300109580826850124876636477092818948917984058875597354089834058838834282348961159838421839785694845993985430548170776216631961584955330042866738990862616091319136028302455148469822346280762720573610633078739238121876158941422028740042224826960514171004098191450319822525556927197315530594819742207 / 6639458649786872255692089739991565035378010625358949429191314003380880697203941975867138672083590391086970641123213297263589434886307694055143369200990674553320424184528638189915562422668573719758189764546507698393191587540960413961772966100376209395958750835043707889608626022948201942545637693771243342314202625851756081694021529780796099594450921444268604715349809170947513128723572206641094075323700169906569294421714428731225600396531228806391476809217487846309232561739386820086139291200651787613944687783042099764642715454101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 60) / 2 * Real.cos (169 / 2 * Real.log 60) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 60) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 60)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 60) / 2 * Real.cos (169 / 2 * Real.log 60) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 60) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 60)) / (2 * (169 / 2)) ≤ (2427897923312225452064551207445404652399163771888610401390481229674672746569449724813186648946466094200780240495609149006381230686744359604769214421559657788591796710975104041385850988020341009133339861324073799980365582189972159484970019076939083255984882636429165731820063180101555912314911268819821400965892812816354498532640491186563630092399817209937229797917306373690633131825664295752958375295591992125090066310543586855093189972389073874001526535686302127617412890823206118792070936446231198312358961612601024234927371596040747022264004139483325773888524231409830561842772218869529037470397102413743606434065456622520075061012229091921785691172240078851656838297 / 7469390981010231287653600957490510664800261953528818107840228253803490784354434722850531006094039189972841971263614959421538114247096155812036290351114508872485477207594717963655007725502145434727963485114821160692340535983580465706994586862923235570453594689424171375809704275816727185363842405492648760103477954083225591905774221003395612043757286624802180304768535317315952269814018732471230834739162691144890456224428732322628800446097632407190411410369673827097886631956810172596906702600733261065687773755922362235223054885864257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_61 : (-4319118518741 / 100000000000000 : ℝ) ≤ oddTerm 61 ∧ oddTerm 61 ≤ (-2158504832583 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-6810336500560531846472017891856165767186634529604974739838656538252025909549361817998104424919603263877767373961113847222527276661680089656147739613891276374504197582307424069681974118955578541169667551701525320804838975076612797829414974687636130176730686697546271638847320139192874738347747643049631633763166950148060706989836245643402693104655048246550371583184198796052854353633914704713912769306918286189532086261144651330859086275158193121117579273271866597239388972002105026808697427708832391169000535566411570635662260329501766825859438729133149346449358320118199453615813285501943932332458146799471453560198568488695213004662045748853912387288328905067 / 82993233122335903196151121749894562942225132816986867864891425042261008715049274698339233401044879888587133014040166215794867936078846175689292115012383431916505302306607977373944530283357171496977372056831346229914894844262005174522162076254702617449484385438046348620107825286852524281820471172140541778927532823146951021175269122259951244930636518053357558941872614636843914109044652583013675941546252123832116180271430359140320004956640360079893460115218598078865407021742335251076741140008147345174308597288026247058033943176269531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 61) / 2 * Real.cos (169 / 2 * Real.log 61) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 61) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 61)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 61) / 2 * Real.cos (169 / 2 * Real.log 61) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 61) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 61)) / (2 * (169 / 2)) ≤ (-302533834939706383212349739289794835572325028901811591202692755084875228335831530756327088270350784961773626396071347327552818254839372346817594173078563457015309807604228859511402330759600237213948309292756430616540318148540762215719904925661034598218456670026672416762865485918539477892355831404685297190125488415844557338102056234565203467013545063524332062497361115189658116531720821893041552341272299572339187850778345810851673020662747195214529267719742047649603818483598899658196200538318187058281970495183343252776388853629166126844918018199801473240659951640907420029145406586716803299578700955684157430609444008498373736407754987 / 3688588138770484586495605411106425019654450347421638571772952224100489276224412208815077040046439106159428133957340720701994130492393163363968538444994819196289124546960354549953090234815874288754549869192504276885106437522755785534318314500209005219977083797246504383115903346082334412525354274317357412396779236584308934274456405433775610885806067469038113730749893983859729515957540114800607819624277872170316274678730238184014222442517349336884153782898604359060684756521881566714521828444806548674413715435023388758134841918945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_62 : (-1353 / 100000000000000 : ℝ) ≤ oddTerm 62 ∧ oddTerm 62 ≤ (259 / 25000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-4083684191389777769264948613225115918542740350994698388470131348537877207427766152162037155136221517957781200043301378023832504620385817048813990416237405276045786153991158235904443373905275778268726845513620686932616255636183864395309751084277009414541165971229903264003160125076026598701118843060597145137033475982449253791354521227770104417520649093206760934344909600365296155504332973396892111315963998143259961811551482869551138860037929641739761746106794047082110981508848124144011765695218646849875395054389434492557051696010443670079685327558823019692302637652549153715948589817503109137084376336426471133111194237973235153743630832881581918568451153 / 12077104929243200341610808645767183471212794075397959075765018503044995117677793997913138213486655133396144521835982772724654632631987067825581778744873508100355000687211282984054491721815018026533270612247193091012725904039981130994006827859950516351016178005090674359250671883179533219928339701748415504542577083796925001832317374975529855136211920479160843961562585120095742474811363002374662892768720066499680423333692358448798768943618104106265449098314071027396917200784422348235492411187172888483373185923559685333462249134939270334143657237291336059570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 62) / 2 * Real.cos (169 / 2 * Real.log 62) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 62) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 62)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 62) / 2 * Real.cos (169 / 2 * Real.log 62) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 62) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 62)) / (2 * (169 / 2)) ≤ (-453690294610819077459767840616944068828790319349014946476654155804970830901459104774317914642320015013207001484588400526090637450261618350030877656120812391275734332562812133577793387023041845595917013451957959284250473321117403564311757108936505182488032786022073290121479787230647237166418153244968614520388864473154506798412340307228971766263563562817952979712182052734280180743226439837230929654678818230507002403568921129869576170198018505346137229195754033769151164181188539143880308819047780936705592075954600345538830490234426551384520506017868742660332332229269482425944548117380855517340871830449942057254489476716956161466394198138420475953198103 / 1341900547693688926845645405085242607912532675044217675085002055893888346408643777545904245942961681488460502426220308080517181403554118647286864304985945344483888965245698109339387969090557558503696734694132565668080656004442347888222980873327835150112908667232297151027852431464392579992037744638712833838064120421880555759146374997281095015134657831017871551284731680010638052756818111374962543640968896277742269259299150938755418771513122678473938788701563447488546355642713594248388045687463654275930353991506631703718027681659918926015961915254592895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_63 : (-115776005713 / 12500000000000 : ℝ) ≤ oddTerm 63 ∧ oddTerm 63 ≤ (-185117812933 / 20000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-431708151351320053480411504587386572789836372433974262470900089284292977383000181053100445667916034294677097567030146817883816351822591053521829781530306140000017959506495144797928954948180244443256059402137322613688214902077964822831023569007458176402696349209925251951924137730537411783506352194983047720151785757735077517630411434449503420537086170450314157225348511391741967571367300932314097122087640212639118841557372879972834566682510456911423012788586109446404363976898371572894733700258266212817124878098358412105187868593578855168310386575187334453181555543505078143785256912637492241480209290263012245634006126525134459510061059483974738597109414321322483965939611 / 7469390981010231287653600957490510664800261953528818107840228253803490784354434722850531006094039189972841971263614959421538114247096155812036290351114508872485477207594717963655007725502145434727963485114821160692340535983580465706994586862923235570453594689424171375809704275816727185363842405492648760103477954083225591905774221003395612043757286624802180304768535317315952269814018732471230834739162691144890456224428732322628800446097632407190411410369673827097886631956810172596906702600733261065687773755922362235223054885864257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 63) / 2 * Real.cos (169 / 2 * Real.log 63) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 63) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 63)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 63) / 2 * Real.cos (169 / 2 * Real.log 63) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 63) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 63)) / (2 * (169 / 2)) ≤ (-383484126974990622254378518514744546578852496940480422854951909981460132951647094314985910887835874859349579274085976646949112460948770428329999780408919466832681788835617096818865164783542749088226197512653933027324889004435320285244251396845065238156054030897476886624828953721353690060818813325794149758490509471147135903027386006307137917330479863065903564716553960244676070595775751666564501868852975241807214377972641230379718340015334311486680858016108349118986299515062601926809635489725505220797005954791666886785788666009635129081446662387513300321085746459852124544190621242911406928618243548542420749464609302086638716064222884707393098777535854279311 / 6639458649786872255692089739991565035378010625358949429191314003380880697203941975867138672083590391086970641123213297263589434886307694055143369200990674553320424184528638189915562422668573719758189764546507698393191587540960413961772966100376209395958750835043707889608626022948201942545637693771243342314202625851756081694021529780796099594450921444268604715349809170947513128723572206641094075323700169906569294421714428731225600396531228806391476809217487846309232561739386820086139291200651787613944687783042099764642715454101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_64 : (-159864562151 / 3125000000000 : ℝ) ≤ oddTerm 64 ∧ oddTerm 64 ≤ (-511500590403 / 10000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (32883765695680999647289900019800116170751916148222492885820431956294218305743892021431918818821922660595372092506812263772696583093313101765526790346374808628080010027492237085460668023930730520094042948510807617122886014175540062601810084871531565765400812799450661529787910149950734871914319582619171692453046837532068020529204171783848024256835093200342168901728000876871050056921980720720180907447430380650046504771452540401956686983539682568677864561330473823043478318356418204984979923674217954357362673610015278854833905981544717189674514693350950371202943564885931375909100173689442756920825626294979291306339434813051735403811253414612793887009849713 / 111433298867353344720558706593039040605064939374093067033247646030270228364771529883768339352999693643592323643444111929467276760282552974369763545684529498817395165464368092406051712116812442315857049422584487571012070833474738681216609380390681263430619327855401421061928202905536985142162946186264523292509518152694180526906304451309070182656686074443700335763240051937293938285013874243436475201409212572264805720775156435251576496492029924708338257087434121244015811600144748481625842071277293385729121143316243779226664605596451148986816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 64) / 2 * Real.cos (169 / 2 * Real.log 64) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 64) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 64)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 64) / 2 * Real.cos (169 / 2 * Real.log 64) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 64) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 64)) / (2 * (169 / 2)) ≤ (73998020829718481363420656896065955213617414547471308334954015428931971622612039269141055031972388848309514909468453076003078576712964132716777672043319241642929871629056176450302642980221608551716772035439651852648508287964526609576204974427729274979251357414066277565400462253883490121730769855987295479140522709651234998610738556038838013619346855112326465232270271836520993920909511833839570552750581198940571785124283519075827521800691279123828048219028395341276275879213493232167745356029229800595641276357384315177973817466091200249269647722267550617729733292087074942766203627738165621279696035839842909671595819451591804572950544523523760783567418991409485596254632227490351 / 250724922451545025621257089834337841361396113591709400824807203568108013820735942238478763544249310698082728197749251841301372710635744192331967977790191372339139122294828207913616352262827995210678361200815097034777159375318162032737371105879032842718893487674653197389338456537458216569866628919095177408146415843561906185539185015445407910977543667498325755467290116858911361141281217047732069203170728287595812871744101979316047117107067330593761078446726772799035576100325684083658144660373910117890522572461548503259995362592015085220336914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_65 : (0 : ℝ) ≤ oddTerm 65 ∧ oddTerm 65 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (8867484230569451286574570106260009893597425216409079798905681842358420575891502451620034437837682210880543403622395875292908293886725909999804646623958554875659506385099965577000814215849302437542259724444075560875254032773477514620448834846299409003136113225109619144212292628398246778794206946079109227692568047537424271176949831289927929549281857509215071780272173330550142951589453286984778281086487637287149545052949251859160791672970780422019559823386519489720404600661684846613943682939821120005799557704123106743031022023630666263000982331454669962984740841144165608576010706098188514264108422781537290587163436590341914641397261346034531300002522659403031 / 45043553298194272114034581477139016030101200713677853666517430016744372698777333378840452639350362670016217793876466881947545318642188542018736490186116901821917322888058492392419475281435023868696205246259215657730266213133589465326565461869775698962710047496189032269761488110629412057041087968077903211051112380702632446589957484243443380731124842570029244300304648453996252519578926085538306506920268201415054225546820588534229195927372398205923777151003224993480241553554251764833818043988500958515991298076083807337217717494726315630160229375178460031747817993164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 65) / 2 * Real.cos (169 / 2 * Real.log 65) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 65) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 65)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 65) / 2 * Real.cos (169 / 2 * Real.log 65) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 65) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 65)) / (2 * (169 / 2)) ≤ (1247225677991238124813130434051745345702900929348220823826079867952983437450088033600529267955270450391354851702576183416303987683051405704659243976160142195770831647378374814491355726188716654400839828825725993367681059024916438031096975263807188194513625673274112526022252941873382447108815651698249964383576123337817010248483105589834751250509780867341706048153566179709212555305171411798645792220668791103823371603194874868647204727495132818612298769260407544445640818737113054721374052379345343308466499356361715747186198901291784718029784361126926899055256014245941899076416155716896219335214653423659719206941648852676328326339951565507678537986591064240935267090985331 / 6334249682558569516036113020222674129232981350360948171854013596104677410765562506399438652408644750471030627263878155273873560434057763721384818932422689318707123531133225492683988711451800231535403862755202201868318686221911018561548268075437207666631100429151582662935209265557261070521402995510955139054062678536307687801712771221734225415314430986410362479730341188843223010565786480778824352535662715823992000467521645262625980677286743497708031161859828514708158968468566654429755662435882947291311276291949285406796241522695888135491282255884470941964536905288696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_66 : (-1521 / 50000000000000 : ℝ) ≤ oddTerm 66 ∧ oddTerm 66 ≤ (1033 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-3118697992992873239470878473657471718739132686961452629470281441423112157506461891804669624006805288673823693403613904315664958514465189089793067999083687705347644130310334512959369880274551441637521401860849504995756881516191927483317920572498658145090132485772097728721473448310146020624327536115616402091904606052153094998980381371065450250661924867598509569139758448455618242810138417600958942121871052149528187683264319448380652972842500987809862858067159231422941405751585578829738887520323258706891026589066165936937372234870290994593263062915744736664248202848718531369677529553208624556580035436725105891234004038888354831469821272801003834890418227504848339100905658372303948867436012287641 / 17599194183009691823666279504396139461616605640197354141335109847368272423097074862720825075141140965359919054779800301673427074651813637521345015172030989620822458492191025230019961468030093647114876187269161971043399349231606528661632800877875847758009843379151956388391411936468568268892684848296085450226510674443840393067115076593665292292654853513728387557179123901956342283891751059979861137869928633539223131676198980759748323770257278851220671647977422275962191551855239366046986251794792485403424587848879850806679340858317911743468015347719192504882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 66) / 2 * Real.cos (169 / 2 * Real.log 66) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 66) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 66)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 66) / 2 * Real.cos (169 / 2 * Real.log 66) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 66) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 66)) / (2 * (169 / 2)) ≤ (-1385801832057452479725585631876424889394920916894005794782793728231736855887806408641934352564049988046339623140819951534578009844928627332788016886926193184667510325253980241628888910806432279005475302397956507960048412471512851641908529787175391730171783714371586346870418118403931598765556844405380372120343034525879253511536589647995517579548977928996733230721391997147532895469528177092106001873419635102689432505148979342009003336733297845240159880842693372344393282454374978902797861325327038790910380589872983215325425256295318664766392089788540181243744271565512146120461433850887305354143786008381709938792384545689021185962113356425483525504706861847460164556665329 / 7821864081337640810518346446398284205162935840087712951704493265497009965820922161209255588951618206826630691013244578521523144289694950009486673409791550942587759329862677880008871763568930509828833861008516431574844155214047346071836800390167043448004374835178647283729516416208252563952304377020482422322893633086151285807606700708295685463402157117212616692079610623091707681729667137768827172386634948239654725189421769226554810564558790600542520732434409900427640689713439718243105000797685549068188705710613267025190818159252405219319117932319641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_67 : (-2078744152073 / 50000000000000 : ℝ) ≤ oddTerm 67 ∧ oddTerm 67 ≤ (-4156969371659 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-11017177130180169459084578804716504305563119553221091022177958628284443035894052687560584958238124020824573639369563226172341545962204979325498786344976139831532978559859389832652051335178766238627438947403488091868813951179334549072884664809422648477107459145808703165522072426932129957751453320528816149918716796617157318858909573798902797046381390039323463714003642457063905958241804225728569606048008573385274907223234914954838753703141605268410290434759312429544912947172757201114928794480941154273185664551466925247580841662541289032918506385638802645900140458991612620972912842207762064002236598148651228564334033629971478817975809045800575469722810532572890646000008234118143335395073 / 38670104406027154885985477426651673621716174502386764470707028473221301710906658633908062909245671066464665891850147147231651287076738949631861605602607154928564972272880670671430579397527061236336397872417592221530906773213979188953783009741426423296408347268644435423711598493217068950203653231119328381845360368651016488672860275718502839510227949615125851566067410917384541151129335825151062070514979907678957076436960651083431375471756716225826671101512890743080987296556922435161835025916292082185259104160136390932645036065639942795706088410515803843736648559570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 67) / 2 * Real.cos (169 / 2 * Real.log 67) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 67) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 67)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 67) / 2 * Real.cos (169 / 2 * Real.log 67) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 67) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 67)) / (2 * (169 / 2)) ≤ (-4895911992675855212148542139358659748109608756431376184433528006582315094953143302507197133196099961506270031104098140631457975877172154445641080695902383869448483895661541294115045380961734412078626529506069156283310556640116304731871740322277685618418388054395472537317605308084026141396554189260397712588035460895507589440070220445216764545152533681657792120258384385712809795153730188109948132849968856926109265510150197586518351298764597863375143688862168659482091585001707823679888856648368515203729533856629687130875600388817075906793534431701820765918919526670405741398658123947196792338219884855186970281498631836983922105468710867029530186219195950041065363869802152929319099652941 / 17186713069345402171549101078511854942984966445505228653647568210320578538180737170625805737442520473984295951933398732102956127589661755391938491378936513301584432121280298076191368621123138327260621276630040987347069676983990750646125782107300632576181487674953082410538488219207586200090512547164145947486826830511562883854604566986001262004545755384500378473807738185504240511613038144511583142451102181190647589527538067148191722431891873878145187156227951441369327687358632193405260011518352036526781824071171729303397793806951085686980483738007023930549621582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_68 : (-7532905627 / 50000000000000 : ℝ) ≤ oddTerm 68 ∧ oddTerm 68 ≤ (-14518490133 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-251508911767322046364143918027011983441064687741681796708311460917504078316105563603779385310163892685181431067387233540967540926086380562545841360564576494806825519132281716591040696753901647362176977972752880970060528383605615095343319534024010476704415517379858729233702300358358848865901273314302799575485451725276954524409440401438443053060500080908051835281211037730663697506436318782660903921803569171585701404752166041718270633724929455443430349645829035774058426656239632979516246764668748707719105084363876046697978395059118416540890454151582662550902065141709915079868609196855791841970730793087407343890388371906097217264268014425589794017898351652345296871815999630632126326903 / 262248429402853426689897172218503645980605567100604685266839114537362343417064470987332240866737678130863890868124370301863954583582485281249061452925667012048102296772465485781728647172899449573678913522797256276658167678588726053560268892018137093752769282149552649086585818774529818726967049364687285575665692604241377011941598006988544647286159597541814857083247958152835701165970430671868639258592257403421746666374787401553218420896787626314471239566466544210347407338846316427692566093724854072979458985460994404653897000228135462752998103912460692299646325409412384033203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 68) / 2 * Real.cos (169 / 2 * Real.log 68) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 68) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 68)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 68) / 2 * Real.cos (169 / 2 * Real.log 68) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 68) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 68)) / (2 * (169 / 2)) ≤ (-861766840061333043377708960778465668815400574751521724642500686372998052997094989196213040993664893379307325531182760555943658159373638259318998897080795939560806321773138068179750807301918011328703854428493513031319977093680706950500422502889967748102680831512278657687566642926632281833769893848788489317346269093756541103696465410495195073834932158384704339388848356531983412530992266435889923593099835406448622980895234135514750687619873106781510323587656095993466426109707264041027473046458191537845341693804275720795276287999049479705001159924142978152853210286275658920313104357693646304990124600319364377974118392980180524423379819065814256244084054015322164888489586351 / 932438860099034406008523278999124074597708683024372214282094629466177221038451452399403523081733966687516056419997761073294060741626614333329996277069038265059919277413210616112812967725864709595302803636612466761451262857204359301547622727175598555565401892087298307863416244531661577695882842185554793157922462592858229375792348469292603190350789680148675047407103851210082493034561531277755161808328026323277321480443688538855887718744133782451453296236325490525679670538120236187351346111021703370593631948305757883213856000811148312010659925022082461509853601455688476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_69 : (-14799273474369 / 100000000000000 : ℝ) ≤ oddTerm 69 ∧ oddTerm 69 ≤ (-14797382281773 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (102425541275706830165965055078127099487708682926607153324785904721966667669234304661800404296835557329102549156313382227636168785937335947306994140421873885139709605668288909721796235702273932791148196570626476298573472384531358720992034778996942146569833192259475015876053968530289638941916722611388272848989104364255217348573465616761711121011201859535884000258786921745524032221269100797314303266110368904844228962601324718624234290500426121967352024207866673103723361662088355417683041457804784967224850066989160683374325947321858176516098764040068954474085119299660044467574051174352821392592213720467960860704633960660767116617019264980766450911929625724845866974473702043 / 381299399277327757975010313424080998869692049123077783708402050861732790171744064941145121979189346286655796509881485566712979934986002961346376670321170966635764039683406835163986343435423273460669204456619175472504958644480771777345189791807318545063845107441975221171705367425825754010547444020813560241279908438675181986249311151793529339572417283043512503049314666948186981705909406991194672772170169567422246489762156034034161687691545419633534241293175057179699089053752485978844838679399914010740966215460375334273607829884821070907680365621035294900628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 69) / 2 * Real.cos (169 / 2 * Real.log 69) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 69) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 69)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 69) / 2 * Real.cos (169 / 2 * Real.log 69) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 69) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 69)) / (2 * (169 / 2)) ≤ (9219476864582808648449474206307795145050921511480431581448702641432662589210698175882737951567766035578524716420954021820410451089674524519857109672225348550657389322163251756541468859857168612680763392081722114516776759416824331155228900960694007399935839818722042393715767297665854751575209436048943661077468434174950152897451020834039406476202964838008368939980522024651284434654341936916548187351236195559686577898664875502720753687488026659323534755801750035727498868758201437059335498929837532486232466577149769440652916842878251661131377456207963221846865785031027188709776593616289948862188489762623719172651922052877275015975671277380100811091890726861087743867367473546589190721545318780821 / 34316945934959498217750928208167289898272284421077000533756184577555951115456965844703060978127041165799021685889333701004168194148740266521173900328905386997218763571506615164758770909188094611460228401095725792525446278003269459961067081262658669055746059669777769905453483068324317860949269961873220421715191759480766378762438003661417640561517555473916125274438320025336828353531846629207520549495315261068002184078594043063074551892239087767018081716385755146172918014837723738096035481145992260966686959391433780084624704689633896381691232905893176541056601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_70 : (0 : ℝ) ≤ oddTerm 70 ∧ oddTerm 70 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (1193226679591248953300812085004089499787318142047641999172703350024946404205821449383864058686795303178183240662560499635961311319405795369401593213472683006663280454898602247293998372784289911609944755516889132720858993301699476839026781280174668673581057293439745126876780930184735051482574657402765589008801151623047658395274612185469650977454340573406353475979403569976601674801606612526932585297811509732033079550796200513212698864614960292099086174969587074394778697897678774643317654192681238643672467080356059846537727334715053390200536436311511633543649684776501132788521915103072497876894353069483961570608213281943800493585155473171914505417931133260413799609867118068478961488001658286660586116294964111 / 6714210836172685908874307797338325412410468977566997689326639888398046167248056162097512020347509478550591991217150245756480944691906405252948772509713434621101394128060113977517641505240674647701150625532063867031922178617950108677342332977114363129358467683004930115529020338488118718956577904239910503388756164982681874001995477342062775954028501390326416357169191221045840277577775234570729120598694779213723596541089674555027363339810169123923400585242893389687210167180685477372222221381297763715340863593996233404941184969838918293937201149091211024298827132771657190322875976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 70) / 2 * Real.cos (169 / 2 * Real.log 70) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 70) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 70)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 70) / 2 * Real.cos (169 / 2 * Real.log 70) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 70) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 70)) / (2 * (169 / 2)) ≤ (1342634606896070983521958836334879576374742302248723264129192383894188008035658854139844735048014039385298310932165381425275631205214669522925067662844321528237479418611548315874447406960415569696314836694466380715858114293385262640718716479723760507373572615883125652212200879356897134771175856800997556890113234852087845811253130070929733878657491537559873751313538222719383847748602082835267307371281457621195550432925819466618970424876069539617418072651355438353662770128405973093192355085108881303536691693982241795331679460838412374946443523010061017304195729804946951901611574763782207520267377750468903887098466505248901217551798536726825457893494603449123813315253153906353268755645607593329742918495600996785922260537 / 7553487190694271647483596272005616088961777599762872400492469874447801938154063182359701022890948163369415990119294026476041062778394705909567369073427613948739068394067628224707346693395758978663794453723571850410912450945193872262010124599253658520528276143380546379970147880799133558826150142269899316312350685605517108252244912009820622948282064064117218401815340123676570312274997138892070260673531626615439046108725883874405783757286440264413825658398255063398111438078271162043749999053959984179758471543245762580558833091068783080679351292727612402336180524368114339113235473632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_71 : (-3311209960861 / 50000000000000 : ℝ) ≤ oddTerm 71 ∧ oddTerm 71 ≤ (-6620754625463 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-1637149241830556530400846764595844267705320889569168829681162099890626243358238871916966675957668414090413565710948745126850448188012045993028764715749695095740601843165271543012657072265142165456425626899347492389560390405618413653552608077296331263948651326572264204687707438109614714671355083744921181162417404378459527857077371492605420429422464499611527366784631937137258956122517439298563359428290641809115337691068328670264714333387320815653282389267349523979336413495501485447120768049091507161269207015490340656389701522169933942939855413022559749909857292591915502857459506405520113579333806296921183059791775581335709330258558432029786503673669401175369180547253303293577602204518564154935245839092980269967 / 12506192244910981336374409119297425099481770726976911889997571498897012634664878551098540463200787973684430106016155790084006161786441514739671298320802738184298191458098802673663276257441704436579999747745811691567156796563323789606508487792898645865467316811913494235890024040803534386598650187700820161753811249477196250114581505473820075307094494607907564113231731990437657158035366301556544603032422772075466060156169672599113291762415634699023143547108198310597259862684990237228986288199755854374432682234786885613466026205269467633100601190871020824273726218886034917687766210292465984821319580078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 71) / 2 * Real.cos (169 / 2 * Real.log 71) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 71) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 71)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 71) / 2 * Real.cos (169 / 2 * Real.log 71) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 71) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 71)) / (2 * (169 / 2)) ≤ (-11639022643897757950775466937244440212936107508505545773280116355989773566344883460963167157384794373278695075856975059259358330942743958162086523139024181734001920297707234694510361612407475668310445105340687622561857718551683025848304217159688518309359798819559330960229623373021621750573189390737766496360817357129851974725569781785421650616932856955507524660686400897920678551458671970206566135869951264033555044954887116702964650304944403636342145943239135810671054622105823858670707226172876481711803310789659231834407865987920709604713051431603136006284574413723433867331631415234117713120691341947410182736293869703126477592361213521770146902259958027386156866437551619027695146968322807 / 88932922630478089503106909292781689596314814058502484551093841769934312068728025252256287738316714479533725198337107840597377150481361882593218121392375027088342694813147041234938853386252120437902220428414660917810892775561413614979615913193945926154434252884718181232995726512380688971368179112539165594693768885171173334148135150036053868850449739434009344805203427487556673123807049255513206066008339712536647538888317671815916741421622291193053465223880521319802736801315486131406124716087152742218187962558484519917980630793027325390937608468416148083724275334300692748001893050968647003173828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_72 : (-2353293054917 / 50000000000000 : ℝ) ≤ oddTerm 72 ∧ oddTerm 72 ≤ (-4706010115587 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-8103024397833754777527188152283607023857269050830586956005138968444264789030558251859913739210021036205794314746719725055471417713008223821997122467283177566213835941972397520428825721295067104635534825730920186327986612814657323222546520659318376610606795469884177535296222393075845864617077005389071163205179177454257822398449971567764557899486911804684573177458689939455460811341000608784555070889600699211778513121546823540816833658778223893687892572577843729108933430017511364910461341734280845040146818563899895907866913231025622035058065970757998533305582456579572937779379014033641571291552463328236089465095248503257023214221207856591542748844128827306018347406838735939638374377616210769497 / 30939083533083736668092810330135003500387441048628725352417156605738196738679042794945335389761323677161127895528628332445864193140304715405587943724759506734035224142101005208401292056149028776606902082451750299283097399071514100785193470358542985300083819083286717972357725719753251056951910982737507599615388408240198075401195159592225271596163334406624126573835633146579231999078388280901919787718785542616838332861341220349566090269845259323039029896799252739678664450368598679731199996125020095200290699441134643529968980341017735498462622895012300399968995427811796333007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 72) / 2 * Real.cos (169 / 2 * Real.log 72) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 72) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 72)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 72) / 2 * Real.cos (169 / 2 * Real.log 72) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 72) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 72)) / (2 * (169 / 2)) ≤ (-144036137918446428986153149716279653642342716604735800123571147784197271695940164201783494288614135348168590906499875058655665031758574942422190595136467069924351938486582693829244517214376775215519408934247322959428974710294724558368058397161968027630477905274602164181000382281108219551334984396765445801912639706795427696062033479228431797431716436492384010529462879736157078979643098214947854263216496056023569495259907834855907239633148207840803824031215386230636226775090481167608063847178951396409375607152390322039387539821349582389291540999339315491604207102846730722221998261488688326359427624369024747278691476181059964248935991441896510781884339334541305756782243801774560367475747687381 / 550028151699266429654983294757955617784665618642288450709638339657567942020960760799028184706867976482864495920508948132370918989160972718321563443995724564160626206970684537038245192109316067139678259243586671987255064872382472902847883917485208627557045672591763875064137346128946685456922861915333468437606905035381299118243469503861782606154014833895540027979300144828075235539171347216034129559445076313188237028646066139547841604797249054631804975943097826483176256895441754306332444375555912803560723545620171440532781872729204186639335518133552007110559918716654157031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_73 : (20827824861 / 2000000000000 : ℝ) ≤ oddTerm 73 ∧ oddTerm 73 ≤ (1041838223431 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-61294810424323668491689886749028249727254224908271261615370155455436122350166315272784898344581691301314936626407926583947306891071593305630942117148524520653253253180508938469085361530349136560737463455352525532076387044878304935711834501989752890613007623607736854059338002374920095447932717808285577947140603866593922689363706372461568365652224882113179648853373426569041203012693599841495672416641178009219077680397201217002523565274964003699543958773311925444572588289448482310957354545620794271804248492115538948121544883657342343571964627707754840873797927419213337479962603362121844331611017296880993538989816865677316896207496024671498931256586783965710404442553527864820324560665476663827333430810278289106154176331 / 839276354521585738609288474667290676551308622195874711165829986049755770906007020262189002543438684818823998902143780719560118086488300656618596563714179327637674266007514247189705188155084330962643828191507983378990272327243763584667791622139295391169808460375616264441127542311014839869572238029988812923594520622835234250249434667757846994253562673790802044646148902630730034697221904321341140074836847401715449567636209319378420417476271140490425073155361673710901270897585684671527777672662220464417607949249529175617648121229864786742150143636401378037353391596457148790359497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 73) / 2 * Real.cos (169 / 2 * Real.log 73) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 73) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 73)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 73) / 2 * Real.cos (169 / 2 * Real.log 73) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 73) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 73)) / (2 * (169 / 2)) ≤ (-54460900536530959982167031476067816423398771818934207492358806094133680829141636348271114767420074281123592698408213932671880159607148244135917700476930335014591296044119473995922026997509852159666972567208265470459938493959518101514135342977092141231041413025600990845634475528502795450983502076457040794719611284183670557409157540073298304061514774215680213644039048974676770091487530671148776240952974842588423136152715423999733685921861584113159284554842617100537249571206727637953276614654075779855188888703767214658078468449119278563160785446586692584435670957277247420489229096628969661361319449208611685397128234248114245658141781603048757631366201125849562082992459592917563375081356158408586626802351559 / 746023426241409545430478644148702823601163219729666409925182209822005129694228462455279113371945497616732443468572249528497882743545156139216530278857048291233488236451123775279737945026741627522350069503562651892435797624216678741926925886346040347706496409222770012836557815387568746550730878248878944820972907220297986000221719704673641772669833487814046261907687913449537808619752803841192124510966086579302621837898852728336373704423352124880377842804765932187467796353409497485802469042366418190593429288221803711660131663315435365993022349899023447144314125863517465591430664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_74 : (-1282640403039 / 12500000000000 : ℝ) ≤ oddTerm 74 ∧ oddTerm 74 ≤ (-2051889702567 / 20000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (28309877609389498935607757852642015422203243140320082124475257407368035426323222996052886871749786884409079087061659139658921990985646293769063337615886928084893676480210205891451325624817650503134289751752636771756833466962815223944896777247695671577544196196103875795242920762880303562068432679162500911740414972546826369647212963869648951312033090779527211964128412388950433762304632493959544095114120706220388735330203961017675078620529743251727854573491504004185126259553916534114529757755880791974974032872516988888658947236344998278093641326181519121214106281422971928724737677146358357978090298441794580227037534012732343157438482381406693072406694069047439741732463730270244769 / 149204685248281909086095728829740564720232643945933281985036441964401025938845692491055822674389099523346488693714449905699576548709031227843306055771409658246697647290224755055947589005348325504470013900712530378487159524843335748385385177269208069541299281844554002567311563077513749310146175649775788964194581444059597200044343940934728354533966697562809252381537582689907561723950560768238424902193217315860524367579770545667274740884670424976075568560953186437493559270681899497160493808473283638118685857644360742332026332663087073198604469979804689428862825172703493118286132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 74) / 2 * Real.cos (169 / 2 * Real.log 74) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 74) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 74)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 74) / 2 * Real.cos (169 / 2 * Real.log 74) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 74) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 74)) / (2 * (169 / 2)) ≤ (637076222788797063765065577429984957060039445779894231717201682660827107306824247257242412110524438760027891079994091592271646731822178538921099103238036139427898282379642684495710078576569580024920860925334039110167664046078093863150308689006942856463068375071031990804008204800228043439215187592383870379620993822030971274462927719629197817108394719936206611287538510506662152324672906402836937591394092604284051671711204974315154556008072327178185490381213831521210127528835452537634539620381616177393314052882161271925294319104122832929765652126843421519617924634001390760384630411563213079821127480740230385742741120925708971618300211964914974703139910966837015158439414136822762895372761784461062786687 / 3357105418086342954437153898669162706205234488783498844663319944199023083624028081048756010173754739275295995608575122878240472345953202626474386254856717310550697064030056988758820752620337323850575312766031933515961089308975054338671166488557181564679233841502465057764510169244059359478288952119955251694378082491340937000997738671031387977014250695163208178584595610522920138788887617285364560299347389606861798270544837277513681669905084561961700292621446694843605083590342738686111110690648881857670431796998116702470592484919459146968600574545605512149413566385828595161437988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_75 : (0 : ℝ) ≤ oddTerm 75 ∧ oddTerm 75 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (29602668401042580137128985104120748219915815322169339742675230427853220559066945646813402811769380075732245721673297433342594666395843978994798349663473523929014995577936501122117411099179632602276429565954514703830186524288987246463224387933142990906744043666186655155389143807428602507072761909390330676019773609021197493038518581839439630950886927493553268030410581457867319453079048999668378497781001112633751536537542625519046107492345426907381949988096619750190467396469710166955518873461787123504731261699059704862435398046112708802494842785258870219768179725434723424826600050336506393563118683737481136439117972652191769173957153531977748236158803691769078094177153460283741635973067927890684191697983029579395499 / 133641934704181306656072539473744081712031956530361279268936579734379854396128362636025908724200781129467400763207935324441193582594180891217397852670960517318440208428444791345357092642373105637844982931607829935076638747516235581084030472521446772997858573919525419543305032689884500270160015582984280856253996974066542117728621695537152525213056139571119099022353698941643586087508038315439685203332603232275480319938395562984932508172143522095055325144178430375080887471533367374513973204130768822665456340332499445207617021106080981072887472842952018732703483209799025242649619520125120475384505880356300622224807739257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 75) / 2 * Real.cos (169 / 2 * Real.log 75) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 75) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 75)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 75) / 2 * Real.cos (169 / 2 * Real.log 75) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 75) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 75)) / (2 * (169 / 2)) ≤ (266460202881035456649023273691124056377068512380661635131430217990679861906296037962551325936425558895813274247828862075925950176267182335814780386933634567201246517151369828969068793574603091009288651769334728017435096809623163158888006952157822876773248910586180439962584507902226221015600931496768515518404607191649276667671333136372235355545869580036535337956406257563911803186681077640126830053193168454249074032516201673483923735878229959415284204304439491684734634185174049866949597084349505134685465483892928416674046353846306181321706486937181221703495554001904142789144959497058132148909445839594357825139402584733333026351933637640074677731768243534961349873702646725173905186835974303401767618813389741283540257 / 1202777412337631759904652855263696735408287608773251513420429217609418689565155263724233178517807030165206606868871417919970742243347628020956580674038644655865961875856003122108213833781357950740604846384470469415689748727646120229756274252693020956980727165275728775889745294208960502431440140246858527706285972766598879059557595259834372726917505256140071891201183290474792274787572344838957166829993429090479322879445560066864392573549291698855497926297605873375727987243800306370625758837176919403989107062992495006868553189954728829655987255586568168594331348888191227183846575681126084278460552923206705600023269653320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_76 : (-73 / 100000000000000 : ℝ) ≤ oddTerm 76 ∧ oddTerm 76 ≤ (7 / 6250000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (569613083539561835704718685192284008298615031643856425294711127282714252297535117414992769727421353246660107911833639685834698644959604986434499873328944103642434113328121565323561210019235438725742320368522937448447731433064086177992340353950267958893694612353949080448113416814930645646702533629381418256264444749975790061387787939923282206319792818306616859460813428228935462206873496417981529356937630616986329613612503269807090471625830268088514680121325848150845403689109699818671487355209574074944323533955981560288322901764141707853094119326074308837228100871204563855599175402264598155274775619327446923431111982701148810773376444953660310643806240642629743431843241540506237295021633389292809384931754130846643986293681850196399 / 96767998721224949571255008928449123094003397127848578203756740581314493613477494852825836731651131541839810726639765830784636426340544347643136607556435997506956250554284237717834279715168147805822029815133949844309430693130136582301938903237897930054593145726653105684065314256134481653235110529951374457082533120715433498100367970033900053099265613698648816307135755325319737883159470135742739832343458302516544540522136322378042240247640652503874001721381513097120572818185013885303390516149673353896948075570330359010076134784457035991459071838617823488868257908628769547503210107444646054090204238891601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 76) / 2 * Real.cos (169 / 2 * Real.log 76) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 76) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 76)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 76) / 2 * Real.cos (169 / 2 * Real.log 76) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 76) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 76)) / (2 * (169 / 2)) ≤ (643979842289566165568592384575906477297837453297572699511091662936301040428008355982379134315149242656750189673213392066644075322228007470940452559593881344478176566305925916387534959442578171285995108212884487385984956269349157951605611357949546769640660192261242748644145078159835575843608841810041731425669852683033941651893634266038087864296521657002339548282410852521103152188430262728303115006335687407015909592609516983536340820604776836516636606164819271904948596679579516325943751464058813388160539972444385933685325822422229479494429457453636630997377959920617635513243753025707099530228428191202945801408779006895544614564245963807178973686628131156342963849560169978923780625146624390288062993065700718221392695808839540755396826696457379 / 108863998561378068267661885044505263480753821768829650479226333153978805315162181709429066323107522984569787067469736559632715979633112391098528683500990497195325781873569767432563564679564166281549783542025693574848109529771403655089681266142635171311417288942484743894573478538151291859889499346195296264217849760804862685362913966288137559736673815410979918345527724740984705118554403902710582311386390590331112608087403362675297520278595734066858251936554202234260644420458140620966314330668382523134066585016621653886335651632514165490391455818445051424976790147207365740941111370875226810851479768753051757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_77 : (-1039 / 100000000000000 : ℝ) ≤ oddTerm 77 ∧ oddTerm 77 ≤ (61 / 10000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-23709509106731722891403018499272713621458559008069689180055053968985776587670614137383023330961893775539278400248159584476164781813565882116221305737377749312349518568276422817920687091742202078775545686620153680144825534281028749244554884729323007464186993403410664088574827923389739059489861879257877409360911589527630745089162368742259949113279816368066191124495383203421223222550179426454063039482859609164935261103303394533550559189601549026556771714240436469579067567861780401562186459579120344524042765227910928399942271691638613618945528796017091188816968200366574337579641818861898884076578879184428363806362432742105129409751541191032972335270881826164558502030956547034421213650483262256429340969451359704795358395884449296177521 / 116798399335432364274139042544430180946205186357434613026742577360368877391393141196353625882621730191842089129355863217913442113005877914415211457193960484833470825774923313485750208153257071558707720265177636405662654133789853202796832489405121391034454774914069496995349086146755412428260504497976024911160546284585447808297422611307291750625379602753975303782194795926673691995977119818257718181905450262186528858278588088044843397439403725457397015980361440194648003552451523016535857793809824312711548717635821686384322746359423099686327350421667750218485726276024137934263944904551153337676920642707045772112905979156494140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 77) / 2 * Real.cos (169 / 2 * Real.log 77) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 77) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 77)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 77) / 2 * Real.cos (169 / 2 * Real.log 77) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 77) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 77)) / (2 * (169 / 2)) ≤ (-168577034475885387179315635964654282047136105921694824756819402493136433231775499236830074986120596017014875979346175850340017721586508190923378043853025580076778175211942635127346305641362160124936563231063873357347556336835068072027419821852020632332022144449562041915028280663027773875743016565106149113306262531379465303929635091435297819730347536377064489142762198903238533737384173884807607160910116707270026044816163529765857320947202317351857279784573325961822130450575752530576794186747117531840361900338850780584161893554316850650290827694498019823093420812166958440620932241354439050060443962269249815914662959120954427027309996699014686795263088027074733403764701806859045086924388756864103815169220110543 / 830566395274185701504988746982614620061903547430646137079058327895956461449906781840736895165310081364210411586530582882940032803597354058063725917823719003260236983288343562565334813534272508861921566330152081106934429395838956108777475480214196558467233954944494200855815723710260710600963587541162843812697218023718739970115005235962963560002699397361602160228940771034124031971392852040943773737994312975548649658869959737207775270680204269919267669193681352495274691928544163673143877644869861779282124214299176436510739529667008708880550047442970668220342942407282758643654719321252645956813657903694547712802886962890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_78 : (-5589421371629 / 100000000000000 : ℝ) ≤ oddTerm 78 ∧ oddTerm 78 ≤ (-5588570428479 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-20089317892528025862400990656376494801179540707513460183664489067376025752859657772714189370722881138572258684608131077488470835833142375454011574102917019965409765512647945939051118797305150265618253734748656880174123721306807731204566793537454342520459416949227580157664021860332869603602996447652697934725956697878506717749278927729645467264423780411864298100151285305022737518705988718809543991581138112916545805122485790262972021820799069451266227789268963242107600352336239497815253597647787112785195637917554343234470084332021687726314338694322013048791882063336204910668969151980317195085519568511411502139923513588463991916621154193902148217994619929652402591330500569079711463921846458868242679569899125927719914232032851919982449574073 / 108863998561378068267661885044505263480753821768829650479226333153978805315162181709429066323107522984569787067469736559632715979633112391098528683500990497195325781873569767432563564679564166281549783542025693574848109529771403655089681266142635171311417288942484743894573478538151291859889499346195296264217849760804862685362913966288137559736673815410979918345527724740984705118554403902710582311386390590331112608087403362675297520278595734066858251936554202234260644420458140620966314330668382523134066585016621653886335651632514165490391455818445051424976790147207365740941111370875226810851479768753051757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 78) / 2 * Real.cos (169 / 2 * Real.log 78) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 78) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 78)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 78) / 2 * Real.cos (169 / 2 * Real.log 78) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 78) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 78)) / (2 * (169 / 2)) ≤ (-17854452861929966114188952690548733447085672358756277774029094832445428764881482584409150908780301498250658551540624963479385835339188875643489150131354739366555944470421227215167722961018989705425102415926879892209033902857180734326566258497213150572894486088370236775590039182791900559965376991576089709587307005264369794742049051700048922033017569934815615602650455723904127037404566267492163291044802735418164191936611816998258644316749585979480819948855072638597838341796248698708722589605555366798919856378109941850971528362933146599012003688097112779958840607496358571645545211657434300801693764602777732865182883114212722182407220854441459636815340144681752468604919923324085016005794287480991175824166574193855682005985417260230611618039 / 96767998721224949571255008928449123094003397127848578203756740581314493613477494852825836731651131541839810726639765830784636426340544347643136607556435997506956250554284237717834279715168147805822029815133949844309430693130136582301938903237897930054593145726653105684065314256134481653235110529951374457082533120715433498100367970033900053099265613698648816307135755325319737883159470135742739832343458302516544540522136322378042240247640652503874001721381513097120572818185013885303390516149673353896948075570330359010076134784457035991459071838617823488868257908628769547503210107444646054090204238891601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_79 : (-14261612681 / 1250000000000 : ℝ) ≤ oddTerm 79 ∧ oddTerm 79 ≤ (-113959580951 / 10000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (63407396421129360328800125431211196974821223481562809170005828542314367350155580669264888238875273400597521954717221393754147938441510449664716777538438566675909059499829815364555148869275470443773408876771830212490800745748901397483667927142798965942525757027698026966583041091879709407778692708536359988927945756544276160787372641552358863257294126824098246730270415194279864218662849585304249296092004675767834263404014589810102814099449542795003341759388697017284925518944901408886294510354872898127073395877227752364884841627149198006411558149368825309478971568640602931642053015410509691948225322712894897608867051149576832177080650142717304037636786263009173032138811066357260489671938846306790909706164519895790081181 / 2735281903713474237616080346414358494559373198229500289473267255421104126899112489989488790939000323138609701684298408574478398181827025957886410717192205316139333753808703243035901427614337296577946989238703405406170906032634971316287649619799534950516743597414223303278712386093775931650289493304558890025652749825738560386682790958419446861819718486241835523167557870321611171795767929206292506049106918836895965657097146890729722284109903839500280136045659326091122703243675293178576898199875971046616540566963129347220485010947050385333180147927782048553581445641696175418035368978766196167098091180233126258000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 79) / 2 * Real.cos (169 / 2 * Real.log 79) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 79) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 79)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 79) / 2 * Real.cos (169 / 2 * Real.log 79) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 79) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 79)) / (2 * (169 / 2)) ≤ (228533674515552997485694018731325202323983700344185522554495251584740543720245828064967240582856200488760989234555544073141682232966648512945832257856382203714564921367383385127995922376532467995518106919672694555006064036781379363345429728453534718514670755645319602057643843682535252732584162733421068134656473923139316773996908284982687985901216645911960357027830890026210053634412646771199556158282008132622551594820170407422017513050512580949241628896149425696914038493882300367186796131889098112692961564623268391403025331561066719431162738740986537635600961705232410279571739240784545166037303559261503525042565765681254338045093647267573537806030361269371786685547426008302142045129537113380546557292116542691248437678042540304163523998109 / 9847014853368507255417889247091690580413743513626201042103762119515974856836804963962159647380401163298994926063474270868122233454577293448391078581891939138101601513711331674929245139411614267680609161259332259462215261717485896738635538631278325821860276950691203891803364589937593353941042175896412004092349899372658817392058047450310008702550986550470607883403208333157800218464764545142653021776784907812825476365549728806627000222795653822201008489764373573928041731677231055442876833519553495767819546041067265649993746039409381387199448532540015374792893204310106231504927328323558306201553128248839254528800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_80 : (0 : ℝ) ≤ oddTerm 80 ∧ oddTerm 80 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (590104749350453342068992388875766450235703118586974790660277286852017689910016604092532357343658323220849503726951159318176350564981036592042613494301017296360980790627363202407745259202342296487685495554421338106089913522390852208558744882253124814952104452128620640957202433768207261278886303064822331942872553734107371511754741625533756471605708541717424861855162769213912375499378240397107502477358022147985397023882948236134561807034132450252887183615777054914652034263745265266188464385508131737223948945745282016968757480182248445578537043175051325996263970510650847775798155569789287549546831239991950010181737837004552054692954512434843763671091061223244695477342475001534615703626795083230156112150504431416480791467 / 3036772948343229569641100014559096925203377723955778010848391152333274475182536822336897043216330874958030718518185340853408502794582608472635965842991951153683564961004107954951504652745627784258205516242038918724078684388695238767538919355314969095745718072236999710876395470841888548252695538059507829348918350549067568951636432126783223652632635587702387173400573184080654311806943745029366283959667470556560393176833864015950717223490844353661932837391178947695905225016760657007016564134933535086942658151002582375377875102348046871073772465718689837547807292718822419950214640514703163994945191084521425592956944683464826084673404693603515625000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 80) / 2 * Real.cos (169 / 2 * Real.log 80) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 80) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 80)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 80) / 2 * Real.cos (169 / 2 * Real.log 80) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 80) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 80)) / (2 * (169 / 2)) ≤ (20748725178258389912280757520661562076293097673410256467719983270689853662815318797008156352083992961643135377899224523188728496768194198322759241782845398248408402273420282305625551815749928219107898985685652516159233100033621592723461467535622054959920095358648555599446990315125507431963729430440236864479388918957769254949636968027516761500541838846208584878883689000563253393209821058021696672587677077399219348406257337339768907809357637904152652643278111775213945230110114112647423983804256104636707200443197527942223370101780100611454853460752260621098720811077547130690167066833622376556981896329634842182453160409252407377644910803927841353367984169065615774014576467850240247246942381334196384734771489121392360843394924411486963325751781 / 106761548965191664557694922386843251276681248107820320693888751449216680768136060160281536675574132322743267447904953389377642676372044829116108174167685782746687830660300670291263835448088476790327537680384180736393391248040066987921290133585291882272310400977082021085498278271785144274508827509904572125547910761490656720955968316957222706537866094880162049064863901002835503149462866036188658420457059511754076322623065531810767402388349996808427326314533634879934168066995491847902926082868757092900327825621184536634378421566923522811187313247922689601290100134646100701374733455595033109197291874065206368502392586528060292039299383759498596191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_81 : (99148919123 / 2500000000000 : ℝ) ≤ oddTerm 81 ∧ oddTerm 81 ≤ (158663660963 / 4000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (2125713489440737848056169593338513939771331827157343729008198682922598434485925767943112430473571652260249929683337916716877716468101232470043713029950421904423078518839917041262549417622463257453517828911123843629835878403141717557129926776296910145719116769086208279569318334074336178466915873512140761990572862840561249759636248479046514149013586499111903113567172754481853858965098915704523600945811210743530843140874593749018273494812954881767479532647258861268101706668660491488076425137354706235699637923212833181882350595262276529364877853118912913760097734105920538479952836633602838753976799209481553256811657500545437302278494674687777046652032358486109477419056944931815115383176322591855097502423707563416020951252926633952113960557977891186143157 / 13042840498511668384628679019996445153042665473124982306829773213487167963500559282252735094733239761059807308598987620232002249631056909360343984209023500996300381440204158988170153749534307940377936311906353976279119997180151802617491005038259196045478551852294079319375574045628432901622245279810709428909553288582508851941503481666657671269510834151467492690885342933280998095492210050612890749211821169075469806943402990773819552822637099454404259376743599539237607494562508073704609385489826064332087233385863920913793969206557514120736981143607053988235385158737641217317749829191046696506014305020490294733047485351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 81) / 2 * Real.cos (169 / 2 * Real.log 81) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 81) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 81)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 81) / 2 * Real.cos (169 / 2 * Real.log 81) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 81) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 81)) / (2 * (169 / 2)) ≤ (2391810425764207205263839047336579288582676104375382094422931230166901482562586603367568478503632567286892420420038356828180187987264034129471984866269777328269993711218906956371619824759035347702477558823412312201190531642310800637599729364136349951803893198955425887489428649699968680365431090919399937064172010532959157675496477138168192013993133078346639217997926606409513534588741508373363640089418677070835838190066347591072696418368613805402937106460146943590323830760185583369332462930722180971867055656991930749685631053769842936960689742928658785413319010757402001814912921657852203097030490904921877063409667007321732073943952501004550955124360769591085692379983463084497513098290578378355398142502458828285579421403871147492196206068140355956390793 / 14673195560825626932707263897496000797172998657265605095183494865173063958938129192534326981574894731192283222173861072761002530834939023030386982235151438620837929120229678861691422968226096432925178350894648223314009996827670777944677380668041595551163370833830839234297520801331987014325025939787048107523247449655322458434191416874989880178199688420400929277246010799941122857428736306939502092863298815209903532811328364620546996925466736886204791798836549481642308431382821582917685558676054322373598137559096911028018215357377203385829103786557935736764808303579846369482468557839927533569266093148051581574678421020507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_82 : (-123 / 100000000000000 : ℝ) ≤ oddTerm 82 ∧ oddTerm 82 ≤ (73 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-582222107666302964600770279646647331015272337299157410704691059759223936686947087541313521450032211297871610401616315347723448089754551331258969723999398850068271391182545176583316030858775773189460804918756737410126786236651348125313756253870625402516449122539512345684780872539745041759233121900544466133715670945549041942727663741159771566621783885323108319423502469597507133292037088690669185226657452487175376981182112119947928717673527509858502608781905543695607061009638686433001164825327486907263388506755453413004870607282839148310269668872281499233942244072115639774293293950522758446014872580589843691496308113099782494488038972665960321606348513560679287097476846186122779778810701553448355972703754140996559921017762196993674919871758439659400922747245073 / 25049425295012811270510155195743215534356677648082601342828699135348530920953445218306044737187126031955322694869918564339231045974013389009958759755107825615968878194930443574145392737535172832869784913737047242589378356993083083182957868319413111873070148467345534130463358374455324108934224062989360888738435670744107749807782217246657080934759225019111675287340188279928185189587974584536092805412918707117810400637492515759718455991113345107629852500304669269895427411238461727988723220444415987707382601816720066831855835740647602603032044821243291892474467962387945004768138309302304082953115546693905456048705213506016601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 82) / 2 * Real.cos (169 / 2 * Real.log 82) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 82) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 82)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 82) / 2 * Real.cos (169 / 2 * Real.log 82) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 82) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 82)) / (2 * (169 / 2)) ≤ (-6462138266887277017764340171462002826513528726627367586732201436095568846568499740649374280965727925632475923703391858748182528824938464930922988009517584430784297638738522943560853206225535327723568964127176424639065314827036751876841346404070032082005616448170768529512230222080047665513141402218137361515614140270577546766163630091401620041788453297660844382119491387666690103879047988542526504413658486027242283572761913836777331308723839143318251140898791401244952385857195986507471060003447214092647665327675405245559759828918023717442197590577868270539421209404365337885083858697068935323615917859070954533856439391601066115204349757409963612524177421047013236306188955553749978190765750631667484061987078617550229489650569475606418975353 / 278326947722364569672335057730480172603963084978695570475874434837205899121704946870067163746523622577281363276332428492658122733044593211221763997278975840177431979943671595268282141528168587031886499041522747139881981744367589813143976314660145687478557205192728157005148426382836934543713600699881787652649285230490086108975357969407300899275102500212351947637113203110313168773199717605956586726810207856864560007083250175107982844345703834529220583336718547443282526791538463644319146893826844307859806686852445187020620397118306695589244942458258798805271866248754944497423758992247823143923506074376727289430057927844628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_83 : (603444904607 / 25000000000000 : ℝ) ≤ oddTerm 83 ∧ oddTerm 83 ≤ (301764950921 / 12500000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-5747920164720967787807289322730571484238353466298102225273255509926196490074410565186441813257444961343158062511274799459930923568880456514135874489680507404405236022029887384536994509758825066744690440731166456701694769800218607207028332368535610202689548298762755471064787261329953033535085047892080351766358027465009215068711536272500161063528772120380890905248918578211576357003525023107392738333176349805441191768494459141657541004447615227391345254582517433174228030072596587587327238261837671415440641141173525558115049592407299481400894478952373577701733640704591633461722346865421231186389769317934417875086357687809862885044563828297359754679730420563117438022239062308361705951418721902617368974130772305421371200231686360868037341951454774847863963132247 / 32806540207110127293649041786802836549644431045852748805985653921108573309696076752844150561531443132494736965429804270250763425976928629256090620444734003182925502733905740339441186317390610274135260875283482191051648291313576591877298897434188694294080972934332357133705259965805150129076794338020299328294047305345443564622843398715473264515870399943670065489431973331280993691513397972568758304800760868829135667436266178532600476162045394589756131245338768848022860285876399655811620902968533321016940086898172827421033074157578583024920721566186639688715544130753770156721765638754111823302524851205111059889655286905202871139408671297132968902587890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 83) / 2 * Real.cos (169 / 2 * Real.log 83) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 83) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 83)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 83) / 2 * Real.cos (169 / 2 * Real.log 83) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 83) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 83)) / (2 * (169 / 2)) ≤ (-40868342523120142592917375855126045120642542733050832945467822182641610157705399861112027452153832059644208262333283027962011365324462330525044286012185577701380517695116606121925727120947522103351514260551379736950868969988418706155038993971460449985788557057084964519809576567228376011743882651332497181314651499790409253206155400177348040105206840758612918139583475139247096229579645140041677682970553664151176170900292339837813320315536469969791769859549536815936011290484549575464276265251580348898486429789536825406627359407713681927000398898482411036401050368273484304261921745315049727002801129297063935625085834617932834647699615398084079210496168093155408769004746420564744306110873817039712158761379913830815491508795930853281328721 / 233290952583894238532615408261709059908582620770508435953675761216772076868949879131336181770890262275518129531945274810672095473613714696932199967606997355967470241663329709080470658256999895282739632890904762247478387849340989097794125492865341826091242474199696761839681848645725512028990537514811017445646558615789820903984664168643365436557300621821653799035960699244664844028539718916044503500805410622784964746213448380676270052707878361527154711077964578474829228699565508663549304198887348060564907284609228994994012971787225479288325131137327215564199424929804587781132555653362572965706843386347456425881993151325887083658017218112945556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_84 : (-2525250764839 / 25000000000000 : ℝ) ≤ oddTerm 84 ∧ oddTerm 84 ≤ (-2524861878741 / 25000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-366795658112135708258935107961798960171900173695624463957469752584848103063061650132892987599568928807020203077457183289804279817208652084350942110345423559948023193637517687767977443276662855887957973267141519239305551140001559619890328882866201054861293923370969154922826767722921675776693012349397557672064692953265804415704206546934516600557889291032728346167882548627992406817287330293959537979311774534645931694862180568615927711342300545121604146736370193662683131575490507593961797558285045071226644456805339554615193408571997210378506805246559470062635698861381210713367305735560456485821899694055188156627061735550803932301594818728437737381627031743237272059226360939852052839077025276301183316164274127214074109558037386627106182064019480994713556569844609577 / 2356496818470850191953877826905524884588461426856540101191717134889770521975778788016377389681939916258847966598522172385851420633314239687527307046713033902722824333135869228296536326020199665588346607841539888131691000581354505631333069634961709006620130350855882962072093540243899924047557400705933282138601146787739961587907645121561126573115653073448630841145176236901825993591777439291590486861010521692344497126007294600694813274002511461421684836622887983225329225448187450508613355658778731389645711666621495045069889693095869089804835784086006570371753135978149111257882855604082128997869538681293577287382365804001043817112874717769482619394993960781903297174721956253051757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 84) / 2 * Real.cos (169 / 2 * Real.log 84) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 84) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 84)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 84) / 2 * Real.cos (169 / 2 * Real.log 84) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 84) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 84)) / (2 * (169 / 2)) ≤ (-20374398455847666756831406263358191266291940550321690554551608741830942095098762030897489578794912282418219613507622046889155846711272288904931914554655893663496155596446092610964928018505919003717393367161755197351011217513886105013360450789847775986111726220518448018823607132048490248994384788646540747962258615563887096069128861937245469204088218931305470615167367802611334915999585223061875088461732280026366051403617195315721728241568486025302367509673515879894867390533614956703871440549587413101738467390523058970482873997737013176876070020359352900526089556918816150863588747120667407141289460848988069160181515903179981997038473132420769647431849126387751505829157712630425795752293690374728439809942826593260784554799176692832647404737448819240410030100146699 / 130916489915047232886326545939195826921581190380918894510650951938320584554209932667576521648996662014380442588806787354769523368517457760418183724817390772373490240729770512683140907001122203643797033768974438229538388921186361423962948313053428278145562797269771275670671863346883329113753188928107404563255619265985553421550424728975618142950869615191590602285843124272323666310654302182866138158945028982908027618111516366705267404111250636745649157590160443512518290302677080583811853092154373966091428425923416391392771649616437171655824210227000365020652951998786061736549047533560118277659418815627420960410131433555613545395159706542749034410832997821216849843040108680725097656250000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_85 : (0 : ℝ) ≤ oddTerm 85 ∧ oddTerm 85 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (1749541032475569588765710303115852006429813209308795641322976972780932971313083700273835671426432302046386180719550718308390637998410097929493521066487158293500687241017878498956804059385852356095124597011319999053986762536469035692684804547035505655317449024237063939221304865351603008132296162502439715853148207890642938111646871682099526407811759436481089146292484738733097810016985498479756264138466457762722263553662937479768374081994866915659277173202618584046321605380453637642623909876642038524521000332650887266350835112678234180628323574555219317454522728901006159103151147402055365412306419733519593907085879289914124605603020400330378852746920243920663382017379058145518810261398509726331892049961985890332341316483593584590865005655167251874013813637237143530804878433063028643 / 663294887097817517507033668448339772114312642383468024190137514094387852530864567003437963744233375804209934314815690658814764301367657598093560569697588013244991134995026245062910365553967195690898900870230898757147779968167745229214408177447809738060733307432666590825889801804212472203256986646265905803639709017141319353785356443024030636208834660017357153808908492842578149714125761823900077188235780959798440016069743173135342101375711559592922450396080175384113028932106717915520232905983340486256031474305268189049731302435994647488695940893895260306656610301482854217421441402052481393878821916558156197013464978246417065204960595369338989257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 85) / 2 * Real.cos (169 / 2 * Real.log 85) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 85) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 85)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 85) / 2 * Real.cos (169 / 2 * Real.log 85) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 85) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 85)) / (2 * (169 / 2)) ≤ (1568847940243555149607399357005899646378064445698739782788859729948947476354936290954720546381955105766362322824042384503605088716639252819062064013466619535808720756499078522313921472707268557398976119335300718705999746166258598765705621973106264306701557679004876491855472318243518237548457745781896130971313362204817918121006092545928867827837056056415886077451888949036169987182520306841958173962248793658375289111641497344717934915507529352148207239549672288802761794554963039656669841039257931050449900584012077378360684016801150237831162822451086292480676351865131355664612682938750498956213926727089510760242167531489648187150888153032653135984412960486505369169621712874092718574101254031604432826780072381684055963202827690015543108010881098108831952883336085879593489 / 589595455198060015561807705287413130768277904340860465946788901417233646694101837336389301105985222937075497168725058363390901601215695642749831617508967122884436564440023328944809213825748618391910134106871910006353582193926884648190585046620275322720651828829036969623013157159299975291783988130014138492124185793014506092253650171576916121074519697793206358941251993637847244190334010510133401945098471964265280014284216153898081867889521386304819955907626822563656025717428193702684651471985191543338694643826905056933094491054217464434396391905684675828139209156873648193263503468491094572336730592496138841789746647330148502404409418106079101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_86 : (7656791815679 / 100000000000000 : ℝ) ≤ oddTerm 86 ∧ oddTerm 86 ≤ (382899008481 / 5000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (3130856071491197427959350698762396635109196484180255213289719002330767613721025133594959418237240062979118696647095797986157487969394422931847393927520110232938615503794115970161325584488274512545581517491242027008524251908986853396878626382767277297753619958450663067712742144279175383219302848900272129537611879099695129938431452991140912127115521615386332576144938390816371964109389545679238406392365320144963832199560750760574765235184204048152913812344918207341968778822245962747792640177963512688625877101144677990228274247791093967429586949192965557570151862823026143365078383494548520233520549134735045255626321261722222337864962266204190516617224185522300895706724854651407618175092348154507021343183901962725261322314692759837122415222827830339218736811 / 21225436387130160560225077390346872707658004556270976774084400451020411280987666144110014839815468025734717898074102101082072457643765043138993938230322816423839716319840839842013131697726950262108764827847388760228728958981367847334861061678329911617943465837845330906428473657734799110504223572680508985716470688548522219321131406176768980358682709120555428921885071770962500790852024378364802470023544990713550080514231781540330947244022769906973518412674565612291616925827414973296647452991466895560193007177768582049591401677951828719638270108604648329813011529647451334957486124865679404604122301329860998304430879303885346086558739051818847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 86) / 2 * Real.cos (169 / 2 * Real.log 86) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 86) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 86)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 86) / 2 * Real.cos (169 / 2 * Real.log 86) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 86) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 86)) / (2 * (169 / 2)) ≤ (7045519471228218040193326685558694331771475868109020249304333239507106282426015383091520554811116144435462285559694136675675279423898796418876538679972730507201580664560427335353610968668667056611779265601232704086875207848580119723104378171517283798254696998321728063550734406838350477920588456052469545021636861110616489035781097490770634428859336599613670375414636204150263510863519002476528959156441680925003182537065817527801964337712293168454709806219595657952231582088946688223285699976441142810758149805220945364609534826436188066591721928020019220403359618466477176562570450756866447960862231938398036997584136985539530073836633434253798440128709199261350896853342931854742277231501441317690100823007973257760652331132723065516883928799168149602650243582221405499092295977332813 / 47757231871042861260506424128280463592230510251609697741689901014795925382222248824247533389584803057903115270666729727434663029698471347062736361018226336953639361719641889644529546319885638089744720862656624710514640157708077656503437388776242301140372798135151994539464065729903297998634503038531145217862059049234174993472545663897730205807036095521249715074241411484665626779417054851320805557552976229105487681157021508465744631299051232290690416428517772627656138083111683689917456769230800515010434266149979309611580653775391614619186107744360458742079275941706765503654343780947778660359275177992187246184969478433742028694757162866592407226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_87 : (-101 / 20000000000000 : ℝ) ≤ oddTerm 87 ∧ oddTerm 87 ≤ (411 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (4455801375393171405315383192290585556071184453768829068001836517987957221439879986652634646679965907105863343464955535747065330485169464904424280941787787691146506984746453904426171670518732380111554005047853213925482149508273816679702949564920652919499994346496376811844390070573714998353181785907170396470899258055301990607573706434556982243111590260062733344766330270253039987920198452968184416447906569213644288566576705190803349778507878560460846339742132973769276471295926643035015985689469873946763971820240932971779710135535394823702846088547567348481158551172867418859967640116047196107522010370661884263814474666139091711907217999712319352817472149817866782264349076191278457994742292327565411689616457420181606467278134353149443042455477362991519183028662420433834462303593801 / 28751526995848548099531783941442357305123008257466421152793165814799333493754870161856204039208335013164320563917525203286398810295244777181825387616367528443270003248127655730499187723637854579899810990571584922537199122966082919068537171139359349519316046144112036073234632660697881944321687773127875988305122482346748720484570429959850292326175605745973164221747488668617827964096073539966531072596909896880277618983517818073041275605444606406721083774718522617498392808124019510953875718286109335937264649118482771881832998020741146414387987754243955645012779894373826603112521267128803884474391722896153015234990830562250694164506793123760001766060084849030431541905272752046585083007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 87) / 2 * Real.cos (169 / 2 * Real.log 87) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 87) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 87)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 87) / 2 * Real.cos (169 / 2 * Real.log 87) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 87) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 87)) / (2 * (169 / 2)) ≤ (40107905676655163598966541846526863129822351783550819275679581243899363468977995113995198705230038329398177220859515839479705687035260584933747717645738388289881289457117882971806884792039085926730762345315280734708729161708253322464365591688921671703469559427133511560459671438875910809286222907632048552003135968366661457650688374400359620361558638842784440855494566261530177920749469009792287436845987613274349863880404880603824380136786200231195984210440537476574136822090221250582019706804121307009355117979993916652877308259647990777907765883587840708661487248692291848313842803233899613910509573599533177511233423117703442761869898824224231780957225317846536260043163413485916595505096634919843032256800443421282097662672117883659879352824528801612037364037372341126173021685586833 / 258763742962636932895786055472981215746107074317197790375138492333194001443793831456705836352875015118478885075257726829577589292657202994636428488547307755989430029233148901574492689512740691219098298915144264302834792106694746271616834540254234145673844415297008324659111693946280937498895189958150883894746102341120738484361133869638652630935580451713758477995727398017560451676864661859698779653372189071922498570851660362657371480449001457660489753972466703557485535273116175598584881464574984023435381842066344946936496982186670317729491889788195600805115019049364439428012691404159234960269525506065377137114917475060256247480561138113840015894540763641273883877147454768419265747070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_88 : (-243 / 100000000000000 : ℝ) ≤ oddTerm 88 ∧ oddTerm 88 ≤ (199 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (18225787841398179665007542614348884315976894033161069658518064523238282517227377733995812787906651469642425817650807614651673112592357906037707754792243424919825713177680135667812267383346522208100367102341338017131340603369379594676781198034624871286319323379012472584150928246677745197757919206421322038541976242976247242044894875587071112355256266018563787735648392945983162183181141529292479550352758292668305182475982781262687193798084504986294026290066023206447263506758692125801313959352017650246887693146093913257272007475031141963410003104834343063922352466388722504091467739795242309627974578414225126958672333203007817391741481486756019635426110036613513323134131489954773884729747804140681654953621085058684701021759277780400327434672943508176864943768866859802115925314271 / 582684148191763248819285621195038331110345997553031467512461208343971087738193202786120555313457322005297824616821259241698105232710675884040112711167323595510513714980034178638554862320774516107882824702244628360150737060738041324037596718529318056726711053211608222820275361630355617158777996313606569308416961821321518266554608477051782633814845514258841503653893139184535403838896646392646100069826569531469711649493284356050339842936833130631335596342551813149597226757567756215000912243136208002286859101639639621617377569561349236605371883893574321993962108399353739046387688854679313465075287402211518417110134082304840151758899765013371679273476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 88) / 2 * Real.cos (169 / 2 * Real.log 88) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 88) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 88)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 88) / 2 * Real.cos (169 / 2 * Real.log 88) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 88) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 88)) / (2 * (169 / 2)) ≤ (4103611342875806345138941976958813110069104818750288949250698749101990186510305231615589872672449248844413379369136745443051916882570527793297153224277386087767384345054080936356370037935119933377101606603970377847904972511211424179990049434842964390801604715788951856728235315692907575958574414730236825370347664794690314949273955891319588789184889835183438654162543218571717005056289998404171145628042881140471211915262863898308739517706177925490713092469863620683164392901297590606001628774720048253847805543813435069075097315175823156238284864658016982383643435394571031919015490530694333678173076476215206849933933352926237284439106784649553719387601980811466944924067244764319825023872701132011649652016006365302741875716130608185546334969750911569085155195021770800196145845590907269692863 / 131103933343146730984339264768883624499827849449432080190303771877393494741093470626877124945527897451192010538784783329382073677359902073909025360012647808989865585870507690193674844022174266124273635558005041381033915838666059297908459261669096562763509986972611850134561956366830013860725049170561478094393816409797341609974786907336651092608340240708239338322125956316520465863751745438345372515710978144580685121135988980111326464660787454392050509177074157958659376020452745148375205254705646800514543297868918914863909953151303578236208673876054222448641474389854591285437229992302845529641939665497591643849780168518589034145752447128008627836532226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_89 : (2593744162319 / 50000000000000 : ℝ) ≤ oddTerm 89 ∧ oddTerm 89 ≤ (648559704431 / 12500000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-1939116030218941658786046275813224590189890539766010816966997746521991024302140014078679432303823839474484327508140375494233950524207566871873701663681246971606249162170924919653404904738536180350673738336478387829398933997458939269390927359101205867993399718304071768853073294248822080654061633923336324462483242166096923803632312901694393392194850232393852868912843472262946372931112624345735470615204723500031049664126867002418128255441925884371230921313117609148981508742574328089560856128862305562723471149265973626820547046941984987282896131413014497269249879212147128156103623401885529654887371110137359893663576039068456854076392555864938010328323883767635457805902232463851990977045900571559245343537539249310373583739239581420298642177777722517739005285773608137737316831120117769391055040839177 / 17782109014641212427346362951508738132029601976105696640394934336669039542791540612369401712446817688149958026636390968069400184103719356812747580296854357773148001555787175861772304147972855105831385031196430308842490755027406046265795798294962098899130586340686286096810161182567004918175598032031450479382841852457321724443194838777215046197962814766199997059750156835465557978481953320088076784357500290877371571334633921998606562589625034504130114634477289219653235679857414435272244636326178222726039401295155017749553758836711097308513546261400583556944644421366996430858999293660867720491799542303818311069034853585963139396939079742839711891890764236450195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 89) / 2 * Real.cos (169 / 2 * Real.log 89) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 89) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 89)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 89) / 2 * Real.cos (169 / 2 * Real.log 89) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 89) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 89)) / (2 * (169 / 2)) ≤ (-861665018177471449004403780197846775728461885636058148028951906063164672228330861608395994114549752460417886354801577887747242334512331764826380222792766458045817215594661407083507910423282908032934181918000058666704494062911121426116160062358211326382112793681892992243546689264317218596561994742879482811687689271999895204930343848230676436332461813755514542822802763780710986488130718217239082281798138953939997334974692695461058278004329050895982125635739462864251762206701112854784984569276170177943731663828067244293444257565561941059788326336093039554794121370081564716000982116399291160333790254542535656119664361887414722169685312006906351399655518813754624737406710159770150056632939114187257620351216685642700460800120310291146813175095281861932791085942217515738856017 / 7903159562062761078820605756226105836457600878269198506842193038519573130129573605497511872198585639177759122949507096919733415157208603027887813465268603454732445135905411494121024065765713380369504458309524581707773668901069353895909243686649821732946927262527238265248960525585335519189154680902866879725707489981031877530308817234317798310205695451644443137666736371318025768214201475594700793047777907056609587259837298666047361150944459779613384281989906319845882524381073082343219838367190321211573067242291118999801670594093821026006020560622481580864286409496442858159555241627052320218577574357252582697348823815983617509750702107928760840840339660644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_90 : (0 : ℝ) ≤ oddTerm 90 ∧ oddTerm 90 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-13310421341466247476402911954316308635440538831187496787245256040678630207596018895982350749036360349553417206843069286689245038116037248794691932046569346618913326249708238858439265460336944184433785591389559442349465546258739674769367698271932656298410432074435400227732130048146878503715687872126573876776071911721710179333708734600740444228965019612309550418260228445502733973445362598371975383336922223253849893036907606413670253824529149126980675927123529308732987024335323237358863657421967095882451935510445160256106950743544925750087532385111986903113513273693383348018429974035518897275490249967144157204620214962407524493605025472487431440293530563326594193414641940147892051478267686754256275153945966455943489675067335597633184687812700330128384254869368944823652509373324761156699617 / 88320976004399707577254783015481074654891558019574031083431615013096412138295817012525568611412189415447339852631614800770554581184589068139373005574127424722991723725120914630489789095583336300005901706112739161304406030757109609784182609796494010460786720551101419874442919361556810064130716186104937183219676338604426299014258567832463271546108915603443160309018547259950911103743891680511130598050870794055915541648361772226192964168784510506939816881023364195225646621715479520598253408393748986329188874551787450460326013766643021124348480358221311528154522852116406401443473553035606763089124327216771454433370023151565878214868810281319747536293136268210817780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 90) / 2 * Real.cos (169 / 2 * Real.log 90) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 90) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 90)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 90) / 2 * Real.cos (169 / 2 * Real.log 90) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 90) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 90)) / (2 * (169 / 2)) ≤ (-473196493143736043309599431915460115132147490559648121313443115456706894138366385589220416270686803995919856696526591697155785850192881203966969742511898990240126283000275284553974698256596760616369750647031377743064865174200879745786550507381924120710463147120208730091452914936075565973385364120364706034117943782700943417556234697629930021837426779654541077361718949192034704440583213298561754414828887478095763637179840814539483603393723145045903117986882565093257086753180424294467302616834062168090798695511207963008545307461336858672347120684390480309411829411589878813976407035836719263120489515376069817762704775989730389508862597159060671335127981590288946066501745496749789613487088221251835525922032644687929133815674222788670391958417307747892941668331244387748208463451936219094403 / 3140301369045322936080170062772660432173922062918187771855346311576761320472740160445353550627988956993683194760235192916286385108785389089399929087080086212373039065782076964639636945620740846222432060661786281290823325538030563903437603903875342594161305619594717151091303799522019913391314353283731099847810714261490712853840304634043138543861650332566867922098437235909365728133116148640395754597364294899765885925275085234709083170445671484691193489103052949163578546549883716287937898965111075069482271095174664905256036045036196306643501523847868854334383034741916672051323504107932684909835531634374096157630934156500120114306446587780257690179311511758606854400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_91 : (-3577753911419 / 100000000000000 : ℝ) ≤ oddTerm 91 ∧ oddTerm 91 ≤ (-715349618953 / 20000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-158194658448090357743395576537502764230370668131861127407754242903593876432893597250832207368649449497189584740490596636374113173359065688500542645792501064917248481887042172921723008558269216018351229480590043075321029135194170120365648533389596492287431841000055312416351528415490152856055029989786564590029290675509971838741527673005977169037870808946856160639852318714569944792260286709671626988436291983304022046344145143873950526318231265526002013211703508007317279718999686560188708058268303066167682681617491107374250158669925610867229308178009024415396933436680289829738679885818331733816916657005411912127474389268868503767266105140347649126288764625789255637918910552532196417754166987706082569319779221264669324985267302597016117432867120703748575056134847753258396077783052514507081787826134792694264597 / 2259568279221234052657957470105421502199185270679931565844577386198659850286245134717196934354833318734519877143400338045866889514624432219013026512355115697125405743184875512944010114144772187733511335040001008700136021153776256558517863103825707798896066995968048781473587616609871384135473784873157690202470770206385025864940171317382273988646553392964149559740274944195960911023675602369199012848157844020093321777363194556295923337477422931114718906350333593637250008789226178864278336203389394506897299131408329196650953384234327644649655755194676345807071837690088437272600051790446491271589063356925697492613703290358882719663585275756414857095593003731981986684233074120260425843298435211181640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 91) / 2 * Real.cos (169 / 2 * Real.log 91) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 91) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 91)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 91) / 2 * Real.cos (169 / 2 * Real.log 91) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 91) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 91)) / (2 * (169 / 2)) ≤ (-2811558846737881668484738510383346135007523140489588696120426423331719589845421363842794647066616390970074278868623387272148596203837600974715194862484540219445988416479791667579644909479546616811674569302904994516311098020086794896478519183911213613918516133494110259309122093697466336271123493617230959005725798051301629542422965332772836801499113392004946064635882037162084716677785083457414557180647289369348253277809223656353848035124707463873032514602514071834036937844416784037334810628162515132173400993263917281116659025850859214172809357870309289364777077182953699200762334309014017262166435318707850105108077290246242880885894832848773149658698322991915395107226002771207430401157014675993490068313673512057369186549303679249772358164634952786710714245545268315446138759297060574086381021326191 / 40170102741710827602808132801874160039096627034309894503903597976865064005088802394972389944085925666391464482549339343037633591371101017226898249108535390171118324323286675785671290918129283337484645956266684599113529264956022338818095344068012583091485635483876422781752668739731046829075089508856136714710591470335733793154491934531240426464827615874918214395382665674594860640420899597674649117300583893690547942708679014334149748221820852108706113890672597220217777934030687624253837088060255902344840873447259185718239171275276935904882768981238690592125721558934905551512889809607937622606027793012012399868688058495269026127352627124558486348366097844124124207719699095471296459436416625976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_92 : (-846698865149 / 100000000000000 : ℝ) ≤ oddTerm 92 ∧ oddTerm 92 ≤ (-846425893069 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (261028737589818829526748507116254594471319380092977149598196515610027882126804949197060755068638486491259312947412498882322713818891812997651306665750926501870658942691240041900377122368779790341756446632948849454525902203920518447902259353449240168235415156709362181264896570658744476020250542770598321660284203543268807705054079480810825343994721770226820605382143309585419164557869041099963615761235512189592712946130969687155660460275853465502998858425483276144380943434660577903697845860654246250403230979900031185529997209488756127282112506677756740990832404470213612413564863262819078939835526545362697876099931959480603746401505287287296969938532485845117653978623548947647650407232149210216447260754032426865595174586083593035259267941117634917050739397731273119447727750738946257135020848591483 / 4463344749078980844756459200208240004344069670478877167100399775207229333898755821663598882676213962932384942505482149226403732374566779691877583234281710019013147147031852865074587879792142593053849550696298288790392140550669148757566149340890287010165070609319602531305852082192338536563898834317348523856732385592859310350499103836804491829425290652768690488375851741621651182268988844186072124144509321521171993634297668259349972024646761345411790432296955246690864214892298624917093009784472878038315652605251020635359907919475215100542529886804298954680635728770545061279209978845326402511780865890223599985409784277252114014150291902728720705374010871569347134191077677274588495492935180664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 92) / 2 * Real.cos (169 / 2 * Real.log 92) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 92) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 92)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 92) / 2 * Real.cos (169 / 2 * Real.log 92) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 92) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 92)) / (2 * (169 / 2)) ≤ (146876016976730788960821951176764447948505414504979452270795824115042979404097593862895871121301278555643850731179442281881503407536100818838951690133861625314493328897270896094470584288647434112229509069122118366210889333697102303153053232306468963199612514277896929065938777013863955519229849870310172297761492068777769877382604200681400235628048869257515772099144111823026015416707180336968802118052682768411421474816863828448781806643166234040491676444084594464678730453235703856267731168059436263634279511997349727564295455753157034674755930559187556267358724928896923440332156820262374280827405404615817577447905521020459598154682291333450281786320819134040412868215494528989520131225385016425798891163344886705954892323372398132303009837717236246082002925949530727785415338659886894889881646160271592157492370611916141723 / 2510631421356926725175508300117135002443539189644368406493974873554066500318050149685774371505370354149466530159333708939852099460693813576681140569283461885694895270205417236604455682383080208592790372266667787444595579059751396176130959004250786443217852217742276423859541796233190426817193094303508544669411966895983362072155745908202526654051725992182388399711416604662178790026306224854665569831286493355659246419292438395884359263863803256794132118167037326263611120876917976515864818003765993896552554590453699107389948204704808494055173061327418162007857597433431596969555613100496101412876737063250774991793003655954314132959539195284905396772881115257757762982481193466956028714776039123535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_93 : (-699 / 100000000000000 : ℝ) ≤ oddTerm 93 ∧ oddTerm 93 ≤ (211 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (2305284104815180102261354389612963503235710565799978350240251483197670049516057406668286968303711528301228793033044953324702787112676270874944302710369524079406732263334640796458805388706411426003142238067777342409366655311803337625490435174984085172201529104083133680792377179533137280351150780566464422399031508025440657044996880453826568409018687432205375444982709915841395064060230068375721308310871006507663333633126648202298414679748782506261604109820113074564414233129355012980216112326833424450662194717732435386967149168262354884138283624947441832514474188747171797549180918104186232996027378629998453646516572442845533026237969259074676008420365071732594184702616020335772000340950551216206619364550771652999090589542622078137562321177579788685577287992840734012699910746628377612876539 / 17434940426089768924829918750813437516969022150308113933985936621903239585542014928373433135453960792704628681662039645415639579588151483171396809508912929761770106043093175254197608905438057004116599807407415190587469299026051362334242770862852683633457307067654697387913484696063822408452729821552142671315360881222106681056637124362517546208692541612377697220218170865709574930738237672601844234939489537192078100133975266638085828221276411505514806376159981432386188339423041503582394569470597179837170517989261799356874640310450058986494257370329292791721233315509941645621913979864556259811644007383685937443006969833016070367774577745034065255367229967067762242933897176853861310519278049468994140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 93) / 2 * Real.cos (169 / 2 * Real.log 93) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 93) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 93)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 93) / 2 * Real.cos (169 / 2 * Real.log 93) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 93) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 93)) / (2 * (169 / 2)) ≤ (324225353152874299143011094295341258705127706382423935497954401676464245737567937324942501853011170647330632569891133665675312955110682416604017731481094127275884648760896108017753740374105135560318373100086645467077109908593535475828810344730269805088593687106028272990555225717615075451829332173254102262087415563816108663140213198070596407673789822999105020216980716986847624174891486615153040176042645458910030496251665789548242202264436332264660992945297308664906403570147665546034697259489119327502486219722432364475074089832325655043032571782389236892579680255271299723801620921647261941679450669680091530256529934572133637704534475358706184081985471709670005535384081069827133004494477621692711749855484524410460636022529845401027964185108846385532754287738357808887488698241405471974990293387582803213089497757 / 2451788497418873755054207324333139650823768739887078521966772337455143066716845849302514034673213236474088408358724325136574315879583802320977676337190880747748921162309977770121538752327226766203896847916667761176362870175538472828252889652588658635954933806388941820175333785383975026188665131155770063153722623921858752023589595613479029935597388664240613671593180277990408974635064672709634345538365716167635982831340271870980819593616995367963019646647497388929307735231365211441274236331802728414602104092239940534560496293657039544975754942702556798835798434993585543915581653418453224036012438538330834952922855132767884895468299995395415426536016714118904065412579290495074246791773475706577301025390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_94 : (-5148408703891 / 100000000000000 : ℝ) ≤ oddTerm 94 ∧ oddTerm 94 ≤ (-5147511468863 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (27690150301709633899498415738374937778183001628014250123232846866529668806573058008764822190445263219469619935798325796726618127402917355300092801219123339059690115267719913210760381926768839048001776566374967409058215200572681981583143029590755500693974489055232571510876280298042496593751770348066627590951769529084144185194954971698734164780140059615859512654572329046587119185412952781782920672650760767203821714741126600787402297011159095791131004774888060713971217872795959608987891535586751828522625338382275950261144124167903915345162205312082455083682138801683684608351974778054997788189162766588990159781033833596406305242422566465547640501715690015124452502679337864283786341233505210314518801986447741210853808595663345310180106955147114753412743860909566068700787359250430687399167375522734138007811480393 / 272420944157652639450467480481459961202640971098564280218530259717238118524093983255834892741468137386009823150969369459619368431064866924553075148576764527527657906923330863346837639147469640689321871990740862352929207797282052536472543294732073181772770422932104646686148198375997225132073903461752229239302513769095416891509955068164336659510820962693401519065908919776712108292784963634403816170929524018626220314593363541220091065957443929773668849627499709881034192803485023493474915147978080934955789343582215614951166254850782171663972771411395199870644270554842838212842405935383691559556937615370092772546983903640876099496477777266157269615112968235433785045842143388341582976863719522953033447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 94) / 2 * Real.cos (169 / 2 * Real.log 94) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 94) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 94)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 94) / 2 * Real.cos (169 / 2 * Real.log 94) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 94) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 94)) / (2 * (169 / 2)) ≤ (124627395651423844595055201538653175103112514855224390636801544516260564197063599956661925999941523647220549618034010403498924904494409629645235792056543151551921126998592200547074673978798439621945196889217346999352887847485991640006231480062458723823251317292626136098718355445884400794598743198471930346848819523530548712041981245639616663406176606919702254670531772426948983746148081803311747499224736942317259476317405567063056105738395396453105780657243496208491366139250475289592046751435186559809897016113027572278893854715181536810947590701658575878786286797082239720356157715566513512988945841584936983166433076774167199872152711130632473161107881791749881390512315611621898311428764365879506213182671127776124918282361496279738324552517339012922503953170950543396495312439597189842783528410939877175544339633 / 1225894248709436877527103662166569825411884369943539260983386168727571533358422924651257017336606618237044204179362162568287157939791901160488838168595440373874460581154988885060769376163613383101948423958333880588181435087769236414126444826294329317977466903194470910087666892691987513094332565577885031576861311960929376011794797806739514967798694332120306835796590138995204487317532336354817172769182858083817991415670135935490409796808497683981509823323748694464653867615682605720637118165901364207301052046119970267280248146828519772487877471351278399417899217496792771957790826709226612018006219269165417476461427566383942447734149997697707713268008357059452032706289645247537123395886737853288650512695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_95 : (0 : ℝ) ≤ oddTerm 95 ∧ oddTerm 95 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-308769731470142037756584469342520288735559415227265792094153357752615249575219828304132568378637031845574266017094702212166356664051220569330055374158048841028461574656615857708620819108741916185179704248577000335553425857468544648647593547641529470630607128119078318308923843953096446774897663031294872023424468896138843679179853301192090590208297296008823931685277289273431516861699168915651731306715457068284851723295773334785236701595397306650171096407342445687719191422577660539171657254966350827334872172829109464535430968279398144173104872820229815013534185151247254914115159744610815432041815744244531725010612388956404112403464448342034981128370671364328526294892684953154115150675546936867009733386888710240028280207311872008792151853491361870693986968073060954702321315733278131566971199827809879641 / 1089683776630610557801869921925839844810563884394257120874121038868952474096375933023339570965872549544039292603877477838477473724259467698212300594307058110110631627693323453387350556589878562757287487962963449411716831189128210145890173178928292727091081691728418586744592793503988900528295613847008916957210055076381667566039820272657346638043283850773606076263635679106848433171139854537615264683718096074504881258373454164880364263829775719094675398509998839524136771213940093973899660591912323739823157374328862459804665019403128686655891085645580799482577082219371352851369623741534766238227750461480371090187935614563504397985911109064629078460451872941735140183368573553366331907454878091812133789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 95) / 2 * Real.cos (169 / 2 * Real.log 95) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 95) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 95)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 95) / 2 * Real.cos (169 / 2 * Real.log 95) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 95) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 95)) / (2 * (169 / 2)) ≤ (-81675386955941650853492392456555630518618570882055590516105785559412653839096784546149909711628879772148967987984144341921677397084500962229531580848481612894556324538480108793644104519429920526935477328560489425076685684543504621771001276410115175938890833848828905081484026928209065758389054075120708140534055941811915532838012216934766995387348897854354986731419136342128555862622398915527018462128082377050346306674391869470288126214561464298944289817046297815259815962253470337824989957745388287961852964702305402742894542814937810960018780642349645003681770603625586090724478225270132408651046477635965770639905272660542007715786108401191906008963885360237095763242595063995321842003424312939880804847676675366456191309171591461915505303510754054725660458928759105905683522223513026778490324171947006310968234121759 / 306473562177359219381775915541642456352971092485884815245846542181892883339605731162814254334151654559261051044840540642071789484947975290122209542148860093468615145288747221265192344040903345775487105989583470147045358771942309103531611206573582329494366725798617727521916723172996878273583141394471257894215327990232344002948699451684878741949673583030076708949147534748801121829383084088704293192295714520954497853917533983872602449202124420995377455830937173616163466903920651430159279541475341051825263011529992566820062036707129943121969367837819599854474804374198192989447706677306653004501554817291354369115356891595985611933537499424426928317002089264863008176572411311884280848971684463322162628173828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_96 : (-763132521 / 2500000000000 : ℝ) ≤ oddTerm 96 ∧ oddTerm 96 ≤ (-30519855931 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-27417005417328276468429826171795864570379155573770365504699524755021163465917365547610349258503921360614079560006890706821101696323809672002126025408917444492054049698188601129375152010648249182940025558657042041121512697824891510491008447428129595510478911333784700210428886734416421362561135483047296854869038241865825708141844306212990371075339262581669081531033975157339241695541518216220984981387698262432851677816239615490648244656588469314515217836322636779912251720976053070150683396046016542085028334439319429247316928097916069158494618706959877907607008629563876472184482592021803278971480024941679556335715058886065967237947885887653493370316443090992450624632030259280697254482513901395393103506803792327448053945055501934426674420397966506859540371599293006882134096566150317764510705421751941816173232555476995932059971 / 294486609132841982633077479813990107537466797931129410581515227379893226862012194640892966579992435659524850517578641043042534746275105670835343558683494159855201248135483040442356025381725689771107250162178870833618998137335458274971836611624578971826844457796258835371024235920614342475119523009282784564438597515787175661851224007389867166196405921099413191536679670777334827423468671535804092189570524009364056466999747221502700677057080942778171470823014064031446185075107783483783751744047182321299428082591366712167194409698850709978511042349016601891976018673017497236370525721443198330064243252659427987978743282748334603690878793562690131246105744123018634712267429628242110152444092539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 96) / 2 * Real.cos (169 / 2 * Real.log 96) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 96) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 96)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 96) / 2 * Real.cos (169 / 2 * Real.log 96) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 96) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 96)) / (2 * (169 / 2)) ≤ (-304579093038025151921749324749992322617627153813452486118045005649705816488497140507193178245805749687526737178690767389066195152736830130746467872900584568275063597743033805967387018854360090017645564788357372949684790895097413898158113627235221765041102649596551293684005742825276921228931487656115449297267847005103222439006486386148031309414214875444411195779391038585864438193707387429063523991704466597436853455289216712198695064646983103488417042059590088300908354896913529865065304795216304997365363586763461140586414343752082820179256732620475830651599015778130043034040093787009060336968566138196038692410092008734752068661806247700338805093434018542666626428465012416784209740632918583651650831062682678210462268326001797694879254472655923819214783623014453381898153028019198146585944097608281306893 / 3272073434809355362589749775711001194860742199234771228683502526443258076244579940454366295333249285105831672417540456033805941625278951898170483985372157331724458312616478227137289170908063219678969446246431898151322201525949536388575962351384210798076049531069542615233602621340159360834661366769808717382651083508746396242791377859887412957737843567771257683740885230859275860260763017064489913217450266770711738522219413572252229745078677141979683009144600711460513167501197594264263908267190914681104756473237407912968826774431674555316789359433517798799733540811305524848561396904924425889602702807326977644208258697203717818787542150696557013845619379144651496802971440313801223916045472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_97 : (-1484943875201 / 100000000000000 : ℝ) ≤ oddTerm 97 ∧ oddTerm 97 ≤ (-1484736285481 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-41266744804951519465656855727963947447952065826283872904676743872522732697927040211164472759301994547171580310663851876949103646896359891028727787563877781919017676734236392937353691778949572404436979633567241345369280369059600863111517288211926039534719353821536528081357506165060670936960687031980570266992039042063891910286760745103836676129063382016316320445683997535598787129099728271231285329098874153996034881942688730540515052837259296959248384843503700420856549975523834348268997623794432641740591915698554169658138704981256716543579968079808930362997469307023707108188161672947752949424764296662347443693852832030710467735001431687499278301217429956339489411114745092627383530633809153613270528450622881002801321003555844054093488753906999822652902947504911524921357879511718728354673617092045768855817919 / 366696837770239508111841711738236598172872585149155315330895598467902393035519024294915093704195494250418449473648299748362985496156919185428422291033413585195317530392819178667977899404687734470089214666251716618853671687141151888808293026688282953321414992927773229573264730223652019651507418524323687513177270172097545327379908303536803861598079529973071657132472922222966927768465473271714013916449667032907478387488032974146806746557728200961257030620298535665707815036333921282695667716025508478113970313234194877484745463717033389177302620179893684027124744573965194488822375876217158505706408621176040192856508687074825512212428661211774512511505027146494308888224495746761875877861288355353244004564521583457159525920587839209474623203277587890625000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 97) / 2 * Real.cos (169 / 2 * Real.log 97) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 97) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 97)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 97) / 2 * Real.cos (169 / 2 * Real.log 97) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 97) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 97)) / (2 * (169 / 2)) ≤ (-22922764379355724463734329564215724512082831314381497181030854369685803159999203409164884563081237675743770470855331828299040089318196506791922432022500609235733600125765950735903909813786257781582537674499818264118387732747572242954427415967590573587821635809062033199861671274867170671077181875184025231962936477189283680304464990348757105546665646459974241838283208685881084144021852091336225002530598797070736409003835712480258963478268481710100736443106937319175643861386637316880239194413075317559687683845475251816201992799178168004045348488708993173384964898839606301395912889137107381902479030255330188059754214560421071122573359208865202468578268094092614832999866609088105136110504911912880478630843352215189194796882850399616808912233928109637937949375628906219803450246011451714781346920398207491193 / 203720465427910837839912062076798110096040325082864064072719776926612440575288346830508385391219719028010249707582388749090547497864955103015790161685229769552954183551566210371098833002604296927827341481250953677140928715078417716004607237049046085178563884959874016429591516790917788695281899180179826396209594540054191848544393501964891034221155294429484253962484956790537182093591929595396674398027592796059710215271129430081559303643182333867365017011276964258726563909074400712608704286680838043396650174018997154158191924287240771765168122322163157792847080318869552493790208820120643614281338122875577884920282603930458617895793700673208062506391681748052393826791386525978819932145160197418468891424734213031755292178104355116374790668487548828125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_98 : (-94415148111 / 12500000000000 : ℝ) ≤ oddTerm 98 ∧ oddTerm 98 ≤ (-151020600547 / 20000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-334649938359130740062222708774561725668056461719063956060556057955603343184548814021748916861629730199197246530123647252177734032978853782744760398927224557719125271952769908972156821250351854201573269362991153571685584483256723933844418667018050780036713145332239079186191819475453157203781688987892999185089605335969403207229755582775621479102675044189316870347024450393284059189573789051158988314872997593690277472743268013808867079879509646760823895836907700934762139450467556551208941718289047690988211452351716608946085777408647208220736686905012515961647378675137770517102761985361940570380765291441944217558524261743865763462094103046028902467661290427288329103317879719281068930696605978182224970056903683904390113581023024183660263110443104935587760154866880821542520405453513468098120391101387386254088989640389520173584059287339814019137442849 / 6299803703079184997709947448977542007451124430362389445483056055239953935230769502929959146225180583184413099217391444900896208971665206342120133955463621566623994261490577622482183681575646754565460268775498711127344867623169564392800987852844121883639087884275429244485888209043392760350294718653419273548879777758860995611897278124677654871721047510565578112193985362212778299420613871228695246544160785345707901872351668861320593917190412796742058838257011217763618617090684974578465054244850296061080937024222971950750834022196052018626220396671012038613833419430135853487086167765488159904229017622254182748400950526905093919435318818550541045453027661335141030900185314953733419180102095642671238108450779691338539123535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 98) / 2 * Real.cos (169 / 2 * Real.log 98) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 98) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 98)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 98) / 2 * Real.cos (169 / 2 * Real.log 98) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 98) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 98)) / (2 * (169 / 2)) ≤ (-594761371726712074426022320277631222726778870429858014946904398534058168202353632066025578228179998699738581820955835246552042500188553352219881987745366226246528328715952931569650483227632992431829065613710903265628544261246753397250109268403122124790702752593827472479533208797838880959287643924772687883132542481378986484821179919458804972281139317598286270848242314070968673963385539231366271226760271847987068469247414199891600709561299851187718259574186645998077653567605052298071954552515986594303418139050362590189032075520392488703593884724016184918624533768172312275528555548758203798490841523267178264006950607555393281160732891095273675575219839614214664139152781039114843158933679386388480143744050192633731896411836909500586861605167588349067992692451527383070157325308739648885112392321116360337489957582244920884082928119955111 / 11199651027696328884817684353737852457690887876199803458636544098204362551521368005208816259955876592327845509719807013157148815949627033497102460365268660562887100909316582439968326545023372008116373811156442153115279764663412558920535089516167327793136156238711874212419356816077142685067190610939412041864675160460197325532261827777204719771948528907672138866122640643933828087858869104406569327189619173947925158884180744642347722519449622749763660156901353276024210874827884399250604540879733859664143888043063061245779260483904092477557725149637354735313481634542463739532597631583090062051962697995118547108268356492275722523440566788534295191916493620151361832711440559917748300764625947809193312192801386117935180664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_99 : (-683 / 100000000000000 : ℝ) ≤ oddTerm 99 ∧ oddTerm 99 ≤ (1 / 250000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (213711215967105700166054609112625401283603554915927743221280936460417954968364634112841683080164503405711729508468703005372530649733753256799034039056152340553184525965926312317504336252965857789452869005913364745188500414372377411648253897797913651214447123108643936249686529912306061890584720898123322189086536295890660927529806298930398534404724142342659774121999872514993549034914554343094199601326720496513632259006250670611033841728809323374498616593544479990818059264877610220181274241124913022278187884472156885142903699013308415456682909869659142392698050020248575283910588768741446272522084559966517872599403851784753305982595084708192558122406510872805088407942635611175296594920116355545700208610924861410601797303207554578713044626667130977954358979482277683809823024063454313913174776313025235908919683371484892746074976924163143033 / 5891750631251668846031805605424120135729370907504895573295064128677926359278564420158555531800029169801928589028902632877554754140993256502005993353945257779612055393841869437000576884188692397179858358677416178455476426185448087347988364340606803403250722703155687453761820869633434719976633155662279131680792993394448789186156063638307232954291077340846591901925486589959316741080163560250906651919160945315897338573227655464418881918035878560480659629085931526483510791007528463205979352235064938555809623807854392786847043875235266651424546124162735778692713096871934832417495655094402266641921439532761923606746208863528810672398911158341092008021859399626988292811008622726613514060127501511378962036187466258133205119520425796508789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 99) / 2 * Real.cos (169 / 2 * Real.log 99) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 99) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 99)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 99) / 2 * Real.cos (169 / 2 * Real.log 99) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 99) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 99)) / (2 * (169 / 2)) ≤ (120261088503992285134102426477751888745491527780675525119635426308896658037334685860571076867531377143582024743615590265698524035696332157115467250308358251791349609893714492223788513299243006259827877019788896635804329282850535922495380871799405581089801585430164858483657189616064953682223331871918763249107069174093121758277177244257360113670929592807514951941021046434142580178867206717281175960633901205680870774675285538706837964869599324542462149689738307317430054166294629377750154060726864922529607431679785774993736315106110697957468815619576659478899801570414137956069798396481467102099930893063789113671707670505979220562385736514453412599307450738859436862943708504497372727069108810654598733134915109119857022279691297751492790170801778538960175328588159338488539955835843679150052436474817024364163821561615672358232032850409676786714029829938941892028673 / 3314109730079063725892890653051067576347771135471503759978473572381333577094192486339187486637516408013584831328757730993624549204308706782378371261594207501031781159036051558312824497356139473413670326756046600381205489729314549133243454941591326914328531520525074192741024239168807029986856150060032011570446058784377443917212785796547818536788731004226207944833086206852115666857592002641134991704528031740192252947440556198735621078895181690270371041360836483646974819941734760553363385632224027937642913391918095942601462179819837491426307194841538875514651116990463343234841305990601274986080809737178582028794742485734956003224387526566864254512295912290180914706192350283720101658821719600150666145355449770199927879730239510536193847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_100 : (0 : ℝ) ≤ oddTerm 100 ∧ oddTerm 100 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (557368791358460972217311162813283926474868130515408803966669595752223664977674568276698360139562278462831359673900802572775944317726157218525707018235453716200036017291076500245624688139046662262045542044757965362869527939661938980268841048448884110669348284598410054851313050916132518347857006414328123088375687570053697867816080207473928775425502004724365621290762431671641062709107785558746105297084129486128996569144145808249506156110744931085929847800445139344592890917859171000520693749015034974416176508545387017175636672741080762534059705127999678421921897800143703443436587592889270438764203651157125407061769944577556582674083073484859396039351605875960305131032444667394109789898284863122759402459918397980909176075665266569072795613061411517466487546151705551083123197745472701115554920278797367725591849242620805870773752380159392915952304163927 / 5994911204165858287469763738059635382414273667649074998238640695243752168896748946089301782255814812534391958586021732792767701190643662475435096095984361213780896218149205224722909879807762780532696200866385608615622085360199562383163291286462971526948992570344805402063017154910745183145885253544725503557161868730047360686491169663921149196992999929708766999326821393528624069862895268580486129377712838377352904495631578456468508759917923987969201382909403206909503091390181075197773087223214201755876593165607542762676570889541839782087207988548277378367127721591020526680382061790933139936876921499836762938129810940074585408780202052730392477978992773569379876448636870131036057048626095164306968906574962044626440229131038870277404785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 100) / 2 * Real.cos (169 / 2 * Real.log 100) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 100) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 100)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 100) / 2 * Real.cos (169 / 2 * Real.log 100) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 100) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 100)) / (2 * (169 / 2)) ≤ (1254269937744829278359439258603857154876699934768018847964281382284101505211328181384570320585130646374527222991398591506238294648441854182256654688888588758789271288227980277446694404326281546445976406984983040728162675826143747891908517553239786759151411266835212693006057594903338851172537514932551954131268780356790355536774180175343263852563368984996276744387455605155663291745526836028170326572947823403110017072139400059061700568808409289999031997752553729197654089816475138396414363210098163398593088070421361314638353794177430649968391185181061357396776491071970000801398370307078198938238385918295416771129289097247276687157952071805720654190000590792421400649555448821540871119093676849844715729438915714670145300313208350578670171837646329154356439523232115853044987475233582785500356741051371220102045791830889134707945632364615817451783562465452215535638412489104921129 / 13488550209373181146806968410634179610432115752210418746036941564298442380017685128700929010075583328202381906818548898783727327678948240569728966215964812731007016490835711755626547229567466256198566451949367619385149692060449015362117405394541685935635233283275812154641788598549176662078241820475632383003614204642606561544605131743822585693234249841844725748485348135439404157191514354306093791099853886349044035115171051527054144709815328972930703111546157215546381955627907419194989446252231953950722334622616971216022284501469139509696217974233624101326037373579796185030859639029599564857973073374632716610792074615167817169755454618643383075452733740531104722009432957794831128359408714119690680039793664600409490515544837458124160766601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_101 : (3852168564119 / 100000000000000 : ℝ) ≤ oddTerm 101 ∧ oddTerm 101 ≤ (3852787873531 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (15346726134905619821621789988340839787396531363227639463737292404793154815307514966150263125944357331948802200351426541716668963632814630860196973278192139038759381074223052953556244273747748566887153225456338069143548284692825147255135402837715766511178877724389497940729233048585812178648968316425551706216315990733062822370449710847209712754200536937668232426179901562123331595872916182230059446613289273449586559883059549505088346886582381609812646105052155908293083988033719779136926305865308820503910058943861804441407753735393368212040172159653683643476163129465050263859955807007909294010094809275890692143310535968809990871118138737455153635458853714084160528686639902238511472224928242818078350313942961019637857536092627018180258486561744002283595166418618435719719801940175602393847277950141683082209854258735552764719123920888035099004866305646459355052604127547889 / 182950171025569405745537223451526958691841847767610931342731954810905522732444731020791680366693567277050535845520682763451162756062123488630221438476085242119778326969885413352139583734367760636373785426830615497302920085455308910618996926466765488493316423655542157045380162198203893528621986497336593736485652732240214864700047902341343664459014890433006805399378094284931154475796364397597843303763209178996365493641100416762344627683042113890661663296795752163986300396428865820244540015356878715694476109790269249349260586228693841006079345353646160228489005175507218221447206475553379514675199020380760587711481046755205853539434877097485122008636254076213985487324123233979371858173403783090422635088347230365797126133149379586102440953254699707031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 101) / 2 * Real.cos (169 / 2 * Real.log 101) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 101) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 101)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 101) / 2 * Real.cos (169 / 2 * Real.log 101) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 101) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 101)) / (2 * (169 / 2)) ≤ (34535685164761714866274608991812584028611483832265611614861300438577536260158043228011869267150079115131945723131656448379954640110681950952728511629095164099949983500496591437460485029722093968020066124187996586912159565838201640123349652345373937712677150417672600667685679712505502302115480990071893115947903419164445144951624673184008709912339326331841549123486646822536572997289476707803563798177161238536151683998103213427621481770334483211060068631495193128246185042425747404122236783136274761732857078397031585538676393129917390690243975483029845705343266072388877132554408076278033464781094234380923887068156861592813255568135003128821012510373498927732903834331058812331639286285511539498252262515777028373153861184033501701025396940885479296118276398089161522097235804717979461323380504052212559385913883725759434449933519476512884899084435427933391443748471511712497 / 411637884807531162927458752765935657056644157477124595521146898324537426148000644796781280825060526373363705652421536217765116201139777849417998236571191794769501235682242180042314063402327461431841017210368884868931570192274445048892743084550222349109961953224969853352105364945958760439399469619007335907092718647540483445575107780268023245032783503474265312148600712141095097570541819894595147433467220652741822360692475937715275412286844756253988742417790442368969175891964948095550215034552977110312571247028105811035836319014561142263678527045703860514100261644891240998256214569995103908019197795856711322350832355199213170463728473469341524519431571671481467346479277276453586680890158511953450928948781268323043533799586104068730492144823074340820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_102 : (-159381232933 / 25000000000000 : ℝ) ≤ oddTerm 102 ∧ oddTerm 102 ≤ (-318580939379 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (33961646860558613761337292698585238066740952059853598737522178444058095396945537773192315017765826797089162436288182119907560400084320889176307283661658293641703324482385200360951510754928537054770043104700657242611475860524845737382293771013265014502724493562425317092045000844137262097360545638809453668493741965050056724996126576143322677874446132570425693648299571128899473044384386552323240393044404794906457994633597330040145033795673950120005430311442771065036133961414559222378728621524378780283523411061223677340545960866084407626682677313562132130773282297033776151298147519454062525042510285844186873007664740529139484865809127769832208550747557159713690007769698839167815914509380142919956091524317378441543387322922086461590360768424094552424456987674236862222206989375089072509209807891000899331708213628985093855865682042139903816181759600378235619461610682231 / 1498727801041464571867440934514908845603568416912268749559660173810938042224187236522325445563953703133597989646505433198191925297660915618858774023996090303445224054537301306180727469951940695133174050216596402153905521340049890595790822821615742881737248142586201350515754288727686295786471313386181375889290467182511840171622792415980287299248249982427191749831705348382156017465723817145121532344428209594338226123907894614117127189979480996992300345727350801727375772847545268799443271805803550438969148291401885690669142722385459945521801997137069344591781930397755131670095515447733284984219230374959190734532452735018646352195050513182598119494748193392344969112159217532759014262156523791076742226643740511156610057282759717569351196289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 102) / 2 * Real.cos (169 / 2 * Real.log 102) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 102) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 102)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 102) / 2 * Real.cos (169 / 2 * Real.log 102) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 102) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 102)) / (2 * (169 / 2)) ≤ (38228622852216150065131315639785630240093225191204430966486849641255916560610020190237605252279953227959567556497346967652165764778641717951817782127869709409046185409466992599000099025780347234887456568862915608120270146220902749849394053457237691801049247041626065126201642173219074749396291188756097032980022817411485896318567586224077173038065142929206504845216764354338161049722678463959839498123646490956210824611798683105585456015505862479282809789574685476371067159051944959969331571553311748000886018239152081027515382435801143277413330950802629557039108497690408639540316179337775854177496404321337055947734485225346586777386282101979326535835514492143800932101909221690380928140322963045743863154753212507338315869793699736454782370758053430832699403809993165757388136262655833000891354683798666455919678696911058953728635856591208018543664903696751108246842523530631548967307 / 1686068776171647643350871051329272451304014469026302343254617695537305297502210641087616126259447916025297738352318612347965915959868530071216120776995601591375877061354463969453318403695933282024820806493670952423143711507556126920264675674317710741954404160409476519330223574818647082759780227559454047875451775580325820193075641467977823211654281230230590718560668516929925519648939294288261723887481735793630504389396381440881768088726916121616337888943269651943297744453488427399373680781528994243840291827827121402002785562683642438712027246779203012665754671697474523128857454878699945607246634171829089576349009326895977146219431827330422884431591717566388090251179119724353891044926089264961335004974208075051186314443104682265520095825195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_103 : (595466308389 / 100000000000000 : ℝ) ≤ oddTerm 103 ∧ oddTerm 103 ≤ (148906606863 / 25000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-8601254650786208954078839657839424321391907667134355510918962381474809146107362764663031447570334034507711933206697481115834622945692066238029145651737546051624621368181617555497606103948218113472537967594359906643460416630575371963304081666037315666181839078900166773795595770133426053968612386076405025326047510347106729793655763117080211916738525606486457755327087682556209207497658747061617548433327197747482247402058773123143396382829266344340461098129015190100884604591205785618556585227709152667052685759797011008762232562111751458759225515067080305453457941580338229313644384487523436585892808737940727100129043413772516547653851239868397321870322964904762007472335877668822329875869068156683486138405879317020949063928015023308154752174270365897755662477727354720751875757586898635092447369129529343993921420154941074129968595167839750784655692276043561751056465683512821939033 / 187340975130183071483430116814363605700446052114033593694957521726367255278023404565290680695494212891699748705813179149773990662207614452357346752999511287930653006817162663272590933743992586891646756277074550269238190167506236324473852852701967860217156017823275168814469286090960786973308914173272671986161308397813980021452849051997535912406031247803398968728963168547769502183215477143140191543053526199292278265488486826764640898747435124624037543215918850215921971605943158599930408975725443804871143536425235711333642840298182493190225249642133668073972741299719391458761939430966660623027403796869898841816556591877330794024381314147824764936843524174043121139019902191594876782769565473884592778330467563894576257160344964696168899536132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 103) / 2 * Real.cos (169 / 2 * Real.log 103) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 103) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 103)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 103) / 2 * Real.cos (169 / 2 * Real.log 103) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 103) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 103)) / (2 * (169 / 2)) ≤ (-3821752189018496646960193014412178429270348726161363544806773868410471805625952847167878667582931749675737071216737604022057525905466587896957627050955130015614304315829460978729752724558221062823274056944527108536490059652820934048911144071419983622733996265644013275720853728186503384378973875659622850804150364408753551749934362306441072566887908814544779322065943095548147230338987630605745316850796130218856440152045667320130531366323795587933536879456468521275800470283390717439716370028247230347972180344877221872908890102864456509157358630629931941219472314476137157833077850895649436439632159187653704684855474550549871835289063857530721699939542433619569979576323376996322946476391014635534196023604517834019510464023809848836543641983731865000299946773210469129844987647423768270347468494856092279193528547383751342275932450114734089243677940857724273 / 83262655613414698437080051917494935866864912050681597197758898545052113456899290917906969197997427951866554980361412955455106960981161978825487445777560572413623558585405628121151526108441149729620780567588689008550306741113882810877267934534207937874291563477011186139764127151538127543692850743676743104960581510139546676201266245332238183291569443468177319435094741576786445414762434285840085130246011644129901451328216367450951510554415610944016685873741711207076431824863626044413515100322419468831619349522326982814952373465858885862322333174281630255098996133208618426116417524874071388012179465275510596362914040834369241788613917399033228860819344077352498284008845418486611903453140210615374568146874472842033892071264428753852844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_104 : (-156263643397 / 50000000000000 : ℝ) ≤ oddTerm 104 ∧ oddTerm 104 ≤ (-2499846573 / 800000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-1061346538822969156227711805271231807710385232665596434443419645253450109903249855479534080067783237976315302209855693918129187603727141243348175772658241992945759330314285087476347326244500532076638516472201887107255182065912596501052950043101947941169503177858817877675825531345118389403363571223510721066039985633804597598801204928463886583453570170924092088400531159274756659227065792978118529183525838179800544860282432056793723344657859281060151362558759158559193271893915568951662310077334706979818178337308164439241334642495185841311922591064888411581224845836015885836246192514059922175904929090483420567194706408902961229564683885106504906608180477864734223438287921192121869739157100344232981964487192804749788670457593929104645463477577495909837259454512020955339894897844554555675449298399677025320483263202411671807773200507576874844230432461466465005380122585618112723 / 13488550209373181146806968410634179610432115752210418746036941564298442380017685128700929010075583328202381906818548898783727327678948240569728966215964812731007016490835711755626547229567466256198566451949367619385149692060449015362117405394541685935635233283275812154641788598549176662078241820475632383003614204642606561544605131743822585693234249841844725748485348135439404157191514354306093791099853886349044035115171051527054144709815328972930703111546157215546381955627907419194989446252231953950722334622616971216022284501469139509696217974233624101326037373579796185030859639029599564857973073374632716610792074615167817169755454618643383075452733740531104722009432957794831128359408714119690680039793664600409490515544837458124160766601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 104) / 2 * Real.cos (169 / 2 * Real.log 104) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 104) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 104)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 104) / 2 * Real.cos (169 / 2 * Real.log 104) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 104) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 104)) / (2 * (169 / 2)) ≤ (-471639444904574219307119949569808438667311502330760027565483318929181024807019597705739968380499833143456537272671522129173959760470141018688760033730955739795997048385873568430420210332924972085429672441005575540950417580818281947461532908097689250067121843894613052336943200352550983104623061597802699317484343339602149927244627227220583362990445601900835070739511667604934077232485070153404957773458479697115236785427065986740008651857425237980934045392132883603655210381419248955756180925983356732393417988541616062671690469564318841678330153789190231858402288064591374258980348479093301744086159863419360748824424659576082820915247581733704611772652350391052057220118407261007055193065859898736122837357548380038415081929618556734659711714803892861444310306790114689808555446274776903572432042273460948480127385010637956128951015189962894254247069124789 / 5994911204165858287469763738059635382414273667649074998238640695243752168896748946089301782255814812534391958586021732792767701190643662475435096095984361213780896218149205224722909879807762780532696200866385608615622085360199562383163291286462971526948992570344805402063017154910745183145885253544725503557161868730047360686491169663921149196992999929708766999326821393528624069862895268580486129377712838377352904495631578456468508759917923987969201382909403206909503091390181075197773087223214201755876593165607542762676570889541839782087207988548277378367127721591020526680382061790933139936876921499836762938129810940074585408780202052730392477978992773569379876448636870131036057048626095164306968906574962044626440229131038870277404785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_105 : (0 : ℝ) ≤ oddTerm 105 ∧ oddTerm 105 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-11338473645945274042513530163410064070165691432670865578513849317966882417104386774839629438837010511013604241846238011339658041930332165318070591646641237770678925225202397689126775803465603047169626004184912610932425363844220903561220167881153481048884559178560494904106293302523317042501491848377634391009969413895799903404941963021674016879388196549766020420480080253281573573353827977020637884503670330937196865727070116222076019094544556765145364115695351337799706654158541214854968815564473378295916399841346736968962305966367815832712927348208881483869749861057753269447763119491407063810205152220672989493064828430629798252359489515541362993621432188691478018187070674149079098816561721330517634902762193245729868896937523823254212135305209240074911454680059221635372702264937183613322074878235172850751916749784369429886805649442052984421862612931206878928066340728708073 / 187340975130183071483430116814363605700446052114033593694957521726367255278023404565290680695494212891699748705813179149773990662207614452357346752999511287930653006817162663272590933743992586891646756277074550269238190167506236324473852852701967860217156017823275168814469286090960786973308914173272671986161308397813980021452849051997535912406031247803398968728963168547769502183215477143140191543053526199292278265488486826764640898747435124624037543215918850215921971605943158599930408975725443804871143536425235711333642840298182493190225249642133668073972741299719391458761939430966660623027403796869898841816556591877330794024381314147824764936843524174043121139019902191594876782769565473884592778330467563894576257160344964696168899536132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 105) / 2 * Real.cos (169 / 2 * Real.log 105) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 105) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 105)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 105) / 2 * Real.cos (169 / 2 * Real.log 105) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 105) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 105)) / (2 * (169 / 2)) ≤ (-10076783778550210562220040450859422474336269579101527246348847023258456901369474750689758803626482098639537646298022030525137796195459371609618699314152413522574625501480166407519703571274183361081782727915617224633779142027933673470903969564957776098336595616655282676482887271177158973536070152017210168023482872163344387170140147107739668220860037349518317570059353841476974309007159891459061779967725510706424387006187883856851995772892321633938297446723051775211283476886080797658751941040184240448918624902694090876619865783434966101271831528200370961398147573710275700587270416730599691854867979542334470197134822082013979706338217992266110783859421093481188375920000323120626830260498746183312294906812190327882587216228407305411852647468900026211757473180507884606743383614788113808937833091225599734428386064720852519980056125931755874980184494060115003119110453923442841 / 166525311226829396874160103834989871733729824101363194395517797090104226913798581835813938395994855903733109960722825910910213921962323957650974891555121144827247117170811256242303052216882299459241561135177378017100613482227765621754535869068415875748583126954022372279528254303076255087385701487353486209921163020279093352402532490664476366583138886936354638870189483153572890829524868571680170260492023288259802902656432734901903021108831221888033371747483422414152863649727252088827030200644838937663238699044653965629904746931717771724644666348563260510197992266417236852232835049748142776024358930551021192725828081668738483577227834798066457721638688154704996568017690836973223806906280421230749136293748945684067784142528857507705688476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_106 : (-111677198967 / 25000000000000 : ℝ) ≤ oddTerm 106 ∧ oddTerm 106 ≤ (-446195914197 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-1112309315059375319068023806752605698617013169477302294878992763318063987671637316147677952152450926893853455735197837438407709697869955097094501544863204582409393943832784667694838559182375321976875722779317988319624409103324127697649774499358657860842383790061940893260395504380505494821572821125548499345963976083649750991146000669046490286630323424001387597360081663876736414304331779361612366369867492700355995084642316520648665203521769947427970812148539135330579063529727306752402641885577774551222227833491753572566876548726321967671207912904655275843648667967765525456899278503445744196338448721007271718828253635369264645613698026253037222845675035831796395509738785077833184619884887576724975670315227512401141140986826443504799768394769764927665956603346748679332989501618759667974463304512336723443313123350334887435278059801591953468982359384107310780218589515367117682240392959 / 121887722241004696652826752488906230138729510378202698067112879430730353175460061144158186535771018558914616907825226540134174279094227518559497753637822677215946696121038135333509017579831221776117410073050258711630944403579071735820006899387777853940614805185045799642405275474100114189164105194519754631469383494059510085112354890186569655425059376137296535556923175249007285143617699935885286846746077420933664523386336797812021927840752013571853604275119822529799563222362646265548676531902357158112747065431865389100604996032385828760499870226412804688751568195564302368808075945951215456961708621389441304478332575081979043255664194902600034875129861863085767607629694281888056327753798765988093932006373754017185206402617129595003559964243641601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 106) / 2 * Real.cos (169 / 2 * Real.log 106) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 106) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 106)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 106) / 2 * Real.cos (169 / 2 * Real.log 106) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 106) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 106)) / (2 * (169 / 2)) ≤ (-4937921044871724716604244047385935113211948036251024073649131551968001968465377971507068138475106493785911420352345939188217684745164852526812748143252726425517922977187537975884825345805476303530521603847855235401783904685385498026028674909096342201560203409025320774619527403174461621902248924167380393049848350972747738365940509917913536564473609333403549316845364621615422138345634597744934231308808594526791784860562928812701421755584144579113278606162246951540284598950382632909173859915886548045403156799662905922115367243849128217459083785657606529154452599886451469685380433667470417789117738881334467934583780828180838196689357225076078785618626753583406588360456178293741527470405061471649967300097991250374067943786927325519984703478237107472540684396107510042715870279729025173374508360920694581971402501061351713421485878277585845051485081273463203327683202752686511 / 541723209960020874012563344395138800616575601680900880298279464136579347446489160640703051270093415817398297368112117956151885684863233415819990016168100787626429760537947268148928967021472096782744044769112260940581975127018096603644475108390123795291621356377981331744023446551556063062951578642310020584308371084708933711610466178606976246333597227276873491364103001106699045082745333048379052652204788537482953437272607990275653012625564504763793796778310322354664725432722872291327451252899365147167764735252735062669355537921714794491110534339612465283340303091396899416924781982005402030940927206175294686570367000364351303358507532900444599445021608280381189367243085697280250345572438959947084142250550017854156472900520575977793599841082851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_107 : (261773958569 / 50000000000000 : ℝ) ≤ oddTerm 107 ∧ oddTerm 107 ≤ (130919160337 / 25000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (1317306399471092028399355706828890926760346446624328530627612244550504668961819276976139071168116205273021355514772792458680780593622762415289730561947323194502810156611496803803110166867090415386873606748301598880881892256775817069047865782770547834866265559941323765589044657925468090158204984477877396184628577909863463486313929046034566193167838809926171495443109822997402653764258853335406881977252777109524176351037323752360184700372461147405465667986907562676022884192253301020142311532609982374380327512462696510080649679530502092061930210321510335923563486527124542435823723958376166517134056859535612597550430677575246843769804651671498977167281421903391959600636401092538092534072880972296192682823206995431879555012338636964005193475678557085505228024610176765918314174218474542844977531735658902162515587004636030292564690572769366093178563304625310023919431909 / 32289219496251396775994500183769393003974890809112839716570345409904679503827641048473301605587805260264772019869811413058750968269302452553510070810800837732936725648519233950908718527643209504052641676015392597948430486143713987090854353212721574025846800588249047502519097718689207021173928895134331022757790749353702885604528556979118361850595308975987046442276418275040331189796050372623148718607711108772930707768953322784641564644906789348351585672993083140532059993310145872314420417123995134065614028886123601357302399749858069091505440136171130256851929610454851354177283166766488673147018385301547925863883912585041004619509430700567042794526911275409530959561055046157851835821416316029255637064608932605633525425226722715961551656787565443664789199829101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 107) / 2 * Real.cos (169 / 2 * Real.log 107) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 107) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 107)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 107) / 2 * Real.cos (169 / 2 * Real.log 107) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 107) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 107)) / (2 * (169 / 2)) ≤ (741167034593118771410799087994609686786175960628324965061394687492985747463599972954314932416603463866798537992258185792208827699136002137967791031562536975209938076088365125634587459753911106937161685197165983618478291900786723454879614892335978241487586456869543269956178304922030755390386287575963418438171597028989438921585401266942671964603441399768863318631000833853658623817856810889539374254291071652906418151221740827319738818651011934067989083812601632528815681773906840261358799084946323902029099163357431666963355568262935494917484935724154390779360884233145413589864649550865888987850294089418869296567353928343729446063732753115524639322429027808242538774254961018702410735475673075797506149422682585406496519944858749002769578040603460140117326756190389995196933562865446958962763945370825764404391997656682093032939068167740961255920100899582775509164917602644366387239372272792821 / 18162685966641410686496906353370283564735876080125972340570819293071382220903048089766232153143140458898934261176768919845547419651482629561349414831075471224776908177292069097386154171799305346029610942758658336345992148455839117738605573682155885389538825330890089220166992466762678949410335003513061200301257296511457873152547313300754078540959861298992713623780485279710186294260278334600521154216837498684773523120036244066360880112760069008447766941058609266549283746236957053176861484632247262911907891248444525763482599859295163863971810076596260769479210405880853886724721781306149878645197841732120708298434700829085565098474054769068961571921387592417861164753093463463791657649546677766456295848842524590668858051690031527728372806943005562061443924903869628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_108 : (-244075907599 / 25000000000000 : ℝ) ≤ oddTerm 108 ∧ oddTerm 108 ≤ (-61009610787 / 6250000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (15696645810418300302369379327255118653142831408344402352533325531405966508919844770860089496952608984285751789052140321796048478148532367953767108103388104532688555007198352167038712499594946165500488148227844186295951411190170768390730310892340373762845821661450373118982647767136381348130841942302922390335996709620552477401192158187978525175467520563801930739737729171665676552754587746330178921336264649595731333969321813535961390835106768000543813614512167947047104761971455427837551414349661361026220635343206654131379729846915206675240570256435026675696749509428057358491977379946347300145315218506749075603989588348701263520439629922187018018905369904888544216117753981032215126375716872574982944527743262372726228830779348674541544725270719633396540162391164009921901228645168777756999079225175465289464061403239156335535581749005538705639486777574274893771293 / 258313755970011174207956001470155144031799126472902717732562763279237436030621128387786412844702442082118176158958491304470007746154419620428080566486406701863493805188153871607269748221145676032421133408123140783587443889149711896726834825701772592206774404705992380020152781749513656169391431161074648182062325994829623084836228455832946894804762471807896371538211346200322649518368402980985189748861688870183445662151626582277132517159254314786812685383944665124256479946481166978515363336991961072524912231088988810858419197998864552732043521089369042054815436883638810833418265334131909385176147082412383406911071300680328036956075445604536342356215290203276247676488440369262814686571330528234045096516871460845068203401813781727692413254300523549318313598632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 108) / 2 * Real.cos (169 / 2 * Real.log 108) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 108) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 108)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 108) / 2 * Real.cos (169 / 2 * Real.log 108) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 108) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 108)) / (2 * (169 / 2)) ≤ (8830718726492108877389390625271251083235493415603196820145251195447626749305517710297359119735326481649869339098296592461173078813699520479614026869229361367979870472962564725541218348084358635774764536453786777318195682949627205434853185980799935593170545309908928343215437738922782755018018624076393144673102910027196168871834617609297211719440374476508050819568615544431962186377801436271286002030692014827482260430518697551787027054556934116584116910091053592614682441803143823144734866361288685034456205160752526887080983033453564927262275992917915584703018878268961117186689463602810974845727956617741414552899086897419308731033832269264022669686996421585363755190990453474747061440268808059945067816716435622554711976038054515384897394601524335395716371696017754476243525458650101339922232704131366373152067544258361033985185478947180155998432346266013261567226699503820416151654762099 / 145301487733131285491975250826962268517887008641007778724566554344571057767224384718129857225145123671191474089414151358764379357211861036490795318648603769798215265418336552779089233374394442768236887542069266690767937187646712941908844589457247083116310602647120713761335939734101431595282680028104489602410058372091662985220378506406032628327678890391941708990243882237681490354082226676804169233734699989478188184960289952530887040902080552067582135528468874132394269969895656425414891877057978103295263129987556206107860798874361310911774480612770086155833683247046831093797774250449199029161582733856965666387477606632684520787792438152551692575371100739342889318024747707710333261196373422131650366790740196725350864413520252221826982455544044496491551399230957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_109 : (-1980321258331 / 100000000000000 : ℝ) ≤ oddTerm 109 ∧ oddTerm 109 ≤ (-395984425743 / 20000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (647498408913879882539898159623765882068465347540699055391817982097241492018155607726181593450087791957282994222114487917842711820705169990216074129142465867551420735623746044092710962348126482641835027118784725838494437855288698198468529642723874360339668094873547946512822570419181571800951786903599327209245862082228622837805693770912246064580927066302624901936981374809709565884440464469689787419298332602333358523954403887701299910066572807764169391180740178787223258640617336518193187796522115007347468371477069078874321871948897196909763642641843788026746272860806521767984960378579921586398250929845638529828578670090302515194968957297031520879564937789219273098923140305581064370359949106677261391635844933334815616091194687212592323642979399964764788362904766354753184463001390148214187083575668806875555361584527310016852439534896881146045036133102478441594102240569194277356485414243 / 14695182561849524577163719194746603749364572528236243497674681644329951916408668637171849264054183371782722910376305283098738218447895871739908583337893359039345425361814975806991345676580731792066624478328783120132974585693850276791571047862145285245540943912163122063368691583972332439858712528274468874357323434372529668826238774376274312237782042840626993580840467694951688505933846925140490794601909411281547131002403645569543538753948689907872010546286629838179924192510928610333318447615542674348083895813062474573278958819490961222089586977528549948007278187158119016301127983452837511690020811799460033815385389549814217213501180905502511920709136509341937645595786829895840124391613470050647898824070909772519435571303184027175390620689096450805664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 109) / 2 * Real.cos (169 / 2 * Real.log 109) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 109) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 109)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 109) / 2 * Real.cos (169 / 2 * Real.log 109) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 109) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 109)) / (2 * (169 / 2)) ≤ (728582554004143097717723851819419488577281150766158956264712556224014174834667857614418545172675789866177310029682527498996877556817115054167652911023502480109612236553563696469694677515352722403371326408110504981141492304372621595044690862187529765909949467103997021608467847562044814754127935127021626277623598189506550580551306650938794112971375371954873715472911685015986651323313689958947455100074845381818118529491687844385902761674219113246377654547798745801691155763714667246381616049968730777953096148218478868354345615376458238313016557541163275745341847666303208000952778718041680054016393358523557845185088130866621800935014201690662331853048553689970271391980009217335292035546488745892047494263037453305621193737609144334154495905593530275203307773843298372339964204789388169722764909073393737333375048128169773983722654258831168044245872743368749445554009670736134333227070436753 / 16532080382080715149309184094089929218035144094265773934884016849871195905959752216818330422060956293255563274173343443486080495753882855707397156255130028919263603532041847782865263886153323266074952538119881010149596408905581561390517428844913445901233561901183512321289778031968873994841051594308777483651988863669095877429518621173308601267504798195705367778445526156820649569175577790783052143927148087691740522377704101265736481098192276146356011864572458567952414716574794686624983253567485508641594382789695283894938828671927331374850785349719618691508187960552883893338768981384442200651273413274392538042308563243540994365188828518690325910797778573009679851295260183632820139940565153806978886177079773494084365017716082030572314448275233507156372070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_110 : (0 : ℝ) ≤ oddTerm 110 ∧ oddTerm 110 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (189507282288823311812531938288899703293630464879742852504213799729487980856193097653701770948681006015785881029528007531852542833303490331753467399220187416787029397945875183296256266701122738399419117049293493637901153311724481060995213348798612719674565433157340885160627057949173220654859630593766188003619559069856422428355097023515389547687441799050645939660893437406206820952412881457651592009427185396193301514433631642890794937882114868640876384409112294710449436520135777841541872367147252395590733472540557024673722324089860192576819614807327894182721934219443393883660723068061608600413203869322055841373562369947856368904595865112199166228180949472664226396364949769569552507116560191133352274772252726298626816633655048585802223105121092444076744173889196668203751095528859874609006865044101562680528477440589162488351640211934277159941446878057261266236941711 / 32289219496251396775994500183769393003974890809112839716570345409904679503827641048473301605587805260264772019869811413058750968269302452553510070810800837732936725648519233950908718527643209504052641676015392597948430486143713987090854353212721574025846800588249047502519097718689207021173928895134331022757790749353702885604528556979118361850595308975987046442276418275040331189796050372623148718607711108772930707768953322784641564644906789348351585672993083140532059993310145872314420417123995134065614028886123601357302399749858069091505440136171130256851929610454851354177283166766488673147018385301547925863883912585041004619509430700567042794526911275409530959561055046157851835821416316029255637064608932605633525425226722715961551656787565443664789199829101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 110) / 2 * Real.cos (169 / 2 * Real.log 110) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 110) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 110)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 110) / 2 * Real.cos (169 / 2 * Real.log 110) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 110) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 110)) / (2 * (169 / 2)) ≤ (10674696003431538357377833929865876740306202779730845088750925259706544125678094573217025156173082657559822372554327241497961157556555049294091439599238249114601458332375284239041585846352339655644711742298747011452564781641283954797074976932083589154762102149498581977161565272132185480964636829693686053458150758583456733604924590321326421332036901102321803037112278189802542730623530207919273083060266369680420508896003957504342982959630356654972340193415699429988149297042418801186794623626909773774717190841919061338486498295101436321354598559764123408714863115130112626925715453779620230409825657614433035957744494591011264909181139271764466050435178472505705653609160663984434064474377843798581669843687755338685364175851503551213553012941540117365183124177936008078434666581232495729998570293367817777228559647412514673024370076073382225456876824828429408311990449902046243687 / 1816268596664141068649690635337028356473587608012597234057081929307138222090304808976623215314314045889893426117676891984554741965148262956134941483107547122477690817729206909738615417179930534602961094275865833634599214845583911773860557368215588538953882533089008922016699246676267894941033500351306120030125729651145787315254731330075407854095986129899271362378048527971018629426027833460052115421683749868477352312003624406636088011276006900844776694105860926654928374623695705317686148463224726291190789124844452576348259985929516386397181007659626076947921040588085388672472178130614987864519784173212070829843470082908556509847405476906896157192138759241786116475309346346379165764954667776645629584884252459066885805169003152772837280694300556206144392490386962890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_111 : (-705254039273 / 50000000000000 : ℝ) ≤ oddTerm 111 ∧ oddTerm 111 ≤ (-688541583 / 48828125000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-4344341771682593989052899714118234725131726707989361640890021741758278291192216051115670801306258553095485009923978810745041880638275815259670221590131931320965381051188509258251530471544290674882854565191301810410202620966073240801299068603342060278914842578024596782576007129510229173562504349161833617629032749842713436493910264728956654576469324127495701286482516628920737259818711693738635512553394446765343847692649085673670608448355127546000619871501053473215817476563748288433443293114890005173258884473602018098045879039937673955453144327775474413461742245664752321917204409478245299160166771263113202452006682739148414282833469375260709391828376127769427571605340042618327969124265695727104088928996119780228576911163728304099364262075022932407644712608619998345344180514534284291963985684041445761108616231320307328690309668453564384944209053924103337039268854241829425720354535755250926959 / 148788723438726436343782656846809362962316296848391965413956151648840763153637769951364973798548606639300069467560090991374724461784945701366574406296170260273372431788376630045787374975379909394674572843078929091346367680150234052514656859604221013111102057110651610891608002287719865953569464348778997352867899773021862896865667590559777411407543183761348310006009735411385846122580200117047469295344332789225664701399336911391628329883730485317204106781152127111571732449173152179624849282107369577774349445107257555054449458047345982373657068147476568223573691644975955040048920832459979805861460719469532842380777069191868949286699456668212933197180007157087118661657341652695381259465086384262809975593717961446759285159444738275150830034477101564407348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 111) / 2 * Real.cos (169 / 2 * Real.log 111) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 111) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 111)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 111) / 2 * Real.cos (169 / 2 * Real.log 111) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 111) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 111)) / (2 * (169 / 2)) ≤ (-1930305349612384987865311810016725277481016262106789935862284366722752907485316813278215774900421900150358938481939274531168159780026588479835363914419657394867879600388101183224383633319648388417661206927888180293117442090835273904298222755184835482377529068937872576427445062971508615210749264243217373669510766074406959839723749190114128347908395230190102313995993810566231415088100132375336469076646123521965977191515077472067003313187910455232992218352538508608561633281636505449628803235574738846053969276361750944558164964844580333814999261978871017931993313990512009625144156020332200040510049769634998702160392666375811037180416594137057201065319671473460691685515245871570966406590581287787792167241167723980021063222376871378416992599910020051218251583171079653512678422943423645542774964326733450798808448845738005891536174226861673862276725006062566564003085370631 / 66128321528322860597236736376359716872140576377063095739536067399484783623839008867273321688243825173022253096693373773944321983015531422829588625020520115677054414128167391131461055544613293064299810152479524040598385635622326245562069715379653783604934247604734049285159112127875495979364206377235109934607955454676383509718074484693234405070019192782821471113782104627282598276702311163132208575708592350766962089510816405062945924392769104585424047458289834271809658866299178746499933014269942034566377531158781135579755314687709325499403141398878474766032751842211535573355075925537768802605093653097570152169234252974163977460755314074761303643191114292038719405181040734531280559762260615227915544708319093976337460070864328122289257793100934028625488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_112 : (-4710876743 / 10000000000000 : ℝ) ≤ oddTerm 112 ∧ oddTerm 112 ≤ (-47100919253 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-693634139428046261226250352090844894938579931905778261838704670037501858247825309592199910912577547098867395839666119934087561229844754248646272277593126428590354584475294884068964387578064073152194129447479822951659234243898701646325780033692333477708838847931382345202983818588166417000919862366207203288384921895518366998151522596089389347404001545768923819895593512475792881577345619636051626431700720367602891105632782119350507019367925289242250713551756575789020309033002335101031390553752209041700986159289045932205116467688650555272888299997396959828862507720164043578115090710257265550875250924799607296718365027658132089361230846076260422157977499377922699992550869283319476686009608289465364694221267465014948158373606274953532804631364393143112947012615005896073641756670868852434563608559985050232667516959389089724561015162614273997712942587636146738201976476489570754501196355316047905487368337 / 16264723081847197930777864083725461169941124704787095036270243616050623299152481341816458375394027224733985017217596153066126174301387804549707459416807184362827352936883393791513676714366337716671242465655916504271274661560983136550167816864897926196078814399846735733053535707432463344424071521885701060496569668114572196533467325160331049306419249391878838313416142326513347590285170062937575894502743979535938513112044515595420632767551763278448371606790237264482199679492877502882488949976371862373613610285796500111451962223598531223675080970862389950335389099334167358677591277605034368551024325170033883359456210585315657679648912333413297212175128307097504342475099248232485477084026044951531736610782862219219649354169460296015557406018156329984681115808486938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 112) / 2 * Real.cos (169 / 2 * Real.log 112) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 112) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 112)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 112) / 2 * Real.cos (169 / 2 * Real.log 112) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 112) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 112)) / (2 * (169 / 2)) ≤ (-308230485556359484200756557071640319291831165070450188894287232152924854234924596655938210394350168644563344232178721353157401087365934407931090857958657035422867024934244972804442674347016385165236786632002686166917817275003020503970166241247281443456473019123645845502041367328565782630912573605995618057251799662866453607692396521834638178916697104174431611960711687534595609405345132368736792905198323566013033155719912679280998711474005255185115804007541489742560082527529406741854292612790558779955872794278744149392747395875140508161033131644911884385138929856791818417095528881916555302885319205916435656195346037945992544229656576827951582534879361829900201964243430756364230146724628517125715822462979065759994882031917226621521647069127862865210196244973954694562655988545953213326016244750829085887231642293680982907627983304952768573161088783789963124769126719055363567199 / 7228765814154310191456828481655760519973833202127597793897886051578054799623325040807314833508456544326215563207820512473833855245061246466536648629692081939034379083059286129561634095273927874076107762513740668565010960693770282911185696384399078309368361955487438103579349203303317041966254009726978249109586519162032087348207700071258244136186333063057261472629396589561487817904520027972255953112330657571528228049797562486853614563356339234865942936351216561992088746441278890169995088878387494388272715682576222271756427654932680543855591542605506644593506266370741048301151678935570830467121922297792837048647204704584736746510627703739243205411168136487779707766710776992215767592900464422902994049236827652986510824075315687118025513785847257770969384803771972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_113 : (395384123427 / 100000000000000 : ℝ) ≤ oddTerm 113 ∧ oddTerm 113 ≤ (79093587807 / 20000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-63642430852626865228715354808996067085068909259429453713996300257177330007767857621902115926283492648411230740193687821152531941236926959443711236098672137616358605207461302404501218745608848964320353634257589711286556666894983886971178006087919296321496043644216013407677759126646432134756269041903619840629154847462986576955972493164032753766574188400485251617585427356483025674856658539316913257234280137987778934281738172585033911653746401809817642479934633047667713098244950306669967155775934884253987735295813285920927591629851446692728126520460228052082099122958657388855118756480379509259812835685083757078816060608569827085447122468062707118669115330386309783962950028643158073510896490187157733502680906656200900399227681395442326071592452874158092846911073226121386284152418794269115792931356300250126593665980708675746421630526849406697479921447623682976326715487647384319416647445125072111162097 / 2033090385230899741347233010465682646242640588098386879533780452006327912394060167727057296924253403091748127152199519133265771787673475568713432427100898045353419117110424223939209589295792214583905308206989563033909332695122892068770977108112240774509851799980841966631691963429057918053008940235712632562071208514321524566683415645041381163302406173984854789177017790814168448785646257867196986812842997441992314139005564449427579095943970409806046450848779658060274959936609687860311118747046482796701701285724562513931495277949816402959385121357798743791923637416770919834698909700629296068878040646254235419932026323164457209956114041676662151521891038387188042809387406029060684635503255618941467076347857777402456169271182537001944675752269541248085139476060867309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 113) / 2 * Real.cos (169 / 2 * Real.log 113) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 113) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 113)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 113) / 2 * Real.cos (169 / 2 * Real.log 113) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 113) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 113)) / (2 * (169 / 2)) ≤ (-56559059984111756463772053096618072767340073621731612609204774525355808535938627104526513768322287541804696864528371352132664711492537795742040922241366198545828975451902634826358452654766773039219593070433556723187727681067268914072794206402398808392477813963767738768510036565058605974108135940214403387698019609037711092771669094738689192195947250050039377476734909901577083134802586213428259035155730377044788285175695618980328813662228180816103311804955467741222013691690791985995879646405171115453692488635873595178094442661837831296441955099415219410248778958333039360826677294476814041946728739244997926484043054464164191009589203716274828217738969437824893562055515966009432744550814591701472361201932028906299773341457503333199332246223772569399527356143642123712152121316282696208160046905848751022258188170662900273011507135888058391187175872295572804324334892850917873796398937274874694611522421 / 1807191453538577547864207120413940129993458300531899448474471512894513699905831260201828708377114136081553890801955128118458463811265311616634162157423020484758594770764821532390408523818481968519026940628435167141252740173442570727796424096099769577342090488871859525894837300825829260491563502431744562277396629790508021837051925017814561034046583265764315368157349147390371954476130006993063988278082664392882057012449390621713403640839084808716485734087804140498022186610319722542498772219596873597068178920644055567939106913733170135963897885651376661148376566592685262075287919733892707616780480574448209262161801176146184186627656925934810801352792034121944926941677694248053941898225116105725748512309206913246627706018828921779506378446461814442742346200942993164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_114 : (-37 / 50000000000000 : ℝ) ≤ oddTerm 114 ∧ oddTerm 114 ≤ (117 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-1150802860018606958208950557090978165243469054341368826772951914941334851216118016204833378993754384255590633497168880011622637795767734260508227720854723683345563125637941980111988716374507251177665738756508347297641513096263072272087455257469250109426401720077906191296225925770864258936720947129650112132865915133323833163398453426297197617445263792730506614824212444569879643166073607412523365763567838773557083378560907795333273906491726252460477249578649604036186999690807062784131497109057829614936082649403958324481536360247039249469799988695485066692489306335101404381931146289241964896752501322864545461309028448559551482049334895593876328599518884913296690023871918169510521247160065667830049178669698621292103017750064157973250857809431639982181356389106278234016235708446990846328793647624648092438301819015465236238582227325868710472814984223374366690467341179277167656408112183780473025211717631 / 186677388586032888010756599612065471782837070636041176288277485229206234841267416717492327569319115837234735362883267651007866689729721221742681000186403897788864784653654520438948608687257995641893355747223717582073570522817663275428149570718915267442474014144932171816789207626294326728939176975348577853413619510821906820670331002262379794668505070861992799243819476070433467052972451203982510659893863591515948605244632953889383415737612231239536352980618117259048887416871067725157461981222455779934998930750848861136186312637700627291640867675797354313969913655890029296855068840013803442076233945325778560435875936433589243231125410921920634853130551124514412555987125075417178900382329371819748998839607917333605492173872739618899718836241534693619436654502018277503872800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 114) / 2 * Real.cos (169 / 2 * Real.log 114) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 114) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 114)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 114) / 2 * Real.cos (169 / 2 * Real.log 114) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 114) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 114)) / (2 * (169 / 2)) ≤ (-25548367386967712096990879027668200087570436136026356040647739544756625193340155248139065106894956011918200585473390544118644006983470710907778561469752057232072448136684824379999973909746708453430635805460708205596039245095491463667811722806470284156226996918358005698945767228633361115569225655492578775122238794849133717245016652475662654500760918098376802654261789237455325176204877823590243036783109322105924029198695287639634903387479481361649673871735145194873396029494464037409281038783017929996724714506529025912359116933626159991757328860765235443323785798917263182366724647418635530464359591649553385342127117152506080546316779311726938068025256012157889508324495507955289624200445769800224324927153903109522981934252616103708405948826237955458969753185643443075566668374067849364480620668113098424280896802552327520398136390025357419236825718362506560751579950873494778145745716327017119 / 4148386413022953066905702213601454928507490458578692806406166338426805218694831482610940612651535907494105230286294836689063704216216027149837355559697864395308106325636767120865524637494622125375407905493860390712746011618170295009514434904864783720943866980998492707039760169473207260643092821674412841186969322462709040459340688939163995437077890463599839983195988357120743712288276693421833570219863635367021080116547398975319631460835827360878585621791513716867753053708245949447943599582721239554111087350018863580804140280837791717592019281684385651421553636797556206596779307555862298712805198785017301343019465254079760960691675798264902996736234469433653612355269446120381753341829541595994422196435731496302344270530505324864438196360922993191543036766711517277863840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_115 : (0 : ℝ) ≤ oddTerm 115 ∧ oddTerm 115 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (293597490299725146585872886732471989742738985154526074052887139467003327268888907005788318423802903925323172004765610526464922216420517682900568164160929158973855281846345257624638808918213675475143455135094249082260726303243804457116443847280980596747835746563608972089272747707899347270486548905639249286263153089295028426000288171914815975509851074156209241588356501431375924428016962431751058813246675158142495511713355042068402835934759515344207927908485417453096499232020844332372272532355539023353329098712973724047953543577021878454720329860068951885231765280373646728139756780223058488324484686146477317654851497001109930072237605398298202095337817831300120674942060277222869495066749489401824541043932121768692823164340247901543097236698911848282448215916543363732438834538003023442476016589389090939665323995712215884243451685085442915387200314066070612199502264012761812448062967095693475515663461344905949 / 17829624860433520712670462631196048455779016831681047004902212574937177313339144172428355653418644360101983983239087608819400104266187616506438386821110657040092820280653287290444420028333861028387920595762000197153040114794923457710034465697726166078581847247104932283797261892208944026493632708663230878918137907733313254819258168925360522042203778408498281156993001580530906975167128974795232717682883106515069115830647172035825274152340560909549188044900372925111852431735559186990317253855865332595096528804701194852078911694219383668794183316900599879694343233777142162379970932087268291369640061188861654458591665508296386751496967411195994997477640134744839144460992046241163378394526441290197720021847880957227019823581405488844797180752359940990827547556847193693418543724145329136848449707031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 115) / 2 * Real.cos (169 / 2 * Real.log 115) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 115) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 115)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 115) / 2 * Real.cos (169 / 2 * Real.log 115) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 115) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 115)) / (2 * (169 / 2)) ≤ (660814721658913745823907004629282757295062811033772753881557142893525360532758826735760310845822705836806495000803344864531015288747368961683346742981351931520017127877310400849613581601170681881107867663356018426671996633933430239547635795689457222434621857622870191767955467539793739413730882742206642887308368796391301107987573170870858173130942487150397372588608138043460040502103076158863266720296289109559682648473912808008796424914388218025348915066601424789058776705735406008817947827420423403866783230278692680154155895055584948776335185622386616256622910945172354506724723659831627979138801976373081389424979867807769235963750482216927102804783068710607508976287956378210238909979152512388844938027409654627704671380440535842773325272338851804283439527208491290534611593850845976975814117860740608259330492404158458361205363021549810036155458619994035417529099968224527079583186008163610955132971110524279428166668469315021620142701 / 40116655935975421603508540920191109025502787871282355761029978293608648955013074387963800220191949810229463962287947119843650234598922137139486370347498978340208845631469896403499945063751187313872821340464500443594340258288577779847577547819883873676809156305986097638543839257470124059610673594492269477565810292399954823343330880082061174594958501419121132603234253556194540694126040193289273614786486989658905510618956137080606866842766262046485673101025839081501667971405008170728213821175696998338967189810577688417177551311993613254786912463026349729312272275998569865354934597196353655581690137674938722531831247393666870190868176675190988744324690303175888075037232104042617601387684492902944870049157732153760794603058162349900793656692809867229361982002906185810191723379326990557909011840820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_116 : (-277 / 100000000000000 : ℝ) ≤ oddTerm 116 ∧ oddTerm 116 ≤ (457 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (3580101677973617392345649449415589689466740772965040078126573965759341993432888458638015780971826386298596583180966036972879991066473783017515327579187087125571005657686967743376276541018401949345684139413750317473739676128976966319870931914805529300851042798109918459917527676447776147541411017121964007938902013345655812461900970613913603896791167774205648521242353892215922420591147695790443084971386044852535920532669801910710515167121395219562558807759570267095448213844378460406273799477266959801708193462328178185750331911972205709827154816883142276296329409363619018382738756822536703151101183212791197134665378750077259823174926693119196287811189284409562117087474465071590189606838718558043361160742523869015714775550848487742352146114262174924303913835385645175965887271366280587011125059302757543675735523938923612949291924488308795498441383587493509762575241372676366970883846858576064507110598554423 / 142636998883468165701363701049568387646232134653448376039217700599497418506713153379426845227349154880815871865912700870555200834129500932051507094568885256320742562245226298323555360226670888227103364766096001577224320918359387661680275725581809328628654777976839458270378095137671552211949061669305847031345103261866506038554065351402884176337630227267986249255944012644247255801337031798361861741463064852120552926645177376286602193218724487276393504359202983400894819453884473495922538030846922660760772230437609558816631293553755069350353466535204799037554745870217137299039767456698146330957120489510893235668733324066371094011975739289567959979821121077958713155687936369929307027156211530321581760174783047657816158588651243910758377446018879527926620380454777549547348349793162633094787597656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 116) / 2 * Real.cos (169 / 2 * Real.log 116) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 116) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 116)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 116) / 2 * Real.cos (169 / 2 * Real.log 116) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 116) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 116)) / (2 * (169 / 2)) ≤ (8056826525230186461908736822620932793109397805479067126370935983022955215303995789849225540220080256881371286426297066397283798173683942918096648435982384862789030988108823720136754387069308278144511336450181371377210306745372854321732975518781838890484068765931192948819663120902792787924390620699615029780172465188054915235881404158071019630838090802385270369734423476776579618435111972276302473158870094575173956305092549930226496629605219437027039768272022254054306775877593040335011464849866578887121088234839388117921784332977109254081992463392578586494134561993646609176627075225983980727177836984592233094336588805107840970725845479681794593981525832616002508603333874843779088957858805834689020213944176651491838707125912147239340604585911255002785360186712810448648598072652153119373657786784516082831817552620141476763123171801340959547394620421702282662079528818460889779842560058004065817970204699913874196168460848005528361 / 320933247487803372828068327361528872204022302970258846088239826348869191640104595103710401761535598481835711698303576958749201876791377097115890962779991826721670765051759171227999560510009498510982570723716003548754722066308622238780620382559070989414473250447888781108350714059760992476885388755938155820526482339199638586746647040656489396759668011352969060825874028449556325553008321546314188918291895917271244084951649096644854934742130096371885384808206712652013343771240065365825710569405575986711737518484621507337420410495948906038295299704210797834498178207988558922839476777570829244653521101399509780254649979149334961526945413401527909954597522425407104600297856832340940811101475943223558960393261857230086356824465298799206349253542478937834895856023249486481533787034615924463272094726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_117 : (-62522790419 / 25000000000000 : ℝ) ≤ oddTerm 117 ∧ oddTerm 117 ≤ (-12501607039 / 5000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (115957567949259608234548793713254098019993170829137665932036151205460623543083099350196021061429817734575732622680084826903337808098308769415249592910860343432386372410738943139720195046418617947288051135233043712135305590490299893880242577010358887545909361559037784448468591389662265944921179417268373322663963661352810817148108191586614078983603203029088269266973853093984796794814691993336211298579574489095440248551297702024926544116599203914721069812931403372829455805996354811140232724353489205209884084947429060040198392971329239592855668257626173636857850555535100158892455302570610249494293555100150912518189669327729385454702871832542864587193558619447395319673402760985857149092382055725654337480654835110591050806113063842191779784326404916357451583503515607161700695175533550731396568063647468248237030317827770488530587895537363170289552940563210981267585724494492967093868648879345305654498369145417400786910046200388156418058845907 / 6268451835325840604046670406561900755993479095849650032669759375250270892412239663032815478896496591552810327180098867800720314242177117971465721258566374683215886309505288915735720882251647331661499060555038973200902834343990218746571717748825982756813535404403343122487016894482684499787080541558434296730622596049251706578322879689733239699684332885220381597984899497970207263732922973067699154101031504713532878042239036655173404470906357561072983514930213746525643087248417048883133451964944506887887590813065891751460818095845571074273910951383885562823416116529411119097764552330680504774161746459253406444675027760241142277335020176979249573388307673311862206382212453708604349020103712215848706661465038290361355421163829365428937615223583138998125390330325735974391320966718482917649864697142048971727490425109863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 117) / 2 * Real.cos (169 / 2 * Real.log 117) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 117) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 117)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 117) / 2 * Real.cos (169 / 2 * Real.log 117) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 117) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 117)) / (2 * (169 / 2)) ≤ (260966115042203026537448159775120440449468492377786144301661073883832276732654857095196415888343509058634582362822405373317763952705603445981733567464208661868830455398599452891104785878031447683220613181596633961915281161367602983945326948475305698444501925933154191033519145238826065926974492409787164968126614827081360582725752466269823883035457940935167828996344274979314081170477063726889464328074025563136912778146745023333813490739227329277278217202196879175492974478683818599365493511085245358377143872094672580277126583695142694004883641360302452423000342945009923551827896675437568983301227864162895774565894551749009343704487373422583080576061975556426855794076453247216177925738334891363612497626391016611237579846707615618385591718139880011776773780364917675811731127065687482548743231175247135734341522065046133535422430844441816238303227727935165053460665200302821386267880201315212564714639594676433572161673002538050913473146195913 / 14104016629483141359105008414764276700985327965661712573506958594313109507927539241823834827517117330993823236155222452551620707044898515435797872831774343037235744196386900060405371985066206496238372886248837689702031377273977992179786364934858461202830454659907522025595788012586040124520931218506477167643900841110816339801226479301899789324289748991745858595466023870432966343399076689402323096727320885605448975595037832474140160059539304512414212908592980929682696946308938359987050266921125140497747079329398256440786840715652534917116299640613742516352686262191175017969970242744031135741863929533320164500518812460542570124003795398203311540123692264951689964359978020844359785295233352485659589988296336153313049697618616072215109634253062062745782128243232905942380472175116586564712195568569610186386853456497192382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_118 : (-11 / 50000000000000 : ℝ) ≤ oddTerm 118 ∧ oddTerm 118 ≤ (7 / 50000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (900474725796506088195740529250806664581131903592928992661705166822259361476721995447640713198775018998467056687787061787510170769466861911524548929836190998911541924482045128487907016169845111544086247789366100550914075132668825576503460483912967734367307327412455451889756748259100488604880253094046396679489464752489722749656197155458409318618827113721537938805300866796976078475903842442251869071603088655757427584668409011489631578069082420773397145933464206797979574976256503192755537314122186678582623661386902704453406153596873741598083170816519183621970060401526566936699529087647638907625433685783438266718815010101019632931644905413423422295852483627798831029668155521088610997904775357479298643938675704480537635602560103446517302506884742812910441530791732163389458601321950123573845247508869438753280167883985966327811897319838201698905751794003222149387577318728642490457009496720765954000805904788301701073536105537540319 / 210334340853716116391322926983393652707731786765108564245015219413197697641025811740937520755179929919490548532262379212896259335257763636929524484301519836794488998492026170563407976314492907278217217245457937483619516493602684403596965936326174518246672310406644477376158279268770412225559608510245657636115498216798085039266287740593335089642758369262491099343635647231475457656832430061037942662740582754767918436032602883191523448527523353150709272388846841903259927227347076974389777360882996840143155789580844176293752921461419697112890894392265894013540044089790201395809842023190260511170285678568259197316209981079123712147163075747078195221286979419221095197421913787518512444099336644494264749960075647691326355907273073301888438042261885233859146537312372445602667320767929598203443984789453476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 118) / 2 * Real.cos (169 / 2 * Real.log 118) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 118) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 118)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 118) / 2 * Real.cos (169 / 2 * Real.log 118) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 118) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 118)) / (2 * (169 / 2)) ≤ (202793185956278067966130400136923398153126256012948561789208672752206702388044081919468147128545728652264835510524033723031508992052281154398800551303655713692471332517288149721784973488248313624841558807665059141039400407030524187848946159696168183171962432298543305388080550289332473055297802751023502068507848607973971955414378708205953557321762462205819056987143617918427350893623022708919663828881915761193875716944449007353175794729412459930398031458129050203523835281547780893485108806069047825243701207716298889440981650267230368736038373784722389302684174864225371770451116385986723939804345193324267787473905409450463194136768745993307700463452176896364739911389495258251693790701513797121112098087203511419947376566408797544911019427929560533426158925090824990305801193746157225166295329850796228808116432276777190051205530247672810697359772262573470187933982902869962050267611314866015008505791178488373637424166418012343855414683200577 / 47325226692086126188047658571263571859239652022149426955128424367969481969230807641710942169915484231885373419759035322901658350432996818309143008967841963278760024660705888376766794670760904137598873880228035933814391211060603990809317335673389266605501269841495007409635612835473342750750911914805272968125987098779569133834914741633500395169620633084060497352318020627081977972787296763733537099116631119822781648107335648718092775918692754458909586287490539428233483626153092319237699906198674289032210052655689939666094407328819431850400451238259826153046509920202795314057214455217808615013314277677858319396147245742802835233111692043092593924789570369324746419419930602191665299922350745011209568741017020730548430079136441492924898559508924177618307970895283800260600147172784159595774896577627032226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_119 : (344459262949 / 100000000000000 : ℝ) ≤ oddTerm 119 ∧ oddTerm 119 ≤ (344609987953 / 100000000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-420484830948730815234974090754359289035042997505413799750600600411053244620446969910408945794290443284210527872365915325843693294395074706189871423517459378678209193996787331126522198246287353083264092347463217710575550447929937535307938997103033560563056547366384993474922623574379414527319505187106621564773968654054050298975202796078969897279323308324709434536355589311729467860587671485055955499929661520915897976157494468927082496271974768114419913364668332620443550474347345495042635492854220877746021512323978359682040417094877260540209399364609193560618655804984256748099946292116266817507373361488145199896303878762323105359242971069680538715623074856742228026783584209308739333599792339596984526699455062961570064187602745411644519458689691637745139944617086880883110063112973173222647644989991944843420143099964949721237181203389356715537871190069507311713237129379493189444750818808360085229422816067746794000123259752081821843692089405439779239 / 57770052114362947006894114466874477367235903347350374701084502402306496544471200734510427453510112587750699975291791165651438416055904319225028087118947709080517608228400742647420403650831181808592375342075239177019520521314213855968404950773180257086793542286981210216840347699552420350037734271002530478669417845189903727825823659220581537072290811870191036807028833773293430142562618119791915404195106347439919004037274961814078095603872991282848616073596849887980326692081411522506957893308928575478772036933215258381462899571312783020508363327953889346980602929935052873604998114279551531998674655368479393794125055838382367227919545951040764068346643517242122094018469973378497680569275811781261680592061792883970251561445851431793089061900542209006723597284281982739990414029277538569061153048861123323440551757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 119) / 2 * Real.cos (169 / 2 * Real.log 119) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 119) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 119)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 119) / 2 * Real.cos (169 / 2 * Real.log 119) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 119) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 119)) / (2 * (169 / 2)) ≤ (-186800408931001307503160604112537362507134118443570156577134048202693283124051678565201783487123807695355677759786776647223854581412663741544486356290989027626807080262363955318634693734705863700865776733350863892797847404617523816661159371185708525410563424448290915518425960000556320109921187519163299217708586066688234008973006617502547427078579854626260572955217266824270282149161446365957245427179189479760716904155383863563531141686890599377817593688327599880572717830097134304523111797543145079789321295288113728110084113527083373268601405026711646891534328439756518433648828928328557113584801310927711446724589388779927627189002772529409626287582638146050272687713755492733916432986935448731068562248440205116029794029558430884981156152392053430702142803121101984051486837995600734265591182610634940179723248557001642597862943106349763858634638274289164113580477299023392145567465990281226314092168082464240362960530536803951 / 25675578717494643114175161985277545496549290376600166533815334401025109575320533659782412201560050039000311100129684962511750407135957475211123594275087870702452270323733663398853512733702747470485500152033439634230898009472983935985957755899191225371908241016436093429706821199801075711127881898223346879408630153417734990144810515209147349809907027497862683025346148343685968952250052497685295735197825043306630668461011094139590264712832440570154940477154155505769034085369516232225314619248412700212787571970317892613983510920583459120225939256868395265324712413304467943824443606346467347554966513497101952797388913705947718767964242644907006252598508229885387597341542210390443413586344805236116302485360796837320111805087045080796928471955796537336321598793014214551106850679678906030693845799493832588195800781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_120 : (0 : ℝ) ≤ oddTerm 120 ∧ oddTerm 120 ≤ (0 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-51765762379890078743602833136133267851846932801437633414072584088929650904361808768291174533512072223832697023861579532987166457896650736229560943778694722893160895148029621013298272253162328608932383567718679448772362531068153764888535147203366811810690300373983921635040774740447416592528655511223507074342090672188467365984049361806092879407756274531284436555564961779876295543882409903146292294367712447086223789237133865611336381186331770813956811727290052083041889932734130050861837082095681564822096428946707137579147693003485579167236572206196391331370260021423142555936304589175677632980046710700647101397527532325921145742500209717754507526677398324491427690685475993031194080846963972775165395625624507177790117054365525217852920172802139661638466099862184909713788485974459567756663635805553434753673115472586304882490965728177364171973924668520693289884828272833331100771287647764197730379414147984922270137431136200429051030140706110841 / 5257269162963542384831258402882708799529786504380858882587823786193946371046371512965892877791418892330155963135696181754122980742114338546221164892971894760664376499618357648973627107890558721130076352675607158559974411060295456848389646028196168595616207715534365425313835520269136253596366407330850102606308650903511810076967792636257623556702680497466707902417078597322887306774687736368339378152204219422321025512283954631790466706197770441587454927355432794503823230154800823908274765662003615484729986054581305768947756431289596951449057414771907564027748173648327872954738738568484745205853050132022725612805846135569706363962520288278510307329927757245732877794516434425517710851562856013285008386198858640164099469463791666038461284109516998806056086785903678677433484909538749448383325865915803883755016651377663947641849517822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 120) / 2 * Real.cos (169 / 2 * Real.log 120) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 120) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 120)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 120) / 2 * Real.cos (169 / 2 * Real.log 120) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 120) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 120)) / (2 * (169 / 2)) ≤ (-9200117595497389679579543734659602205752862812738267449084722307382713653198619596441943775155454060970895275907664738516506728923052839228786323077324622027524323219561916767039549758687020044650407496128380753505361246165398014424097783176198918037124817963264558196046639268224285674872976513908947502497465958072063394456610543926001686403446183970141940790676655055837316313070587858179151996355135958650838239912426544280528547800243825028986616718253261723666665630458564701777237301971924111718951011698591300473186357470904254592678325025106951363638365400378645984177458845296960621325100236560655525349753507959672388165598893313418844982760005478902411835854968383043722547262246680872260401655519039543980590926732809896559432598304206202300281558321963766216395035219084714800751473987797074701480400936726798875732689765467694026448616109956329204730528488919285644603128545911970513439707327708711466263739860463 / 934625628971296423970001493845814897694184267445486023571168673101146021519354935638380956051807803080916615668568210089621863243042549074883762647639447957451444711043263582039755930291654883756458018253441272632884339744052525661935937071679318861442881371650553853389126314714513111750465139081040018241121537938402099569238718690890244187858254310660748071540813972857402187871055597576593667227058527897301515646628258601207194081101825856282214209307632496800679685360853479805915513895467309419507553076370009914479601143340372791368721318181672455827155230870813844080842442412175065814373875579026262331165483757434614464704448051249512943525320490177019178274580699453425370818055618846806223713102019313806951016793562962851282006063914133121076637650827320653765952872806888790823702376162809579334225182467140257358551025390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddTerm_bounds_121 : (-90812684651 / 100000000000000 : ℝ) ≤ oddTerm 121 ∧ oddTerm 121 ≤ (-11346032649 / 12500000000000 : ℝ) := by
  unfold oddTerm
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
  have hbr : (-70305839027383854144926842074248956366503737489500306753320591999745988458091335789745943596976732405258438820534395051843711959347822027171622866082883254231349087087549751065184725226502199252926844142333746098248779898939246032782932545794712889008641196741055980631353165498871835077409082870008839150737148032981128439023002791551884948761965072038686891970466050671599272527362090034967631002232746777608959264422752622882901921931259535377497802015010612713786990090711369144155846006128277659018152330001383964164104442660823608874580122955829801843237512596496273950657205521199059747007330759915245200273677817263117217923673681021796677817917070601285887503141228705218431765001015402363393909296992320321985700255827422602582702051716605982548932469144921738342949482950409041374672034413440069972930413537293868717928433428126846567210879565638074859558906408331654972099212484570991382674969199702916733734644902601857990459666351373315372023910897367444696508569687 / 16876500921253103929503672182973128717018104479890423186706678879662319058470399610575936102454305385937817716149604662133326904301230876416279524234901622111620046325279181536441791355418583980795608465489340574872386793176516149163242009874282161265870574886044436259632514199186644302848559551107703468477991680278984165465344352247726978650981890440745158717884460390049422509419116054704644034070112544662428537066499961638221382793376397923319517637179766024498635109509683475201754119887430644608503184375815300093868775258381050836438110211802178895788289886864863221815131346254955850698922888668175802614867241793402833536616865089135127350440593277953904961997793696465977320799415133650641828672816884616176147923128030880685239008327766413333956554008645827105313489294795848485554464933916952267919979243790827395266499338150024414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (2 * (12 / 5) - Real.log 121) / 2 * Real.cos (169 / 2 * Real.log 121) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 121) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 121)) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log 121) / 2 * Real.cos (169 / 2 * Real.log 121) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log 121) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log 121)) / (2 * (169 / 2)) ≤ (-31231754274019030068853656690432417141379296419657139516901544623091499894112588338159297999368811485259976999998519458099181039855580073779762882548327697822617004907430884859912253902518666538651982023958127404014736933963432821864406634316069323646365497447188176546259373515895476398850853877164096557998243406741904723436529424160902152842246444405306030567814525382249861755984928213438974257139415623399370870736627768796320522943407748802500297719507239665637052384158201165517655339923460358183099371932625695450046020509675847788310624585986449497875527472000414540250942719135387505993846403062012655178609065116172909676282826457337218095728487112463436938955669165560289061545810769434185735030718871723985610819099848820512258732697665333023960143014866399540316047176590972602266993255143380837230682268692474027199879393532487439907692715233308608710531498462866591201057341442038000946359008839319259836185728051175594198630974440346799641 / 7500667076112490635334965414654723874230268657729076971869635057627697359320177604700416045535246838194585651622046516503700846356102611740568677437734054271831131700124080682863018380186037324798048206884151366609949685856229399628107559944125405007053588838241971670947784088527397467932693133825645985990218524568437406873486378776767546067103062418108959430170871284466410004186273802090952904031161130961079349807333316283653947908167287965919785616524340455332726715337637100089668497727746953159334748611473466708386122337058244816194715649689857287017017727495494765251169487224424822532854617185855912273274329685956814905163051150726723266862485901312846649776797198429323253688628948289174146076807504273856065743612458169193439559256785072592869579559398145380139328575464821549135317748407534341297768552795923286785110816955566406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]
  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr
  norm_num at p4
  constructor <;> linarith [p4.1, p4.2]

theorem oddPartial_2 : (-12556182038667 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 2, oddTerm n := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  exact oddTerm_bounds_2.1

theorem oddPartial_3 : (-17834777160219 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 3, oddTerm n := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_2
  have h2 := oddTerm_bounds_3
  linarith [h1, h2.1]

theorem oddPartial_4 : (29079221457003 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 4, oddTerm n := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_3
  have h2 := oddTerm_bounds_4
  linarith [h1, h2.1]

theorem oddPartial_5 : (29079221457003 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 5, oddTerm n := by
  rw [show (5 : ℕ) = 4 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_4
  have h2 := oddTerm_bounds_5
  linarith [h1, h2.1]

theorem oddPartial_6 : (155675972790953 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 6, oddTerm n := by
  rw [show (6 : ℕ) = 5 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_5
  have h2 := oddTerm_bounds_6
  linarith [h1, h2.1]

theorem oddPartial_7 : (10624804312761 / 6250000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 7, oddTerm n := by
  rw [show (7 : ℕ) = 6 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_6
  have h2 := oddTerm_bounds_7
  linarith [h1, h2.1]

theorem oddPartial_8 : (85372500687949 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 8, oddTerm n := by
  rw [show (8 : ℕ) = 7 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_7
  have h2 := oddTerm_bounds_8
  linarith [h1, h2.1]

theorem oddPartial_9 : (26514038108093 / 10000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 9, oddTerm n := by
  rw [show (9 : ℕ) = 8 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_8
  have h2 := oddTerm_bounds_9
  linarith [h1, h2.1]

theorem oddPartial_10 : (26514038108093 / 10000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 10, oddTerm n := by
  rw [show (10 : ℕ) = 9 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_9
  have h2 := oddTerm_bounds_10
  linarith [h1, h2.1]

theorem oddPartial_11 : (13282620567847 / 5000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 11, oddTerm n := by
  rw [show (11 : ℕ) = 10 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_10
  have h2 := oddTerm_bounds_11
  linarith [h1, h2.1]

theorem oddPartial_12 : (57594214456387 / 20000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 12, oddTerm n := by
  rw [show (12 : ℕ) = 11 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_11
  have h2 := oddTerm_bounds_12
  linarith [h1, h2.1]

theorem oddPartial_13 : (155292961850247 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 13, oddTerm n := by
  rw [show (13 : ℕ) = 12 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_12
  have h2 := oddTerm_bounds_13
  linarith [h1, h2.1]

theorem oddPartial_14 : (392996420742107 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 14, oddTerm n := by
  rw [show (14 : ℕ) = 13 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_13
  have h2 := oddTerm_bounds_14
  linarith [h1, h2.1]

theorem oddPartial_15 : (392996420742107 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 15, oddTerm n := by
  rw [show (15 : ℕ) = 14 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_14
  have h2 := oddTerm_bounds_15
  linarith [h1, h2.1]

theorem oddPartial_16 : (192317195774061 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 16, oddTerm n := by
  rw [show (16 : ℕ) = 15 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_15
  have h2 := oddTerm_bounds_16
  linarith [h1, h2.1]

theorem oddPartial_17 : (99983110179723 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 17, oddTerm n := by
  rw [show (17 : ℕ) = 16 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_16
  have h2 := oddTerm_bounds_17
  linarith [h1, h2.1]

theorem oddPartial_18 : (1616583451429 / 390625000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 18, oddTerm n := by
  rw [show (18 : ℕ) = 17 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_17
  have h2 := oddTerm_bounds_18
  linarith [h1, h2.1]

theorem oddPartial_19 : (11619090506103 / 2500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 19, oddTerm n := by
  rw [show (19 : ℕ) = 18 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_18
  have h2 := oddTerm_bounds_19
  linarith [h1, h2.1]

theorem oddPartial_20 : (11619090506103 / 2500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 20, oddTerm n := by
  rw [show (20 : ℕ) = 19 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_19
  have h2 := oddTerm_bounds_20
  linarith [h1, h2.1]

theorem oddPartial_21 : (26213114988271 / 5000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 21, oddTerm n := by
  rw [show (21 : ℕ) = 20 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_20
  have h2 := oddTerm_bounds_21
  linarith [h1, h2.1]

theorem oddPartial_22 : (524262299762057 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 22, oddTerm n := by
  rw [show (22 : ℕ) = 21 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_21
  have h2 := oddTerm_bounds_22
  linarith [h1, h2.1]

theorem oddPartial_23 : (516716759087763 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 23, oddTerm n := by
  rw [show (23 : ℕ) = 22 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_22
  have h2 := oddTerm_bounds_23
  linarith [h1, h2.1]

theorem oddPartial_24 : (2582347663857 / 500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 24, oddTerm n := by
  rw [show (24 : ℕ) = 23 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_23
  have h2 := oddTerm_bounds_24
  linarith [h1, h2.1]

theorem oddPartial_25 : (2582347663857 / 500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 25, oddTerm n := by
  rw [show (25 : ℕ) = 24 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_24
  have h2 := oddTerm_bounds_25
  linarith [h1, h2.1]

theorem oddPartial_26 : (538572965468769 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 26, oddTerm n := by
  rw [show (26 : ℕ) = 25 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_25
  have h2 := oddTerm_bounds_26
  linarith [h1, h2.1]

theorem oddPartial_27 : (67342500241847 / 12500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 27, oddTerm n := by
  rw [show (27 : ℕ) = 26 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_26
  have h2 := oddTerm_bounds_27
  linarith [h1, h2.1]

theorem oddPartial_28 : (544362408263129 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 28, oddTerm n := by
  rw [show (28 : ℕ) = 27 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_27
  have h2 := oddTerm_bounds_28
  linarith [h1, h2.1]

theorem oddPartial_29 : (554606944763117 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 29, oddTerm n := by
  rw [show (29 : ℕ) = 28 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_28
  have h2 := oddTerm_bounds_29
  linarith [h1, h2.1]

theorem oddPartial_30 : (554606944763117 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 30, oddTerm n := by
  rw [show (30 : ℕ) = 29 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_29
  have h2 := oddTerm_bounds_30
  linarith [h1, h2.1]

theorem oddPartial_31 : (142931088813583 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 31, oddTerm n := by
  rw [show (31 : ℕ) = 30 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_30
  have h2 := oddTerm_bounds_31
  linarith [h1, h2.1]

theorem oddPartial_32 : (285856351914263 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 32, oddTerm n := by
  rw [show (32 : ℕ) = 31 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_31
  have h2 := oddTerm_bounds_32
  linarith [h1, h2.1]

theorem oddPartial_33 : (571712703826157 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 33, oddTerm n := by
  rw [show (33 : ℕ) = 32 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_32
  have h2 := oddTerm_bounds_33
  linarith [h1, h2.1]

theorem oddPartial_34 : (152256422607793 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 34, oddTerm n := by
  rw [show (34 : ℕ) = 33 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_33
  have h2 := oddTerm_bounds_34
  linarith [h1, h2.1]

theorem oddPartial_35 : (152256422607793 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 35, oddTerm n := by
  rw [show (35 : ℕ) = 34 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_34
  have h2 := oddTerm_bounds_35
  linarith [h1, h2.1]

theorem oddPartial_36 : (150175517738473 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 36, oddTerm n := by
  rw [show (36 : ℕ) = 35 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_35
  have h2 := oddTerm_bounds_36
  linarith [h1, h2.1]

theorem oddPartial_37 : (591426293051589 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 37, oddTerm n := by
  rw [show (37 : ℕ) = 36 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_36
  have h2 := oddTerm_bounds_37
  linarith [h1, h2.1]

theorem oddPartial_38 : (29571314652489 / 5000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 38, oddTerm n := by
  rw [show (38 : ℕ) = 37 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_37
  have h2 := oddTerm_bounds_38
  linarith [h1, h2.1]

theorem oddPartial_39 : (298125184242577 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 39, oddTerm n := by
  rw [show (39 : ℕ) = 38 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_38
  have h2 := oddTerm_bounds_39
  linarith [h1, h2.1]

theorem oddPartial_40 : (298125184242577 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 40, oddTerm n := by
  rw [show (40 : ℕ) = 39 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_39
  have h2 := oddTerm_bounds_40
  linarith [h1, h2.1]

theorem oddPartial_41 : (625927026010947 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 41, oddTerm n := by
  rw [show (41 : ℕ) = 40 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_40
  have h2 := oddTerm_bounds_41
  linarith [h1, h2.1]

theorem oddPartial_42 : (628064651810773 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 42, oddTerm n := by
  rw [show (42 : ℕ) = 41 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_41
  have h2 := oddTerm_bounds_42
  linarith [h1, h2.1]

theorem oddPartial_43 : (635388496880943 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 43, oddTerm n := by
  rw [show (43 : ℕ) = 42 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_42
  have h2 := oddTerm_bounds_43
  linarith [h1, h2.1]

theorem oddPartial_44 : (635388496876097 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 44, oddTerm n := by
  rw [show (44 : ℕ) = 43 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_43
  have h2 := oddTerm_bounds_44
  linarith [h1, h2.1]

theorem oddPartial_45 : (635388496876097 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 45, oddTerm n := by
  rw [show (45 : ℕ) = 44 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_44
  have h2 := oddTerm_bounds_45
  linarith [h1, h2.1]

theorem oddPartial_46 : (121135587692621 / 20000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 46, oddTerm n := by
  rw [show (46 : ℕ) = 45 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_45
  have h2 := oddTerm_bounds_46
  linarith [h1, h2.1]

theorem oddPartial_47 : (75893385349449 / 12500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 47, oddTerm n := by
  rw [show (47 : ℕ) = 46 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_46
  have h2 := oddTerm_bounds_47
  linarith [h1, h2.1]

theorem oddPartial_48 : (303276550551761 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 48, oddTerm n := by
  rw [show (48 : ℕ) = 47 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_47
  have h2 := oddTerm_bounds_48
  linarith [h1, h2.1]

theorem oddPartial_49 : (310444996977527 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 49, oddTerm n := by
  rw [show (49 : ℕ) = 48 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_48
  have h2 := oddTerm_bounds_49
  linarith [h1, h2.1]

theorem oddPartial_50 : (310444996977527 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 50, oddTerm n := by
  rw [show (50 : ℕ) = 49 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_49
  have h2 := oddTerm_bounds_50
  linarith [h1, h2.1]

theorem oddPartial_51 : (639753507824517 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 51, oddTerm n := by
  rw [show (51 : ℕ) = 50 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_50
  have h2 := oddTerm_bounds_51
  linarith [h1, h2.1]

theorem oddPartial_52 : (635207709460217 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 52, oddTerm n := by
  rw [show (52 : ℕ) = 51 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_51
  have h2 := oddTerm_bounds_52
  linarith [h1, h2.1]

theorem oddPartial_53 : (640358778696537 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 53, oddTerm n := by
  rw [show (53 : ℕ) = 52 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_52
  have h2 := oddTerm_bounds_53
  linarith [h1, h2.1]

theorem oddPartial_54 : (639209184646381 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 54, oddTerm n := by
  rw [show (54 : ℕ) = 53 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_53
  have h2 := oddTerm_bounds_54
  linarith [h1, h2.1]

theorem oddPartial_55 : (639209184646381 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 55, oddTerm n := by
  rw [show (55 : ℕ) = 54 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_54
  have h2 := oddTerm_bounds_55
  linarith [h1, h2.1]

theorem oddPartial_56 : (39876490912343 / 6250000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 56, oddTerm n := by
  rw [show (56 : ℕ) = 55 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_55
  have h2 := oddTerm_bounds_56
  linarith [h1, h2.1]

theorem oddPartial_57 : (638023854596707 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 57, oddTerm n := by
  rw [show (57 : ℕ) = 56 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_56
  have h2 := oddTerm_bounds_57
  linarith [h1, h2.1]

theorem oddPartial_58 : (159505963648967 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 58, oddTerm n := by
  rw [show (58 : ℕ) = 57 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_57
  have h2 := oddTerm_bounds_58
  linarith [h1, h2.1]

theorem oddPartial_59 : (62773302697103 / 10000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 59, oddTerm n := by
  rw [show (59 : ℕ) = 58 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_58
  have h2 := oddTerm_bounds_59
  linarith [h1, h2.1]

theorem oddPartial_60 : (62773302697103 / 10000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 60, oddTerm n := by
  rw [show (60 : ℕ) = 59 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_59
  have h2 := oddTerm_bounds_60
  linarith [h1, h2.1]

theorem oddPartial_61 : (623413908452289 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 61, oddTerm n := by
  rw [show (61 : ℕ) = 60 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_60
  have h2 := oddTerm_bounds_61
  linarith [h1, h2.1]

theorem oddPartial_62 : (77926738556367 / 12500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 62, oddTerm n := by
  rw [show (62 : ℕ) = 61 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_61
  have h2 := oddTerm_bounds_62
  linarith [h1, h2.1]

theorem oddPartial_63 : (38905481275327 / 6250000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 63, oddTerm n := by
  rw [show (63 : ℕ) = 62 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_62
  have h2 := oddTerm_bounds_63
  linarith [h1, h2.1]

theorem oddPartial_64 : (1543430086041 / 250000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 64, oddTerm n := by
  rw [show (64 : ℕ) = 63 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_63
  have h2 := oddTerm_bounds_64
  linarith [h1, h2.1]

theorem oddPartial_65 : (1543430086041 / 250000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 65, oddTerm n := by
  rw [show (65 : ℕ) = 64 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_64
  have h2 := oddTerm_bounds_65
  linarith [h1, h2.1]

theorem oddPartial_66 : (308686017206679 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 66, oddTerm n := by
  rw [show (66 : ℕ) = 65 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_65
  have h2 := oddTerm_bounds_66
  linarith [h1, h2.1]

theorem oddPartial_67 : (153303636527303 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 67, oddTerm n := by
  rw [show (67 : ℕ) = 66 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_66
  have h2 := oddTerm_bounds_67
  linarith [h1, h2.1]

theorem oddPartial_68 : (306599740148979 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 68, oddTerm n := by
  rw [show (68 : ℕ) = 67 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_67
  have h2 := oddTerm_bounds_68
  linarith [h1, h2.1]

theorem oddPartial_69 : (598400206823589 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 69, oddTerm n := by
  rw [show (69 : ℕ) = 68 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_68
  have h2 := oddTerm_bounds_69
  linarith [h1, h2.1]

theorem oddPartial_70 : (598400206823589 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 70, oddTerm n := by
  rw [show (70 : ℕ) = 69 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_69
  have h2 := oddTerm_bounds_70
  linarith [h1, h2.1]

theorem oddPartial_71 : (591777786901867 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 71, oddTerm n := by
  rw [show (71 : ℕ) = 70 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_70
  have h2 := oddTerm_bounds_71
  linarith [h1, h2.1]

theorem oddPartial_72 : (587071200792033 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 72, oddTerm n := by
  rw [show (72 : ℕ) = 71 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_71
  have h2 := oddTerm_bounds_72
  linarith [h1, h2.1]

theorem oddPartial_73 : (588112592035083 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 73, oddTerm n := by
  rw [show (73 : ℕ) = 72 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_72
  have h2 := oddTerm_bounds_73
  linarith [h1, h2.1]

theorem oddPartial_74 : (577851468810771 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 74, oddTerm n := by
  rw [show (74 : ℕ) = 73 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_73
  have h2 := oddTerm_bounds_74
  linarith [h1, h2.1]

theorem oddPartial_75 : (577851468810771 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 75, oddTerm n := by
  rw [show (75 : ℕ) = 74 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_74
  have h2 := oddTerm_bounds_75
  linarith [h1, h2.1]

theorem oddPartial_76 : (288925734405349 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 76, oddTerm n := by
  rw [show (76 : ℕ) = 75 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_75
  have h2 := oddTerm_bounds_76
  linarith [h1, h2.1]

theorem oddPartial_77 : (577851468809659 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 77, oddTerm n := by
  rw [show (77 : ℕ) = 76 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_76
  have h2 := oddTerm_bounds_77
  linarith [h1, h2.1]

theorem oddPartial_78 : (57226204743803 / 10000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 78, oddTerm n := by
  rw [show (78 : ℕ) = 77 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_77
  have h2 := oddTerm_bounds_78
  linarith [h1, h2.1]

theorem oddPartial_79 : (11422422368471 / 2000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 79, oddTerm n := by
  rw [show (79 : ℕ) = 78 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_78
  have h2 := oddTerm_bounds_79
  linarith [h1, h2.1]

theorem oddPartial_80 : (11422422368471 / 2000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 80, oddTerm n := by
  rw [show (80 : ℕ) = 79 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_79
  have h2 := oddTerm_bounds_80
  linarith [h1, h2.1]

theorem oddPartial_81 : (57508707518847 / 10000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 81, oddTerm n := by
  rw [show (81 : ℕ) = 80 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_80
  have h2 := oddTerm_bounds_81
  linarith [h1, h2.1]

theorem oddPartial_82 : (575087075188347 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 82, oddTerm n := by
  rw [show (82 : ℕ) = 81 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_81
  have h2 := oddTerm_bounds_82
  linarith [h1, h2.1]

theorem oddPartial_83 : (23100034192271 / 4000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 83, oddTerm n := by
  rw [show (83 : ℕ) = 82 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_82
  have h2 := oddTerm_bounds_83
  linarith [h1, h2.1]

theorem oddPartial_84 : (567399851747419 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 84, oddTerm n := by
  rw [show (84 : ℕ) = 83 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_83
  have h2 := oddTerm_bounds_84
  linarith [h1, h2.1]

theorem oddPartial_85 : (567399851747419 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 85, oddTerm n := by
  rw [show (85 : ℕ) = 84 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_84
  have h2 := oddTerm_bounds_85
  linarith [h1, h2.1]

theorem oddPartial_86 : (287528321781549 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 86, oddTerm n := by
  rw [show (86 : ℕ) = 85 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_85
  have h2 := oddTerm_bounds_86
  linarith [h1, h2.1]

theorem oddPartial_87 : (575056643562593 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 87, oddTerm n := by
  rw [show (87 : ℕ) = 86 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_86
  have h2 := oddTerm_bounds_87
  linarith [h1, h2.1]

theorem oddPartial_88 : (11501132871247 / 2000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 88, oddTerm n := by
  rw [show (88 : ℕ) = 87 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_87
  have h2 := oddTerm_bounds_88
  linarith [h1, h2.1]

theorem oddPartial_89 : (145061032971747 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 89, oddTerm n := by
  rw [show (89 : ℕ) = 88 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_88
  have h2 := oddTerm_bounds_89
  linarith [h1, h2.1]

theorem oddPartial_90 : (145061032971747 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 90, oddTerm n := by
  rw [show (90 : ℕ) = 89 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_89
  have h2 := oddTerm_bounds_90
  linarith [h1, h2.1]

theorem oddPartial_91 : (576666377975569 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 91, oddTerm n := by
  rw [show (91 : ℕ) = 90 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_90
  have h2 := oddTerm_bounds_91
  linarith [h1, h2.1]

theorem oddPartial_92 : (28790983955521 / 5000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 92, oddTerm n := by
  rw [show (92 : ℕ) = 91 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_91
  have h2 := oddTerm_bounds_92
  linarith [h1, h2.1]

theorem oddPartial_93 : (575819679109721 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 93, oddTerm n := by
  rw [show (93 : ℕ) = 92 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_92
  have h2 := oddTerm_bounds_93
  linarith [h1, h2.1]

theorem oddPartial_94 : (57067127040583 / 10000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 94, oddTerm n := by
  rw [show (94 : ℕ) = 93 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_93
  have h2 := oddTerm_bounds_94
  linarith [h1, h2.1]

theorem oddPartial_95 : (57067127040583 / 10000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 95, oddTerm n := by
  rw [show (95 : ℕ) = 94 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_94
  have h2 := oddTerm_bounds_95
  linarith [h1, h2.1]

theorem oddPartial_96 : (57064074510499 / 10000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 96, oddTerm n := by
  rw [show (96 : ℕ) = 95 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_95
  have h2 := oddTerm_bounds_96
  linarith [h1, h2.1]

theorem oddPartial_97 : (569155801229789 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 97, oddTerm n := by
  rw [show (97 : ℕ) = 96 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_96
  have h2 := oddTerm_bounds_97
  linarith [h1, h2.1]

theorem oddPartial_98 : (568400480044901 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 98, oddTerm n := by
  rw [show (98 : ℕ) = 97 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_97
  have h2 := oddTerm_bounds_98
  linarith [h1, h2.1]

theorem oddPartial_99 : (284200240022109 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 99, oddTerm n := by
  rw [show (99 : ℕ) = 98 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_98
  have h2 := oddTerm_bounds_99
  linarith [h1, h2.1]

theorem oddPartial_100 : (284200240022109 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 100, oddTerm n := by
  rw [show (100 : ℕ) = 99 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_99
  have h2 := oddTerm_bounds_100
  linarith [h1, h2.1]

theorem oddPartial_101 : (572252648608337 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 101, oddTerm n := by
  rw [show (101 : ℕ) = 100 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_100
  have h2 := oddTerm_bounds_101
  linarith [h1, h2.1]

theorem oddPartial_102 : (114323024735321 / 20000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 102, oddTerm n := by
  rw [show (102 : ℕ) = 101 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_101
  have h2 := oddTerm_bounds_102
  linarith [h1, h2.1]

theorem oddPartial_103 : (286105294992497 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 103, oddTerm n := by
  rw [show (103 : ℕ) = 102 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_102
  have h2 := oddTerm_bounds_103
  linarith [h1, h2.1]

theorem oddPartial_104 : (2859490313491 / 500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 104, oddTerm n := by
  rw [show (104 : ℕ) = 103 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_103
  have h2 := oddTerm_bounds_104
  linarith [h1, h2.1]

theorem oddPartial_105 : (2859490313491 / 500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 105, oddTerm n := by
  rw [show (105 : ℕ) = 104 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_104
  have h2 := oddTerm_bounds_105
  linarith [h1, h2.1]

theorem oddPartial_106 : (142862838475583 / 25000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 106, oddTerm n := by
  rw [show (106 : ℕ) = 105 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_105
  have h2 := oddTerm_bounds_106
  linarith [h1, h2.1]

theorem oddPartial_107 : (57197490181947 / 10000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 107, oddTerm n := by
  rw [show (107 : ℕ) = 106 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_106
  have h2 := oddTerm_bounds_107
  linarith [h1, h2.1]

theorem oddPartial_108 : (285499299094537 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 108, oddTerm n := by
  rw [show (108 : ℕ) = 107 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_107
  have h2 := oddTerm_bounds_108
  linarith [h1, h2.1]

theorem oddPartial_109 : (569018276930743 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 109, oddTerm n := by
  rw [show (109 : ℕ) = 108 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_108
  have h2 := oddTerm_bounds_109
  linarith [h1, h2.1]

theorem oddPartial_110 : (569018276930743 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 110, oddTerm n := by
  rw [show (110 : ℕ) = 109 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_109
  have h2 := oddTerm_bounds_110
  linarith [h1, h2.1]

theorem oddPartial_111 : (567607768852197 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 111, oddTerm n := by
  rw [show (111 : ℕ) = 110 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_110
  have h2 := oddTerm_bounds_111
  linarith [h1, h2.1]

theorem oddPartial_112 : (567560660084767 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 112, oddTerm n := by
  rw [show (112 : ℕ) = 111 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_111
  have h2 := oddTerm_bounds_112
  linarith [h1, h2.1]

theorem oddPartial_113 : (283978022104097 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 113, oddTerm n := by
  rw [show (113 : ℕ) = 112 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_112
  have h2 := oddTerm_bounds_113
  linarith [h1, h2.1]

theorem oddPartial_114 : (14198901105203 / 2500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 114, oddTerm n := by
  rw [show (114 : ℕ) = 113 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_113
  have h2 := oddTerm_bounds_114
  linarith [h1, h2.1]

theorem oddPartial_115 : (14198901105203 / 2500000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 115, oddTerm n := by
  rw [show (115 : ℕ) = 114 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_114
  have h2 := oddTerm_bounds_115
  linarith [h1, h2.1]

theorem oddPartial_116 : (567956044207843 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 116, oddTerm n := by
  rw [show (116 : ℕ) = 115 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_115
  have h2 := oddTerm_bounds_116
  linarith [h1, h2.1]

theorem oddPartial_117 : (567705953046167 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 117, oddTerm n := by
  rw [show (117 : ℕ) = 116 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_116
  have h2 := oddTerm_bounds_117
  linarith [h1, h2.1]

theorem oddPartial_118 : (113541190609229 / 20000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 118, oddTerm n := by
  rw [show (118 : ℕ) = 117 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_117
  have h2 := oddTerm_bounds_118
  linarith [h1, h2.1]

theorem oddPartial_119 : (284025206154547 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 119, oddTerm n := by
  rw [show (119 : ℕ) = 118 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_118
  have h2 := oddTerm_bounds_119
  linarith [h1, h2.1]

theorem oddPartial_120 : (284025206154547 / 50000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 120, oddTerm n := by
  rw [show (120 : ℕ) = 119 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_119
  have h2 := oddTerm_bounds_120
  linarith [h1, h2.1]

theorem oddPartial_121 : (567959599624443 / 100000000000000 : ℝ) ≤ ∑ n ∈ Finset.Icc 2 121, oddTerm n := by
  rw [show (121 : ℕ) = 120 + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]
  have h1 := oddPartial_120
  have h2 := oddTerm_bounds_121
  linarith [h1, h2.1]

end PsiOmega

#print axioms PsiOmega.oddPartial_121
