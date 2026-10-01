import DHLocateSkeleton

/-! # Generated (gen_locate.py): two-sided bounds for `ex (1617/2000) n = exp(-(1617/2000) log n)`, `n ∈ NS`

`log n` from `PsiOmega.Num.log_bound_n`; `exp(-y) = exp(-(y/8))^8` (`Real.exp_nat_mul`) with `exp(-(y/8))` from
`Real.exp_bound` (12 terms). Stage 3 of the zero-location certificate (`DHLocateSkeleton`). -/

open Real Finset

namespace PsiOmega.Locate

/-- Interval product with explicit outer bounds; the eight corner checks are numeral comparisons. -/
theorem mul_bounds_of {x y a b c d lo hi : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (h1 : lo ≤ a * c) (h2 : lo ≤ a * d) (h3 : lo ≤ b * c) (h4 : lo ≤ b * d)
    (h5 : a * c ≤ hi) (h6 : a * d ≤ hi) (h7 : b * c ≤ hi) (h8 : b * d ≤ hi) :
    lo ≤ x * y ∧ x * y ≤ hi := by
  have h := PsiOmega.Num.mul_bounds hx hy
  exact ⟨le_trans (le_min (le_min h1 h2) (le_min h3 h4)) h.1,
    le_trans h.2 (max_le (max_le h5 h6) (max_le h7 h8))⟩

/-- `exp(-r)` within `r¹²·13/(12!·12)` of its degree-11 Taylor polynomial, `0 ≤ r ≤ 1` (`Real.exp_bound`). -/
theorem exp_neg_poly_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    1 - r + r ^ 2 / 2 - r ^ 3 / 6 + r ^ 4 / 24 - r ^ 5 / 120 + r ^ 6 / 720 - r ^ 7 / 5040 + r ^ 8 / 40320 - r ^ 9 / 362880 + r ^ 10 / 3628800 - r ^ 11 / 39916800 - r ^ 12 * (13 / 5748019200) ≤ Real.exp (-r) ∧
      Real.exp (-r) ≤ 1 - r + r ^ 2 / 2 - r ^ 3 / 6 + r ^ 4 / 24 - r ^ 5 / 120 + r ^ 6 / 720 - r ^ 7 / 5040 + r ^ 8 / 40320 - r ^ 9 / 362880 + r ^ 10 / 3628800 - r ^ 11 / 39916800 + r ^ 12 * (13 / 5748019200) := by
  have hx : |(-r)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hr0]; exact hr1
  have h := Real.exp_bound hx (n := 12) (by norm_num)
  rw [abs_neg, abs_of_nonneg hr0] at h
  have h2 := abs_sub_le_iff.1 h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one] at h2
  norm_num at h2
  constructor <;> nlinarith [h2.1, h2.2]

/-- Lower bound for `exp(-q)`, `0 ≤ q ≤ 8`, from the polynomial at `q/8` and the eighth power. -/
theorem exp_neg_ge_of {q a lo : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 8) (ha0 : 0 ≤ a)
    (ha : a ≤ 1 - (q / 8) + (q / 8) ^ 2 / 2 - (q / 8) ^ 3 / 6 + (q / 8) ^ 4 / 24 - (q / 8) ^ 5 / 120 + (q / 8) ^ 6 / 720 - (q / 8) ^ 7 / 5040 + (q / 8) ^ 8 / 40320 - (q / 8) ^ 9 / 362880 + (q / 8) ^ 10 / 3628800 - (q / 8) ^ 11 / 39916800 - (q / 8) ^ 12 * (13 / 5748019200))
    (hlo : lo ≤ a ^ 8) : lo ≤ Real.exp (-q) := by
  have hb := exp_neg_poly_bounds (r := q / 8) (by positivity) (by linarith)
  have h1 : a ≤ Real.exp (-(q / 8)) := le_trans ha hb.1
  have e : Real.exp (-q) = Real.exp (-(q / 8)) ^ 8 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e]
  exact le_trans hlo (pow_le_pow_left₀ ha0 h1 8)

/-- Upper bound for `exp(-q)`, `0 ≤ q ≤ 8`. -/
theorem exp_neg_le_of {q b hi : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 8)
    (hb : 1 - (q / 8) + (q / 8) ^ 2 / 2 - (q / 8) ^ 3 / 6 + (q / 8) ^ 4 / 24 - (q / 8) ^ 5 / 120 + (q / 8) ^ 6 / 720 - (q / 8) ^ 7 / 5040 + (q / 8) ^ 8 / 40320 - (q / 8) ^ 9 / 362880 + (q / 8) ^ 10 / 3628800 - (q / 8) ^ 11 / 39916800 + (q / 8) ^ 12 * (13 / 5748019200) ≤ b)
    (hhi : b ^ 8 ≤ hi) : Real.exp (-q) ≤ hi := by
  have hp := exp_neg_poly_bounds (r := q / 8) (by positivity) (by linarith)
  have h1 : Real.exp (-(q / 8)) ≤ b := le_trans hp.2 hb
  have e : Real.exp (-q) = Real.exp (-(q / 8)) ^ 8 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e]
  exact le_trans (pow_le_pow_left₀ (Real.exp_pos _).le h1 8) hhi

theorem ex_one : ex (1617 / 2000) 1 = 1 := by simp [ex]

theorem cC_one : cC 1 = 1 := by simp [cC]

theorem sC_one : sC 1 = 0 := by simp [sC]

theorem exB_2 : (570975204157841 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 2 ∧ ex (1617 / 2000) 2 ≤ (570975204250169 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_2
  have hlo := exp_neg_ge_of (q := (560409495561779 / 1000000000000000 : ℝ)) (a := (93234609473602627177 / 100000000000000000000 : ℝ)) (lo := (570975204157841 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (280204747700039 / 500000000000000 : ℝ)) (b := (5827163092217946461 / 6250000000000000000 : ℝ)) (hi := (570975204250169 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_3 : (411384065241603 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 3 ∧ ex (1617 / 2000) 3 ≤ (411384065330831 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_3
  have hlo := exp_neg_ge_of (q := (888228035518761 / 1000000000000000 : ℝ)) (a := (44745661978243193841 / 50000000000000000000 : ℝ)) (lo := (411384065241603 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (888228035301867 / 1000000000000000 : ℝ)) (b := (89491323958912654087 / 100000000000000000000 : ℝ)) (hi := (411384065330831 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_4 : (40751585470867 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 4 ∧ ex (1617 / 2000) 4 ≤ (326012683843201 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_4
  have hlo := exp_neg_ge_of (q := (280204747777939 / 250000000000000 : ℝ)) (a := (86926924037080166487 / 100000000000000000000 : ℝ)) (lo := (40751585470867 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (44832759635113 / 40000000000000 : ℝ)) (b := (43463462019811014649 / 50000000000000000000 : ℝ)) (hi := (326012683843201 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_6 : (1468063129007 / 6250000000000 : ℝ) ≤ ex (1617 / 2000) 6 ∧ ex (1617 / 2000) 6 ≤ (117445050354833 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_6
  have hlo := exp_neg_ge_of (q := (1448637531069841 / 1000000000000000 : ℝ)) (a := (41718443201849130459 / 50000000000000000000 : ℝ)) (lo := (1468063129007 / 6250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1448637530778023 / 1000000000000000 : ℝ)) (b := (16687377281348361929 / 20000000000000000000 : ℝ)) (hi := (117445050354833 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_7 : (103683163336173 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 7 ∧ ex (1617 / 2000) 7 ≤ (207366326733049 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_7
  have hlo := exp_neg_ge_of (q := (314653671142201 / 200000000000000 : ℝ)) (a := (82147108127814636899 / 100000000000000000000 : ℝ)) (lo := (103683163336173 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1573268355418279 / 1000000000000000 : ℝ)) (b := (82147108130820462711 / 100000000000000000000 : ℝ)) (hi := (207366326733049 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_8 : (93072579334823 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 8 ∧ ex (1617 / 2000) 8 ≤ (186145158732001 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_8
  have hlo := exp_neg_ge_of (q := (168122848668549 / 100000000000000 : ℝ)) (a := (40522989076632893971 / 50000000000000000000 : ℝ)) (lo := (93072579334823 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (336245697270103 / 200000000000000 : ℝ)) (b := (40522989078329669183 / 50000000000000000000 : ℝ)) (hi := (186145158732001 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_9 : (42309212284171 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 9 ∧ ex (1617 / 2000) 9 ≤ (169236849195691 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_9
  have hlo := exp_neg_ge_of (q := (22205700887823 / 12500000000000 : ℝ)) (a := (80086970634964885253 / 100000000000000000000 : ℝ)) (lo := (42309212284171 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (888228035338591 / 500000000000000 : ℝ)) (b := (80086970638455262131 / 100000000000000000000 : ℝ)) (hi := (169236849195691 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_11 : (71945563467787 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 11 ∧ ex (1617 / 2000) 11 ≤ (143891126986761 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_11
  have hlo := exp_neg_ge_of (q := (193869832831327 / 100000000000000 : ℝ)) (a := (78479142978893882137 / 100000000000000000000 : ℝ)) (lo := (71945563467787 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (969349163978773 / 500000000000000 : ℝ)) (b := (78479142982383515027 / 100000000000000000000 : ℝ)) (hi := (143891126986761 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_12 : (67058211585547 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 12 ∧ ex (1617 / 2000) 12 ≤ (33529105804731 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_12
  have hlo := exp_neg_ge_of (q := (401809405322037 / 200000000000000 : ℝ)) (a := (3889602759781496431 / 5000000000000000000 : ℝ)) (lo := (67058211585547 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1004523513126781 / 500000000000000 : ℝ)) (b := (15558411039819552319 / 20000000000000000000 : ℝ)) (hi := (33529105804731 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_13 : (125712018452517 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 13 ∧ ex (1617 / 2000) 13 ≤ (31428004624351 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_13
  have hlo := exp_neg_ge_of (q := (2073761555764617 / 1000000000000000 : ℝ)) (a := (19291327264788612921 / 25000000000000000000 : ℝ)) (lo := (125712018452517 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2073761555407569 / 1000000000000000 : ℝ)) (b := (77165309062598458231 / 100000000000000000000 : ℝ)) (hi := (31428004624351 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_14 : (29600257677443 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 14 ∧ ex (1617 / 2000) 14 ≤ (59200515376037 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_14
  have hlo := exp_neg_ge_of (q := (213367785125109 / 100000000000000 : ℝ)) (a := (76589535457033696417 / 100000000000000000000 : ℝ)) (lo := (29600257677443 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (213367785089383 / 100000000000000 : ℝ)) (b := (382947677302270261 / 500000000000000000 : ℝ)) (hi := (59200515376037 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_16 : (106284269975321 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 16 ∧ ex (1617 / 2000) 16 ≤ (106284270019559 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_16
  have hlo := exp_neg_ge_of (q := (2241637982238547 / 1000000000000000 : ℝ)) (a := (75562901225340944457 / 100000000000000000000 : ℝ)) (lo := (106284269975321 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2241637981822341 / 1000000000000000 : ℝ)) (b := (75562901229272267031 / 100000000000000000000 : ℝ)) (hi := (106284270019559 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_17 : (101200357552281 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 17 ∧ ex (1617 / 2000) 17 ≤ (101200357598247 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_17
  have hlo := exp_neg_ge_of (q := (1145326494504843 / 500000000000000 : ℝ)) (a := (75101352081914544183 / 100000000000000000000 : ℝ)) (lo := (101200357552281 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (143165811784719 / 62500000000000 : ℝ)) (b := (75101352086178391839 / 100000000000000000000 : ℝ)) (hi := (101200357598247 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_18 : (24157511120909 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 18 ∧ ex (1617 / 2000) 18 ≤ (96630044529957 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_18
  have hlo := exp_neg_ge_of (q := (467373113324169 / 200000000000000 : ℝ)) (a := (14933754862087609323 / 20000000000000000000 : ℝ)) (lo := (24157511120909 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (233686556614151 / 100000000000000 : ℝ)) (b := (74668774314912140807 / 100000000000000000000 : ℝ)) (hi := (96630044529957 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_19 : (18499402819117 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 19 ∧ ex (1617 / 2000) 19 ≤ (46248507070751 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_19
  have hlo := exp_neg_ge_of (q := (1190289457516237 / 500000000000000 : ℝ)) (a := (74261884212494506097 / 100000000000000000000 : ℝ)) (lo := (18499402819117 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2380578914536093 / 1000000000000000 : ℝ)) (b := (74261884217102497697 / 100000000000000000000 : ℝ)) (hi := (46248507070751 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_21 : (85307202455289 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 21 ∧ ex (1617 / 2000) 21 ≤ (10663400312419 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_21
  have hlo := exp_neg_ge_of (q := (1230748195646511 / 500000000000000 : ℝ)) (a := (918931683187077111 / 1250000000000000000 : ℝ)) (lo := (85307202455289 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2461496390776543 / 1000000000000000 : ℝ)) (b := (7351453465971258371 / 10000000000000000000 : ℝ)) (hi := (10663400312419 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_22 : (82158265573289 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 22 ∧ ex (1617 / 2000) 22 ≤ (10269783202027 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_22
  have hlo := exp_neg_ge_of (q := (499821564787787 / 200000000000000 : ℝ)) (a := (36584861237008638227 / 50000000000000000000 : ℝ)) (lo := (82158265573289 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (312388477927063 / 125000000000000 : ℝ)) (b := (36584861239397966761 / 50000000000000000000 : ℝ)) (hi := (10269783202027 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_23 : (39628994093933 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 23 ∧ ex (1617 / 2000) 23 ≤ (39628994114811 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_23
  have hlo := exp_neg_ge_of (q := (507009414796233 / 200000000000000 : ℝ)) (a := (14568350319174906167 / 20000000000000000000 : ℝ)) (lo := (39628994093933 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (633761768363601 / 250000000000000 : ℝ)) (b := (72841751600671268743 / 100000000000000000000 : ℝ)) (hi := (39628994114811 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_24 : (38288576047853 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 24 ∧ ex (1617 / 2000) 24 ≤ (76577152136293 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_24
  have hlo := exp_neg_ge_of (q := (2569456522241499 / 1000000000000000 : ℝ)) (a := (36264559431252029687 / 50000000000000000000 : ℝ)) (lo := (38288576047853 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (513891304342309 / 200000000000000 : ℝ)) (b := (1450582377346184831 / 2000000000000000000 : ℝ)) (hi := (76577152136293 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_26 : (71778445395793 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 26 ∧ ex (1617 / 2000) 26 ≤ (3588922271707 / 50000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_26
  have hlo := exp_neg_ge_of (q := (1317085525699571 / 500000000000000 : ℝ)) (a := (35972387274873144911 / 50000000000000000000 : ℝ)) (lo := (71778445395793 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2634171050865001 / 1000000000000000 : ℝ)) (b := (71944774554550606239 / 100000000000000000000 : ℝ)) (hi := (3588922271707 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_27 : (17405335746111 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 27 ∧ ex (1617 / 2000) 27 ≤ (13924268604347 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_27
  have hlo := exp_neg_ge_of (q := (1332342053287227 / 500000000000000 : ℝ)) (a := (35835445168802152053 / 50000000000000000000 : ℝ)) (lo := (17405335746111 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (333085513254867 / 125000000000000 : ℝ)) (b := (14334178068480555833 / 20000000000000000000 : ℝ)) (hi := (13924268604347 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_28 : (33802026338479 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 28 ∧ ex (1617 / 2000) 28 ≤ (67604052713241 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_28
  have hlo := exp_neg_ge_of (q := (2694087346887517 / 1000000000000000 : ℝ)) (a := (71407954280344612263 / 100000000000000000000 : ℝ)) (lo := (33802026338479 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (336760918293867 / 125000000000000 : ℝ)) (b := (14281590857027018703 / 20000000000000000000 : ℝ)) (hi := (67604052713241 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_29 : (16428247125177 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 29 ∧ ex (1617 / 2000) 29 ≤ (2053530891751 / 31250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_29
  have hlo := exp_neg_ge_of (q := (2722458678955639 / 1000000000000000 : ℝ)) (a := (71155160453496180039 / 100000000000000000000 : ℝ)) (lo := (16428247125177 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (272245867841823 / 100000000000000 : ℝ)) (b := (71155160458277199209 / 100000000000000000000 : ℝ)) (hi := (2053530891751 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_31 : (62263577483289 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 31 ∧ ex (1617 / 2000) 31 ≤ (31131788758417 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_31
  have hlo := exp_neg_ge_of (q := (2776378655238813 / 1000000000000000 : ℝ)) (a := (35338593730345469457 / 50000000000000000000 : ℝ)) (lo := (62263577483289 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (34704733183753 / 12500000000000 : ℝ)) (b := (7067718746545042279 / 10000000000000000000 : ℝ)) (hi := (31131788758417 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_32 : (7585710343291 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 32 ∧ ex (1617 / 2000) 32 ≤ (7585710347381 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_32
  have hlo := exp_neg_ge_of (q := (2802047477826503 / 1000000000000000 : ℝ)) (a := (8806346983017353771 / 12500000000000000000 : ℝ)) (lo := (7585710343291 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (17512796733047 / 6250000000000 : ℝ)) (b := (35225387934443421737 / 50000000000000000000 : ℝ)) (hi := (7585710347381 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_33 : (59194516749353 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 33 ∧ ex (1617 / 2000) 33 ≤ (5919451678129 / 100000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_33
  have hlo := exp_neg_ge_of (q := (2826926363858857 / 1000000000000000 : ℝ)) (a := (17558006020319737081 / 25000000000000000000 : ℝ)) (lo := (59194516749353 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (2826926363319543 / 1000000000000000 : ℝ)) (b := (70232024086015302101 / 100000000000000000000 : ℝ)) (hi := (5919451678129 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_34 : (14445723703647 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 34 ∧ ex (1617 / 2000) 34 ≤ (2889144742289 / 50000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_34
  have hlo := exp_neg_ge_of (q := (2851062484565603 / 1000000000000000 : ℝ)) (a := (70020452323017988603 / 100000000000000000000 : ℝ)) (lo := (14445723703647 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1425531242013011 / 500000000000000 : ℝ)) (b := (70020452327742600513 / 100000000000000000000 : ℝ)) (hi := (2889144742289 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_36 : (27586679689153 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 36 ∧ ex (1617 / 2000) 36 ≤ (27586679704057 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_36
  have hlo := exp_neg_ge_of (q := (144863753107777 / 50000000000000 : ℝ)) (a := (69617140127296294093 / 100000000000000000000 : ℝ)) (lo := (27586679689153 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (724318765403891 / 250000000000000 : ℝ)) (b := (69617140131997544979 / 100000000000000000000 : ℝ)) (hi := (27586679704057 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_37 : (13491148248267 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 37 ∧ ex (1617 / 2000) 37 ≤ (6745574127779 / 125000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_37
  have hlo := exp_neg_ge_of (q := (729856783196689 / 250000000000000 : ℝ)) (a := (13884927259408787231 / 20000000000000000000 : ℝ)) (lo := (13491148248267 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1459713566123317 / 500000000000000 : ℝ)) (b := (17356159075433420251 / 25000000000000000000 : ℝ)) (hi := (6745574127779 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_38 : (3300843844337 / 62500000000000 : ℝ) ≤ ex (1617 / 2000) 38 ∧ ex (1617 / 2000) 38 ≤ (26406750768971 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_38
  have hlo := exp_neg_ge_of (q := (2940988410552787 / 1000000000000000 : ℝ)) (a := (69237777733614671573 / 100000000000000000000 : ℝ)) (lo := (3300843844337 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (22976471953223 / 7812500000000 : ℝ)) (b := (69237777738293080769 / 100000000000000000000 : ℝ)) (hi := (26406750768971 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_39 : (10343184239867 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 39 ∧ ex (1617 / 2000) 39 ≤ (25857960613649 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_39
  have hlo := exp_neg_ge_of (q := (2961989591309909 / 1000000000000000 : ℝ)) (a := (863203208899000247 / 1250000000000000000 : ℝ)) (lo := (10343184239867 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1480994795384783 / 500000000000000 : ℝ)) (b := (69056256716587279647 / 100000000000000000000 : ℝ)) (hi := (25857960613649 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_41 : (4966657951961 / 100000000000000 : ℝ) ≤ ex (1617 / 2000) 41 ∧ ex (1617 / 2000) 41 ≤ (12416644886619 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_41
  have hlo := exp_neg_ge_of (q := (187651438521541 / 62500000000000 : ℝ)) (a := (13741622923346488143 / 20000000000000000000 : ℝ)) (lo := (4966657951961 / 100000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3002423015804157 / 1000000000000000 : ℝ)) (b := (34354057310689028131 / 50000000000000000000 : ℝ)) (hi := (12416644886619 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_42 : (48708297340869 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 42 ∧ ex (1617 / 2000) 42 ≤ (24354148683611 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_42
  have hlo := exp_neg_ge_of (q := (3021905886796377 / 1000000000000000 : ℝ)) (a := (34270494646195598559 / 50000000000000000000 : ℝ)) (lo := (48708297340869 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3021905886255819 / 1000000000000000 : ℝ)) (b := (17135247324256577961 / 25000000000000000000 : ℝ)) (hi := (24354148683611 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_43 : (23895204839309 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 43 ∧ ex (1617 / 2000) 43 ≤ (23895204852239 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_43
  have hlo := exp_neg_ge_of (q := (3040930293952563 / 1000000000000000 : ℝ)) (a := (34189094490962970229 / 50000000000000000000 : ℝ)) (lo := (23895204839309 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1520465146705977 / 500000000000000 : ℝ)) (b := (17094547246637697323 / 25000000000000000000 : ℝ)) (hi := (23895204852239 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_44 : (23455166230959 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 44 ∧ ex (1617 / 2000) 44 ≤ (9382066497461 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_44
  have hlo := exp_neg_ge_of (q := (764879329859317 / 250000000000000 : ℝ)) (a := (68219505002106041139 / 100000000000000000000 : ℝ)) (lo := (23455166230959 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3059517318896617 / 1000000000000000 : ℝ)) (b := (68219505006720837117 / 100000000000000000000 : ℝ)) (hi := (9382066497461 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_46 : (1131358649743 / 25000000000000 : ℝ) ≤ ex (1617 / 2000) 46 ∧ ex (1617 / 2000) 46 ≤ (22627173007109 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_46
  have hlo := exp_neg_ge_of (q := (1547728284737923 / 500000000000000 : ℝ)) (a := (67913722634710518353 / 100000000000000000000 : ℝ)) (lo := (1131358649743 / 25000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1547728284467563 / 500000000000000 : ℝ)) (b := (67913722639305901019 / 100000000000000000000 : ℝ)) (hi := (22627173007109 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_47 : (44474275465127 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 47 ∧ ex (1617 / 2000) 47 ≤ (8894855097841 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_47
  have hlo := exp_neg_ge_of (q := (1556422168198509 / 500000000000000 : ℝ)) (a := (16941568608112747733 / 25000000000000000000 : ℝ)) (lo := (44474275465127 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3112844335856271 / 1000000000000000 : ℝ)) (b := (8470784304629623809 / 12500000000000000000 : ℝ)) (hi := (8894855097841 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_48 : (43723655054697 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 48 ∧ ex (1617 / 2000) 48 ≤ (10930913769593 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_48
  have hlo := exp_neg_ge_of (q := (625973203546697 / 200000000000000 : ℝ)) (a := (4226390045417852073 / 6250000000000000000 : ℝ)) (lo := (43723655054697 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (625973203438543 / 200000000000000 : ℝ)) (b := (67622240731262459861 / 100000000000000000000 : ℝ)) (hi := (10930913769593 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_49 : (43000793436911 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 49 ∧ ex (1617 / 2000) 49 ≤ (21500396730099 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_49
  have hlo := exp_neg_ge_of (q := (1573268355718457 / 500000000000000 : ℝ)) (a := (13496294747499420631 / 20000000000000000000 : ℝ)) (lo := (43000793436911 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (786634177724031 / 250000000000000 : ℝ)) (b := (8435184217758120763 / 12500000000000000000 : ℝ)) (hi := (21500396730099 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_51 : (20816107248037 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 51 ∧ ex (1617 / 2000) 51 ≤ (333057716149 / 8000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_51
  have hlo := exp_neg_ge_of (q := (1589440512236059 / 500000000000000 : ℝ)) (a := (16802298571948570207 / 25000000000000000000 : ℝ)) (lo := (20816107248037 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (99340031997853 / 31250000000000 : ℝ)) (b := (33604597146172408179 / 50000000000000000000 : ℝ)) (hi := (333057716149 / 8000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_52 : (40983712516969 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 52 ∧ ex (1617 / 2000) 52 ≤ (10245928134793 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_52
  have hlo := exp_neg_ge_of (q := (638916109377519 / 200000000000000 : ℝ)) (a := (67077429588728224417 / 100000000000000000000 : ℝ)) (lo := (40983712516969 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (79864513658669 / 25000000000000 : ℝ)) (b := (67077429593270388157 / 100000000000000000000 : ℝ)) (hi := (10245928134793 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_53 : (50446724437 / 1250000000000 : ℝ) ≤ ex (1617 / 2000) 53 ∧ ex (1617 / 2000) 53 ≤ (20178689785733 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_53
  have hlo := exp_neg_ge_of (q := (802495253130353 / 250000000000000 : ℝ)) (a := (66948425842278815167 / 100000000000000000000 : ℝ)) (lo := (50446724437 / 1250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (641996202396113 / 200000000000000 : ℝ)) (b := (535587406774502399 / 800000000000000000 : ℝ)) (hi := (20178689785733 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_54 : (39752060527213 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 54 ∧ ex (1617 / 2000) 54 ≤ (19876030274377 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_54
  have hlo := exp_neg_ge_of (q := (1612546801030873 / 500000000000000 : ℝ)) (a := (66822074713134393551 / 100000000000000000000 : ℝ)) (lo := (39752060527213 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3225093601520889 / 1000000000000000 : ℝ)) (b := (66822074717660376479 / 100000000000000000000 : ℝ)) (hi := (19876030274377 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_56 : (9650059445499 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 56 ∧ ex (1617 / 2000) 56 ≤ (19300118901459 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_56
  have hlo := exp_neg_ge_of (q := (406812105296739 / 125000000000000 : ℝ)) (a := (33288463653493705759 / 50000000000000000000 : ℝ)) (lo := (9650059445499 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3254496841833039 / 1000000000000000 : ℝ)) (b := (66576927311497912867 / 100000000000000000000 : ℝ)) (hi := (19300118901459 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_57 : (9512949421207 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 57 ∧ ex (1617 / 2000) 57 ≤ (7610359541091 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_57
  have hlo := exp_neg_ge_of (q := (102150217201837 / 31250000000000 : ℝ)) (a := (16614485844388298989 / 25000000000000000000 : ℝ)) (lo := (9512949421207 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (204300434369869 / 62500000000000 : ℝ)) (b := (66457943382056213459 / 100000000000000000000 : ℝ)) (hi := (7610359541091 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_58 : (7504097405083 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 58 ∧ ex (1617 / 2000) 58 ≤ (18760243524387 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_58
  have hlo := exp_neg_ge_of (q := (65657363490113 / 20000000000000 : ℝ)) (a := (33170617984610641347 / 50000000000000000000 : ℝ)) (lo := (7504097405083 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (328286817388437 / 100000000000000 : ℝ)) (b := (66341235974383656831 / 100000000000000000000 : ℝ)) (hi := (18760243524387 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_59 : (37005489075959 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 59 ∧ ex (1617 / 2000) 59 ≤ (1156421534429 / 31250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_59
  have hlo := exp_neg_ge_of (q := (3296689023935651 / 1000000000000000 : ℝ)) (a := (3311336169242998253 / 5000000000000000000 : ℝ)) (lo := (37005489075959 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3296689023240613 / 1000000000000000 : ℝ)) (b := (16556680847656143317 / 25000000000000000000 : ℝ)) (hi := (1156421534429 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_61 : (36021419915021 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 61 ∧ ex (1617 / 2000) 61 ≤ (36021419944797 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_61
  have hlo := exp_neg_ge_of (q := (3323641519826089 / 1000000000000000 : ℝ)) (a := (8250497110337961299 / 12500000000000000000 : ℝ)) (lo := (36021419915021 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3323641519000939 / 1000000000000000 : ℝ)) (b := (16500994222380887119 / 25000000000000000000 : ℝ)) (hi := (36021419944797 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_62 : (17775479429047 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 62 ∧ ex (1617 / 2000) 62 ≤ (17775479444763 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_62
  have hlo := exp_neg_ge_of (q := (834197037749219 / 250000000000000 : ℝ)) (a := (65895599714273805133 / 100000000000000000000 : ℝ)) (lo := (17775479429047 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1668394075057143 / 500000000000000 : ℝ)) (b := (3294779986077809771 / 5000000000000000000 : ℝ)) (hi := (17775479444763 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_63 : (35094023733161 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 63 ∧ ex (1617 / 2000) 63 ≤ (35094023766051 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_63
  have hlo := exp_neg_ge_of (q := (669944885403573 / 200000000000000 : ℝ)) (a := (13157826072294463513 / 20000000000000000000 : ℝ)) (lo := (35094023733161 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1674862213041143 / 500000000000000 : ℝ)) (b := (13157826073835864061 / 20000000000000000000 : ℝ)) (hi := (35094023766051 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_64 : (17325010042939 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 64 ∧ ex (1617 / 2000) 64 ≤ (34650020120051 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_64
  have hlo := exp_neg_ge_of (q := (3362456973665763 / 1000000000000000 : ℝ)) (a := (32842252872881501977 / 50000000000000000000 : ℝ)) (lo := (17325010042939 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3362456972681237 / 1000000000000000 : ℝ)) (b := (16421126438465066361 / 25000000000000000000 : ℝ)) (hi := (34650020120051 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_66 : (1056206289819 / 31250000000000 : ℝ) ≤ ex (1617 / 2000) 66 ∧ ex (1617 / 2000) 66 ≤ (33798601310493 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_66
  have hlo := exp_neg_ge_of (q := (169366792988379 / 50000000000000 : ℝ)) (a := (65480553374734514401 / 100000000000000000000 : ℝ)) (lo := (1056206289819 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3387335858695871 / 1000000000000000 : ℝ)) (b := (32740276691760773427 / 50000000000000000000 : ℝ)) (hi := (33798601310493 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_67 : (8347540413491 / 250000000000000 : ℝ) ≤ ex (1617 / 2000) 67 ∧ ex (1617 / 2000) 67 ≤ (33390161691111 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_67
  have hlo := exp_neg_ge_of (q := (3399493983647897 / 1000000000000000 : ℝ)) (a := (65381113871275765877 / 100000000000000000000 : ℝ)) (lo := (8347540413491 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3399493982537331 / 1000000000000000 : ℝ)) (b := (32690556940183850581 / 50000000000000000000 : ℝ)) (hi := (33390161691111 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_68 : (16496300075059 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 68 ∧ ex (1617 / 2000) 68 ≤ (6598520037603 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_68
  have hlo := exp_neg_ge_of (q := (1705735990267017 / 500000000000000 : ℝ)) (a := (65283295271683686301 / 100000000000000000000 : ℝ)) (lo := (16496300075059 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (682294395877481 / 200000000000000 : ℝ)) (b := (32641647640528503623 / 50000000000000000000 : ℝ)) (hi := (6598520037603 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_69 : (32605473370721 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 69 ∧ ex (1617 / 2000) 69 ≤ (32605473409269 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_69
  have hlo := exp_neg_ge_of (q := (1711637554946421 / 500000000000000 : ℝ)) (a := (13037409578605158729 / 20000000000000000000 : ℝ)) (lo := (32605473370721 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (684655021742541 / 200000000000000 : ℝ)) (b := (16296761975664761919 / 25000000000000000000 : ℝ)) (hi := (32605473409269 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_71 : (31860869564809 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 71 ∧ ex (1617 / 2000) 71 ≤ (79652174011 / 2500000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_71
  have hlo := exp_neg_ge_of (q := (689275336312401 / 200000000000000 : ℝ)) (a := (4062442438426595131 / 6250000000000000000 : ℝ)) (lo := (31860869564809 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3446376680321689 / 1000000000000000 : ℝ)) (b := (2599963160996857117 / 4000000000000000000 : ℝ)) (hi := (79652174011 / 2500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_72 : (31502620119197 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 72 ∧ ex (1617 / 2000) 72 ≤ (15751310079599 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_72
  have hlo := exp_neg_ge_of (q := (3457684558220217 / 1000000000000000 : ℝ)) (a := (64907268720279030591 / 100000000000000000000 : ℝ)) (lo := (31502620119197 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3457684556952857 / 1000000000000000 : ℝ)) (b := (12981453746116172431 / 20000000000000000000 : ℝ)) (hi := (15751310079599 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_73 : (973539302123 / 31250000000000 : ℝ) ≤ ex (1617 / 2000) 73 ∧ ex (1617 / 2000) 73 ≤ (15576628854141 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_73
  have hlo := exp_neg_ge_of (q := (3468836459184393 / 1000000000000000 : ℝ)) (a := (8102106478232199943 / 12500000000000000000 : ℝ)) (lo := (973539302123 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (693767291578361 / 200000000000000 : ℝ)) (b := (64816851836350264497 / 100000000000000000000 : ℝ)) (hi := (15576628854141 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_74 : (30812444484751 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 74 ∧ ex (1617 / 2000) 74 ≤ (6162488905077 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_74
  have hlo := exp_neg_ge_of (q := (3479836628890337 / 1000000000000000 : ℝ)) (a := (32363894262808388223 / 50000000000000000000 : ℝ)) (lo := (30812444484751 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3479836627574191 / 1000000000000000 : ℝ)) (b := (32363894268143215987 / 50000000000000000000 : ℝ)) (hi := (6162488905077 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_76 : (15077599894591 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 76 ∧ ex (1617 / 2000) 76 ≤ (30155199830241 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_76
  have hlo := exp_neg_ge_of (q := (3501397906690359 / 1000000000000000 : ℝ)) (a := (16138392918367933207 / 25000000000000000000 : ℝ)) (lo := (15077599894591 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (700279581066319 / 200000000000000 : ℝ)) (b := (64553571684458216249 / 100000000000000000000 : ℝ)) (hi := (30155199830241 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_77 : (29838174414533 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 77 ∧ ex (1617 / 2000) 77 ≤ (14919087227869 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_77
  have hlo := exp_neg_ge_of (q := (3511966684652993 / 1000000000000000 : ℝ)) (a := (16117086608891434797 / 25000000000000000000 : ℝ)) (lo := (29838174414533 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1755983341637471 / 500000000000000 : ℝ)) (b := (2578733857867759829 / 4000000000000000000 : ℝ)) (hi := (14919087227869 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_78 : (5905701729409 / 200000000000000 : ℝ) ≤ ex (1617 / 2000) 78 ∧ ex (1617 / 2000) 78 ≤ (29528508688359 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_78
  have hlo := exp_neg_ge_of (q := (704479817495457 / 200000000000000 : ℝ)) (a := (64384331257553193229 / 100000000000000000000 : ℝ)) (lo := (5905701729409 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3522399086081159 / 1000000000000000 : ℝ)) (b := (8048041408601660703 / 12500000000000000000 : ℝ)) (hi := (29528508688359 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_79 : (14612970263961 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 79 ∧ ex (1617 / 2000) 79 ≤ (913310642791 / 31250000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_79
  have hlo := exp_neg_ge_of (q := (1766349294915949 / 500000000000000 : ℝ)) (a := (8037686721453240043 / 12500000000000000000 : ℝ)) (lo := (14612970263961 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (176634929420941 / 50000000000000 : ℝ)) (b := (64301493783008667393 / 100000000000000000000 : ℝ)) (hi := (913310642791 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_81 : (572822221747 / 20000000000000 : ℝ) ≤ ex (1617 / 2000) 81 ∧ ex (1617 / 2000) 81 ≤ (14320555564401 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_81
  have hlo := exp_neg_ge_of (q := (3552912142689667 / 1000000000000000 : ℝ)) (a := (64139228649717089181 / 100000000000000000000 : ℝ)) (lo := (572822221747 / 20000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (111028504413929 / 31250000000000 : ℝ)) (b := (64139228661320361981 / 100000000000000000000 : ℝ)) (hi := (14320555564401 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_82 : (3544798170297 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 82 ∧ ex (1617 / 2000) 82 ≤ (28358385403821 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_82
  have hlo := exp_neg_ge_of (q := (222677032035087 / 62500000000000 : ℝ)) (a := (64059742334318296137 / 100000000000000000000 : ℝ)) (lo := (3544798170297 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3562832511103399 / 1000000000000000 : ℝ)) (b := (64059742346020665353 / 100000000000000000000 : ℝ)) (hi := (28358385403821 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_83 : (28081827148069 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 83 ∧ ex (1617 / 2000) 83 ≤ (5616365437897 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_83
  have hlo := exp_neg_ge_of (q := (3572632632562371 / 1000000000000000 : ℝ)) (a := (15995329058858807707 / 25000000000000000000 : ℝ)) (lo := (28081827148069 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (714526526218231 / 200000000000000 : ℝ)) (b := (3998832265451873931 / 6250000000000000000 : ℝ)) (hi := (5616365437897 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_84 : (13905614999757 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 84 ∧ ex (1617 / 2000) 84 ≤ (27811230040879 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_84
  have hlo := exp_neg_ge_of (q := (559736778599 / 156250000000 : ℝ)) (a := (63903923690684844793 / 100000000000000000000 : ℝ)) (lo := (13905614999757 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (716463076309987 / 200000000000000 : ℝ)) (b := (31951961851282873121 / 50000000000000000000 : ℝ)) (hi := (27811230040879 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_86 : (27287138904019 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 86 ∧ ex (1617 / 2000) 86 ≤ (13643569472617 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_86
  have hlo := exp_neg_ge_of (q := (3601339790207973 / 1000000000000000 : ℝ)) (a := (31876068728433536923 / 50000000000000000000 : ℝ)) (lo := (27287138904019 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3601339788701519 / 1000000000000000 : ℝ)) (b := (63752137468903360511 / 100000000000000000000 : ℝ)) (hi := (13643569472617 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_87 : (27033276330837 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 87 ∧ ex (1617 / 2000) 87 ≤ (5406655274391 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_87
  have hlo := exp_neg_ge_of (q := (3610686715127591 / 1000000000000000 : ℝ)) (a := (63677695147967096489 / 100000000000000000000 : ℝ)) (lo := (27033276330837 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1805343356805351 / 500000000000000 : ℝ)) (b := (63677695160073414539 / 100000000000000000000 : ℝ)) (hi := (5406655274391 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_88 : (535692732709 / 20000000000000 : ℝ) ≤ ex (1617 / 2000) 88 ∧ ex (1617 / 2000) 88 ≤ (26784636676457 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_88
  have hlo := exp_neg_ge_of (q := (452490851963609 / 125000000000000 : ℝ)) (a := (63604189067867286929 / 100000000000000000000 : ℝ)) (lo := (535692732709 / 20000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3619926814182131 / 1000000000000000 : ℝ)) (b := (12720837816007800507 / 20000000000000000000 : ℝ)) (hi := (26784636676457 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_89 : (829407963281 / 31250000000000 : ℝ) ≤ ex (1617 / 2000) 89 ∧ ex (1617 / 2000) 89 ≤ (6635263716469 / 250000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_89
  have hlo := exp_neg_ge_of (q := (907265626534781 / 250000000000000 : ℝ)) (a := (12706319400349281553 / 20000000000000000000 : ℝ)) (lo := (829407963281 / 31250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1814531252301537 / 500000000000000 : ℝ)) (b := (12706319402795844007 / 20000000000000000000 : ℝ)) (hi := (6635263716469 / 250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_91 : (1303421973247 / 50000000000000 : ℝ) ≤ ex (1617 / 2000) 91 ∧ ex (1617 / 2000) 91 ≤ (521368790111 / 20000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_91
  have hlo := exp_neg_ge_of (q := (3647029912243261 / 1000000000000000 : ℝ)) (a := (31694534931934510769 / 50000000000000000000 : ℝ)) (lo := (1303421973247 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (455878738836261 / 125000000000000 : ℝ)) (b := (63389069876212241291 / 100000000000000000000 : ℝ)) (hi := (521368790111 / 20000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_92 : (25839109421359 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 92 ∧ ex (1617 / 2000) 92 ≤ (25839109461819 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_92
  have hlo := exp_neg_ge_of (q := (91396651644371 / 25000000000000 : ℝ)) (a := (63319094071592067663 / 100000000000000000000 : ℝ)) (lo := (25839109421359 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (913966516053447 / 250000000000000 : ℝ)) (b := (31659547041992568553 / 50000000000000000000 : ℝ)) (hi := (25839109461819 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_93 : (25614243603683 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 93 ∧ ex (1617 / 2000) 93 ≤ (5122848728797 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_93
  have hlo := exp_neg_ge_of (q := (916151672862767 / 250000000000000 : ℝ)) (a := (7906243848532728337 / 12500000000000000000 : ℝ)) (lo := (25614243603683 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (1832303344941277 / 500000000000000 : ℝ)) (b := (15812487700175372803 / 25000000000000000000 : ℝ)) (hi := (5122848728797 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_94 : (1587106780897 / 62500000000000 : ℝ) ≤ ex (1617 / 2000) 94 ∧ ex (1617 / 2000) 94 ≤ (25393708534491 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_94
  have hlo := exp_neg_ge_of (q := (114789182272113 / 31250000000000 : ℝ)) (a := (7897702664494851173 / 12500000000000000000 : ℝ)) (lo := (1587106780897 / 62500000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (367325383113203 / 100000000000000 : ℝ)) (b := (7897702666055254633 / 12500000000000000000 : ℝ)) (hi := (25393708534491 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_96 : (12482561426159 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 96 ∧ ex (1617 / 2000) 96 ≤ (24965122892113 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_96
  have hlo := exp_neg_ge_of (q := (3690275514054517 / 1000000000000000 : ℝ)) (a := (31523666026403322963 / 50000000000000000000 : ℝ)) (lo := (12482561426159 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (461284439058233 / 125000000000000 : ℝ)) (b := (7880916508171083911 / 12500000000000000000 : ℝ)) (hi := (24965122892113 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_97 : (24756831016479 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 97 ∧ ex (1617 / 2000) 97 ≤ (4951366211219 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_97
  have hlo := exp_neg_ge_of (q := (3698653827377587 / 1000000000000000 : ℝ)) (a := (6298133782859020609 / 10000000000000000000 : ℝ)) (lo := (24756831016479 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (231165864111431 / 62500000000000 : ℝ)) (b := (62981337841187819593 / 100000000000000000000 : ℝ)) (hi := (4951366211219 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_98 : (24552386792603 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 98 ∧ ex (1617 / 2000) 98 ≤ (24552386832037 / 1000000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_98
  have hlo := exp_neg_ge_of (q := (3706946207767347 / 1000000000000000 : ℝ)) (a := (62916088500105627643 / 100000000000000000000 : ℝ)) (lo := (24552386792603 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3706946206166921 / 1000000000000000 : ℝ)) (b := (31458044256368256331 / 50000000000000000000 : ℝ)) (hi := (24552386832037 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_99 : (3043960115329 / 125000000000000 : ℝ) ≤ ex (1617 / 2000) 99 ∧ ex (1617 / 2000) 99 ≤ (608792024047 / 25000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_99
  have hlo := exp_neg_ge_of (q := (1857577200050183 / 500000000000000 : ℝ)) (a := (1964111505814220929 / 3125000000000000000 : ℝ)) (lo := (3043960115329 / 125000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (371515439849449 / 100000000000000 : ℝ)) (b := (62851568198717056887 / 100000000000000000000 : ℝ)) (hi := (608792024047 / 25000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_101 : (95844271357 / 4000000000000 : ℝ) ≤ ex (1617 / 2000) 101 ∧ ex (1617 / 2000) 101 ≤ (11980533939059 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_101
  have hlo := exp_neg_ge_of (q := (932831234785199 / 250000000000000 : ℝ)) (a := (31362326764763302637 / 50000000000000000000 : ℝ)) (lo := (95844271357 / 4000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (373132493752481 / 100000000000000 : ℝ)) (b := (62724653542244819287 / 100000000000000000000 : ℝ)) (hi := (11980533939059 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_102 : (1188548107633 / 50000000000000 : ℝ) ≤ ex (1617 / 2000) 102 ∧ ex (1617 / 2000) 102 ≤ (4754192438267 / 200000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_102
  have hlo := exp_neg_ge_of (q := (934822630204681 / 250000000000000 : ℝ)) (a := (1566555745459803879 / 2500000000000000000 : ℝ)) (lo := (1188548107633 / 50000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3739290519198047 / 1000000000000000 : ℝ)) (b := (31331114915567872989 / 50000000000000000000 : ℝ)) (hi := (4754192438267 / 200000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_103 : (11792098754917 / 500000000000000 : ℝ) ≤ ex (1617 / 2000) 103 ∧ ex (1617 / 2000) 103 ≤ (11792098774157 / 500000000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_103
  have hlo := exp_neg_ge_of (q := (468397298533203 / 125000000000000 : ℝ)) (a := (31300238173500876429 / 50000000000000000000 : ℝ)) (lo := (11792098754917 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (3747178386640481 / 1000000000000000 : ℝ)) (b := (15650119089942259929 / 25000000000000000000 : ℝ)) (hi := (11792098774157 / 500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

theorem exB_104 : (23400683602867 / 1000000000000000 : ℝ) ≤ ex (1617 / 2000) 104 ∧ ex (1617 / 2000) 104 ≤ (365635681893 / 15625000000000 : ℝ) := by
  have hl := PsiOmega.Num.log_bound_104
  have hlo := exp_neg_ge_of (q := (3754990043241167 / 1000000000000000 : ℝ)) (a := (31269689757874713921 / 50000000000000000000 : ℝ)) (lo := (23400683602867 / 1000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hhi := exp_neg_le_of (q := (375499004161177 / 100000000000000 : ℝ)) (b := (12507875905707767033 / 20000000000000000000 : ℝ)) (hi := (365635681893 / 15625000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold ex
  simp only [Nat.cast_ofNat]
  constructor
  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))
  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi

end PsiOmega.Locate

#print axioms PsiOmega.Locate.exB_104
