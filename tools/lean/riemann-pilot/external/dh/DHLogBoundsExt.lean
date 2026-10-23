import DHLogBounds

/-! # Generated (gen_logext.py): rational bounds for `Real.log n`, `122 ≤ n ≤ 209`

Chained upward from `PsiOmega.Num.log_bound_121` (`DHLogBounds`) by
`log n = log (n − 1) + log (1 + 1/(n − 1))` with `PsiOmega.Num.log_one_add_inv_bounds` (tail `≤ 10⁻²²`),
every bound rounded outward to the grid `10⁻³⁰`. Used by the zero-location certificates for the zeros
at heights `114`, `166`, `176` (`DHLocate2Base` … `DHLocate4Num`). -/

open Real Finset

namespace PsiOmega.Num

theorem log_bound_122 : (600502630536950903389624859531 / 125000000000000000000000000000 : ℝ) ≤ Real.log 122 ∧ Real.log 122 ≤ (4804021046371606894489121291681 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_121
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 121) (by norm_num) 5
  have e : Real.log (122 : ℝ) = Real.log (121 : ℝ) + Real.log (1 + ((121 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((121 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_123 : (4812184354934768164210386260371 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 123 ∧ Real.log 123 ≤ (2406092178505383915791254343141 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_122
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 122) (by norm_num) 5
  have e : Real.log (123 : ℝ) = Real.log (122 : ℝ) + Real.log (1 + ((122 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((122 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_124 : (2410140782583693766856003108499 / 500000000000000000000000000000 : ℝ) ≤ Real.log 124 ∧ Real.log 124 ≤ (482028156724338720108412865249 / 100000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_123
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 123) (by norm_num) 5
  have e : Real.log (124 : ℝ) = Real.log (123 : ℝ) + Real.log (1 + ((123 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((123 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_125 : (241415686843232589637532782421 / 50000000000000000000000000000 : ℝ) ≤ Real.log 125 ∧ Real.log 125 ≤ (120707843473516286503069452317 / 25000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_124
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 124) (by norm_num) 5
  have e : Real.log (125 : ℝ) = Real.log (124 : ℝ) + Real.log (1 + ((124 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((124 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_126 : (4836281906513828666261452986757 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 126 ∧ Real.log 126 ≤ (4836281908589828333633575439047 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_125
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 125) (by norm_num) 5
  have e : Real.log (126 : ℝ) = Real.log (125 : ℝ) + Real.log (1 + ((125 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((125 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_127 : (2422093543010470970997909227529 / 500000000000000000000000000000 : ℝ) ≤ Real.log 127 ∧ Real.log 127 ≤ (2422093544048470804683970457353 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_126
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 126) (by norm_num) 5
  have e : Real.log (127 : ℝ) = Real.log (126 : ℝ) + Real.log (1 + ((126 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((126 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_128 : (970406052696393566973800499387 / 200000000000000000000000000000 : ℝ) ≤ Real.log 128 ∧ Real.log 128 ≤ (4852030265557967502241124963331 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_127
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 127) (by norm_num) 5
  have e : Real.log (128 : ℝ) = Real.log (127 : ℝ) + Real.log (1 + ((127 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((127 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_129 : (4859812403924022783816465396433 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 129 ∧ Real.log 129 ≤ (4859812406000022451188587869021 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_128
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 128) (by norm_num) 5
  have e : Real.log (129 : ℝ) = Real.log (128 : ℝ) + Real.log (1 + ((128 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((128 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_130 : (4867534450017933089019856541897 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 130 ∧ Real.log 130 ≤ (4867534452093932756391979020171 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_129
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 129) (by norm_num) 5
  have e : Real.log (130 : ℝ) = Real.log (129 : ℝ) + Real.log (1 + ((129 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((129 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_131 : (4875197322763502213097801656341 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 131 ∧ Real.log 131 ≤ (15234991640123443376468512937 / 3125000000000000000000000000 : ℝ) := by
  have hprev := log_bound_130
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 130) (by norm_num) 5
  have e : Real.log (131 : ℝ) = Real.log (130 : ℝ) + Real.log (1 + ((130 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((130 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_132 : (2441400961074360761620015351269 / 500000000000000000000000000000 : ℝ) ≤ Real.log 132 ∧ Real.log 132 ≤ (4882801924224721190612153190841 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_131
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 131) (by norm_num) 5
  have e : Real.log (132 : ℝ) = Real.log (131 : ℝ) + Real.log (1 + ((131 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((131 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_133 : (4890349127784104434062757819663 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 133 ∧ Real.log 133 ≤ (2445174564930052050717440156193 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_132
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 132) (by norm_num) 5
  have e : Real.log (133 : ℝ) = Real.log (132 : ℝ) + Real.log (1 + ((132 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((132 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_134 : (612229974939157754754460220223 / 125000000000000000000000000000 : ℝ) ≤ Real.log 134 ∧ Real.log 134 ≤ (306114987599328856587987766161 / 62500000000000000000000000000 : ℝ) := by
  have hprev := log_bound_133
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 133) (by norm_num) 5
  have e : Real.log (134 : ℝ) = Real.log (133 : ℝ) + Real.log (1 + ((133 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((133 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_135 : (981054955600156023546974537523 / 200000000000000000000000000000 : ℝ) ≤ Real.log 135 ∧ Real.log 135 ≤ (981054956015355957021399037631 / 200000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_134
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 134) (by norm_num) 5
  have e : Real.log (135 : ℝ) = Real.log (134 : ℝ) + Real.log (1 + ((134 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((134 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_136 : (2456327442649201338724804312777 / 500000000000000000000000000000 : ℝ) ≤ Real.log 136 ∧ Real.log 136 ≤ (98253097747488046896434622591 / 20000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_135
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 135) (by norm_num) 5
  have e : Real.log (136 : ℝ) = Real.log (135 : ℝ) + Real.log (1 + ((135 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((135 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_137 : (1229995231347618896065891942749 / 250000000000000000000000000000 : ℝ) ≤ Real.log 137 ∧ Real.log 137 ≤ (4919980927466475251635690278179 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_136
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 136) (by norm_num) 5
  have e : Real.log (137 : ℝ) = Real.log (136 : ℝ) + Real.log (1 + ((136 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((136 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_138 : (4927253684719555360567607832939 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 138 ∧ Real.log 138 ≤ (4927253686795555027939730343063 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_137
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 137) (by norm_num) 5
  have e : Real.log (138 : ℝ) = Real.log (137 : ℝ) + Real.log (1 + ((137 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((137 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_139 : (154202310396657575816786330043 / 31250000000000000000000000000 : ℝ) ≤ Real.log 139 ∧ Real.log 139 ≤ (616809241846130261688660634277 / 125000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_138
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 138) (by norm_num) 5
  have e : Real.log (139 : ℝ) = Real.log (138 : ℝ) + Real.log (1 + ((138 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((138 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_140 : (2470821211085827483744476980929 / 500000000000000000000000000000 : ℝ) ≤ Real.log 140 ∧ Real.log 140 ≤ (4941642424247654634861076477207 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_139
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 139) (by norm_num) 5
  have e : Real.log (140 : ℝ) = Real.log (139 : ℝ) + Real.log (1 + ((139 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((139 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_141 : (1237189972485129736791143387189 / 250000000000000000000000000000 : ℝ) ≤ Real.log 141 ∧ Real.log 141 ≤ (618594986502064826817087008303 / 125000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_140
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 140) (by norm_num) 5
  have e : Real.log (141 : ℝ) = Real.log (140 : ℝ) + Real.log (1 + ((140 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((140 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_142 : (4955827057163611399695064295837 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 142 ∧ Real.log 142 ≤ (4955827059239611067067186815651 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_141
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 141) (by norm_num) 5
  have e : Real.log (142 : ℝ) = Real.log (141 : ℝ) + Real.log (1 + ((141 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((141 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_143 : (992568925964451589812761732243 / 200000000000000000000000000000 : ℝ) ≤ Real.log 143 ∧ Real.log 143 ≤ (992568926379651523287186236603 / 200000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_142
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 142) (by norm_num) 5
  have e : Real.log (143 : ℝ) = Real.log (142 : ℝ) + Real.log (1 + ((142 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((142 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_144 : (993962659827670257881559320239 / 200000000000000000000000000000 : ℝ) ≤ Real.log 144 ∧ Real.log 144 ≤ (2484906650607175478389959562417 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_143
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 143) (by norm_num) 5
  have e : Real.log (144 : ℝ) = Real.log (143 : ℝ) + Real.log (1 + ((143 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((143 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_145 : (99534674839658501414648180139 / 20000000000000000000000000000 : ℝ) ≤ Real.log 145 ∧ Real.log 145 ≤ (4976733744058924738104531532293 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_144
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 144) (by norm_num) 5
  have e : Real.log (145 : ℝ) = Real.log (144 : ℝ) + Real.log (1 + ((144 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((144 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_146 : (996721324254137421491543724023 / 200000000000000000000000000000 : ℝ) ≤ Real.log 146 ∧ Real.log 146 ≤ (4983606623346686774829841147037 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_145
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 145) (by norm_num) 5
  have e : Real.log (146 : ℝ) = Real.log (145 : ℝ) + Real.log (1 + ((145 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((145 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_147 : (2495216293170543485277164182447 / 500000000000000000000000000000 : ℝ) ≤ Real.log 147 ∧ Real.log 147 ≤ (31190203677606791487040318083 / 6250000000000000000000000000 : ℝ) := by
  have hprev := log_bound_146
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 146) (by norm_num) 5
  have e : Real.log (147 : ℝ) = Real.log (146 : ℝ) + Real.log (1 + ((146 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((146 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_148 : (4997212273326465732150937554909 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 148 ∧ Real.log 148 ≤ (2498606137701232699761530042327 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_147
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 147) (by norm_num) 5
  have e : Real.log (148 : ℝ) = Real.log (147 : ℝ) + Real.log (1 + ((147 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((147 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_149 : (100078926110156196198816118319 / 20000000000000000000000000000 : ℝ) ≤ Real.log 149 ∧ Real.log 149 ≤ (5003946307583809477312928446957 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_148
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 148) (by norm_num) 5
  have e : Real.log (149 : ℝ) = Real.log (148 : ℝ) + Real.log (1 + ((148 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((148 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_150 : (1252658823414651604740593416393 / 250000000000000000000000000000 : ℝ) ≤ Real.log 150 ∧ Real.log 150 ≤ (5010635295734606086334496197751 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_149
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 149) (by norm_num) 5
  have e : Real.log (150 : ℝ) = Real.log (149 : ℝ) + Real.log (1 + ((149 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((149 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_151 : (501727983637727499774460298319 / 100000000000000000000000000000 : ℝ) ≤ Real.log 151 ∧ Real.log 151 ≤ (250863991922663733255841206443 / 50000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_150
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 150) (by norm_num) 4
  have e : Real.log (151 : ℝ) = Real.log (150 : ℝ) + Real.log (1 + ((150 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((150 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_152 : (200955220816345082288363206277 / 40000000000000000000000000000 : ℝ) ≤ Real.log 152 ∧ Real.log 152 ≤ (5023880522484626724581394210159 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_151
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 151) (by norm_num) 4
  have e : Real.log (152 : ℝ) = Real.log (151 : ℝ) + Real.log (1 + ((151 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((151 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_153 : (503043792095478613198837172283 / 100000000000000000000000000000 : ℝ) ≤ Real.log 153 ∧ Real.log 153 ≤ (2515218961515392899680386671093 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_152
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 152) (by norm_num) 4
  have e : Real.log (153 : ℝ) = Real.log (152 : ℝ) + Real.log (1 + ((152 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((152 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_154 : (5036952601975979827532865900249 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 154 ∧ Real.log 154 ≤ (5036952604051979494905350083321 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_153
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 153) (by norm_num) 4
  have e : Real.log (154 : ℝ) = Real.log (153 : ℝ) + Real.log (1 + ((153 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((153 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_155 : (5043425116481597289478252462187 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 155 ∧ Real.log 155 ≤ (5043425118557596956850814522083 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_154
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 154) (by norm_num) 4
  have e : Real.log (155 : ℝ) = Real.log (154 : ℝ) + Real.log (1 + ((154 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((154 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_156 : (5049856006811887715231517560983 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 156 ∧ Real.log 156 ≤ (2524928004443943691302076552287 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_155
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 155) (by norm_num) 4
  have e : Real.log (156 : ℝ) = Real.log (155 : ℝ) + Real.log (1 + ((155 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((155 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_157 : (5056245804910658726372758168863 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 157 ∧ Real.log 157 ≤ (316015362936666149609091442291 / 62500000000000000000000000000 : ℝ) := by
  have hprev := log_bound_156
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 156) (by norm_num) 4
  have e : Real.log (157 : ℝ) = Real.log (156 : ℝ) + Real.log (1 + ((156 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((156 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_158 : (2531297516294658736269241658833 / 500000000000000000000000000000 : ℝ) ≤ Real.log 158 ∧ Real.log 158 ≤ (1265648758666329284977813431293 / 250000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_157
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 157) (by norm_num) 4
  have e : Real.log (158 : ℝ) = Real.log (157 : ℝ) + Real.log (1 + ((157 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((157 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_159 : (1267226050445645548622003288979 / 250000000000000000000000000000 : ℝ) ≤ Real.log 159 ∧ Real.log 159 ≤ (633613025482322732732605679549 / 125000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_158
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 158) (by norm_num) 4
  have e : Real.log (159 : ℝ) = Real.log (158 : ℝ) + Real.log (1 + ((158 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((158 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_160 : (101503476295923551812704244481 / 20000000000000000000000000000 : ℝ) ≤ Real.log 160 ∧ Real.log 160 ≤ (5075173816872177258008102972511 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_159
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 159) (by norm_num) 4
  have e : Real.log (160 : ℝ) = Real.log (159 : ℝ) + Real.log (1 + ((159 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((159 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_161 : (5081404364546813664860391717693 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 161 ∧ Real.log 161 ≤ (2540702183311406666116668868043 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_160
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 160) (by norm_num) 4
  have e : Real.log (161 : ℝ) = Real.log (160 : ℝ) + Real.log (1 + ((160 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((160 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_162 : (5087596334794734743946493404369 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 162 ∧ Real.log 162 ≤ (5087596336870734411319491687823 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_161
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 161) (by norm_num) 4
  have e : Real.log (162 : ℝ) = Real.log (161 : ℝ) + Real.log (1 + ((161 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((161 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_163 : (5093750200369113003013207207949 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 163 ∧ Real.log 163 ≤ (2546875101222556335193127466009 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_162
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 162) (by norm_num) 4
  have e : Real.log (163 : ℝ) = Real.log (162 : ℝ) + Real.log (1 + ((162 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((162 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_164 : (1019973285477309818329899451897 / 200000000000000000000000000000 : ℝ) ≤ Real.log 164 ∧ Real.log 164 ≤ (2549933214731274379511295884151 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_163
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 163) (by norm_num) 4
  have e : Real.log (164 : ℝ) = Real.log (163 : ℝ) + Real.log (1 + ((163 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((163 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_165 : (638243184182866409875776608867 / 125000000000000000000000000000 : ℝ) ≤ Real.log 165 ∧ Real.log 165 ≤ (5105945475538930946379351666209 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_164
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 164) (by norm_num) 4
  have e : Real.log (165 : ℝ) = Real.log (164 : ℝ) + Real.log (1 + ((164 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((164 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_166 : (5111987787918893901840964408077 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 166 ∧ Real.log 166 ≤ (5111987789994893569214145138869 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_165
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 165) (by norm_num) 4
  have e : Real.log (166 : ℝ) = Real.log (165 : ℝ) + Real.log (1 + ((165 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((165 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_167 : (1279498452994776444052001606619 / 250000000000000000000000000000 : ℝ) ≤ Real.log 167 ∧ Real.log 167 ≤ (5117993814055105443581226879699 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_166
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 166) (by norm_num) 4
  have e : Real.log (167 : ℝ) = Real.log (166 : ℝ) + Real.log (1 + ((166 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((166 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_168 : (5123963978965609593700545812439 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 168 ∧ Real.log 168 ≤ (1024792796208321852214760780803 / 200000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_167
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 167) (by norm_num) 4
  have e : Real.log (168 : ℝ) = Real.log (167 : ℝ) + Real.log (1 + ((167 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((167 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_169 : (256494935724271207052761119347 / 50000000000000000000000000000 : ℝ) ≤ Real.log 169 ∧ Real.log 169 ≤ (5129898716561423808428516153577 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_168
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 168) (by norm_num) 4
  have e : Real.log (169 : ℝ) = Real.log (168 : ℝ) + Real.log (1 + ((168 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((168 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_170 : (102715968732252248664315396361 / 20000000000000000000000000000 : ℝ) ≤ Real.log 170 ∧ Real.log 170 ≤ (2567899219344306050294548704793 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_169
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 169) (by norm_num) 4
  have e : Real.log (170 : ℝ) = Real.log (169 : ℝ) + Real.log (1 + ((169 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((169 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_171 : (321353972254063156984234880419 / 62500000000000000000000000000 : ℝ) ≤ Real.log 171 ∧ Real.log 171 ≤ (5141663558141010179121117758977 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_170
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 170) (by norm_num) 4
  have e : Real.log (171 : ℝ) = Real.log (170 : ℝ) + Real.log (1 + ((170 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((170 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_172 : (1286873619093950927813885888867 / 250000000000000000000000000000 : ℝ) ≤ Real.log 172 ∧ Real.log 172 ≤ (2573747239225901689314466831837 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_171
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 171) (by norm_num) 4
  have e : Real.log (172 : ℝ) = Real.log (171 : ℝ) + Real.log (1 + ((171 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((171 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_173 : (1030658318812025923176346795657 / 200000000000000000000000000000 : ℝ) ≤ Real.log 173 ∧ Real.log 173 ≤ (1288322899034032320813788242697 / 250000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_172
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 172) (by norm_num) 4
  have e : Real.log (173 : ℝ) = Real.log (172 : ℝ) + Real.log (1 + ((172 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((172 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_174 : (2579527649388439848471989966959 / 500000000000000000000000000000 : ℝ) ≤ Real.log 174 ∧ Real.log 174 ≤ (5159055300852879364317426346477 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_173
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 173) (by norm_num) 4
  have e : Real.log (174 : ℝ) = Real.log (173 : ℝ) + Real.log (1 + ((173 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((173 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_175 : (5164785973485864723255099059983 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 175 ∧ Real.log 175 ≤ (5164785975561864390628571510369 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_174
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 174) (by norm_num) 4
  have e : Real.log (175 : ℝ) = Real.log (174 : ℝ) + Real.log (1 + ((174 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((174 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_176 : (80788812415632850791860890091 / 15625000000000000000000000000 : ℝ) ≤ Real.log 176 ∧ Real.log 176 ≤ (2585241998338251059026297074397 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_175
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 175) (by norm_num) 4
  have e : Real.log (176 : ℝ) = Real.log (175 : ℝ) + Real.log (1 + ((175 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((175 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_177 : (5176149732136179810959517901601 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 177 ∧ Real.log 177 ≤ (323509358388261217395814911513 / 62500000000000000000000000000 : ℝ) := by
  have hprev := log_bound_176
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 176) (by norm_num) 4
  have e : Real.log (177 : ℝ) = Real.log (176 : ℝ) + Real.log (1 + ((176 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((176 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_178 : (5181783549854435816683267471467 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 178 ∧ Real.log 178 ≤ (129544588798260887101420262217 / 25000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_177
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 177) (by norm_num) 4
  have e : Real.log (178 : ℝ) = Real.log (177 : ℝ) + Real.log (1 + ((177 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((177 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_179 : (5187385805403105665126021880097 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 179 ∧ Real.log 179 ≤ (5187385807479105332499586130707 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_178
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 178) (by norm_num) 4
  have e : Real.log (179 : ℝ) = Real.log (178 : ℝ) + Real.log (1 + ((178 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((178 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_180 : (519295685045256104517392925649 / 100000000000000000000000000000 : ℝ) ≤ Real.log 180 ∧ Real.log 180 ≤ (2596478426264280356273756849643 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_179
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 179) (by norm_num) 4
  have e : Real.log (180 : ℝ) = Real.log (179 : ℝ) + Real.log (1 + ((179 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((179 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_181 : (5198497030828176415787300110983 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 181 ∧ Real.log 181 ≤ (5198497032904176083160903761177 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_180
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 180) (by norm_num) 4
  have e : Real.log (181 : ℝ) = Real.log (180 : ℝ) + Real.log (1 + ((180 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((180 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_182 : (5204006686639146019524283348187 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 182 ∧ Real.log 182 ≤ (5204006688715145686897905274067 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_181
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 181) (by norm_num) 4
  have e : Real.log (182 : ℝ) = Real.log (181 : ℝ) + Real.log (1 + ((181 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((181 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_183 : (5209486152403771609094843449413 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 183 ∧ Real.log 183 ≤ (2604743077239885638234241384607 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_182
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 182) (by norm_num) 4
  have e : Real.log (183 : ℝ) = Real.log (182 : ℝ) + Real.log (1 + ((182 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((182 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_184 : (5214935757171336288006656465343 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 184 ∧ Real.log 184 ≤ (2607467879623667977690156172159 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_183
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 183) (by norm_num) 4
  have e : Real.log (184 : ℝ) = Real.log (183 : ℝ) + Real.log (1 + ((183 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((183 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_185 : (261017791232033774395853026067 / 50000000000000000000000000000 : ℝ) ≤ Real.log 185 ∧ Real.log 185 ≤ (652544478339584394411341521127 / 125000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_184
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 184) (by norm_num) 4
  have e : Real.log (185 : ℝ) = Real.log (184 : ℝ) + Real.log (1 + ((184 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((184 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_186 : (2612873336637775957844922765563 / 500000000000000000000000000000 : ℝ) ≤ Real.log 186 ∧ Real.log 186 ≤ (1045149335070310316612706439747 / 200000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_185
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 185) (by norm_num) 4
  have e : Real.log (186 : ℝ) = Real.log (185 : ℝ) + Real.log (1 + ((185 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((185 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_187 : (653888577052117161657460056749 / 125000000000000000000000000000 : ℝ) ≤ Real.log 187 ∧ Real.log 187 ≤ (5231108618492936960633381432063 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_186
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 186) (by norm_num) 4
  have e : Real.log (187 : ℝ) = Real.log (186 : ℝ) + Real.log (1 + ((186 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((186 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_188 : (5236441962392299874603615655507 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 188 ∧ Real.log 188 ≤ (523644196446829954197733027161 / 100000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_187
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 187) (by norm_num) 4
  have e : Real.log (188 : ℝ) = Real.log (187 : ℝ) + Real.log (1 + ((187 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((187 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_189 : (327609188413874565514955484533 / 62500000000000000000000000000 : ℝ) ≤ Real.log 189 ∧ Real.log 189 ≤ (5241747016697992715613015369157 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_188
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 188) (by norm_num) 4
  have e : Real.log (189 : ℝ) = Real.log (188 : ℝ) + Real.log (1 + ((188 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((188 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_190 : (2623512035861418406487608403781 / 500000000000000000000000000000 : ℝ) ≤ Real.log 190 ∧ Real.log 190 ≤ (5247024073798836480348956820151 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_189
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 189) (by norm_num) 4
  have e : Real.log (190 : ℝ) = Real.log (189 : ℝ) + Real.log (1 + ((189 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((189 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_191 : (2626136713804490270899073279793 / 500000000000000000000000000000 : ℝ) ≤ Real.log 191 ∧ Real.log 191 ≤ (1050454685936996041834379678929 / 200000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_190
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 190) (by norm_num) 4
  have e : Real.log (191 : ℝ) = Real.log (190 : ℝ) + Real.log (1 + ((190 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((190 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_192 : (5257495371590132216846833319911 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 192 ∧ Real.log 192 ≤ (8214836521353331069094681927 / 1562500000000000000000000000 : ℝ) := by
  have hprev := log_bound_191
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 191) (by norm_num) 4
  have e : Real.log (192 : ℝ) = Real.log (191 : ℝ) + Real.log (1 + ((191 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((191 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_193 : (657836273558404527600390651483 / 125000000000000000000000000000 : ℝ) ≤ Real.log 193 ∧ Real.log 193 ≤ (526269019054323588817689908707 / 100000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_192
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 192) (by norm_num) 4
  have e : Real.log (193 : ℝ) = Real.log (192 : ℝ) + Real.log (1 + ((192 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((192 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_194 : (1053571631725135760096429352073 / 200000000000000000000000000000 : ℝ) ≤ Real.log 194 ∧ Real.log 194 ≤ (131696454017541961696398272677 / 25000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_193
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 193) (by norm_num) 4
  have e : Real.log (194 : ℝ) = Real.log (193 : ℝ) + Real.log (1 + ((193 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((193 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_195 : (329562472382881091937355246211 / 62500000000000000000000000000 : ℝ) ≤ Real.log 195 ∧ Real.log 195 ≤ (5272999560202097138371477891969 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_194
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 194) (by norm_num) 4
  have e : Real.log (195 : ℝ) = Real.log (194 : ℝ) + Real.log (1 + ((194 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((194 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_196 : (5278114658792867897993360617067 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 196 ∧ Real.log 196 ≤ (5278114660868867565367163933243 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_195
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 195) (by norm_num) 4
  have e : Real.log (196 : ℝ) = Real.log (195 : ℝ) + Real.log (1 + ((195 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((195 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_197 : (5283203728300339175727987222723 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 197 ∧ Real.log 197 ≤ (2641601865188169421550899741121 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_196
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 196) (by norm_num) 4
  have e : Real.log (197 : ℝ) = Real.log (196 : ℝ) + Real.log (1 + ((196 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((196 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_198 : (5288267030256885905217855117501 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 198 ∧ Real.log 198 ≤ (211530681293315422903667036839 / 40000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_197
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 197) (by norm_num) 4
  have e : Real.log (198 : ℝ) = Real.log (197 : ℝ) + Real.log (1 + ((197 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((197 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_199 : (5293304824286843064358309328959 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 199 ∧ Real.log 199 ≤ (66166310329535534146651728709 / 12500000000000000000000000000 : ℝ) := by
  have hprev := log_bound_198
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 198) (by norm_num) 4
  have e : Real.log (199 : ℝ) = Real.log (198 : ℝ) + Real.log (1 + ((198 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((198 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_200 : (662289670763798418300175275111 / 125000000000000000000000000000 : ℝ) ≤ Real.log 200 ∧ Real.log 200 ≤ (66228967102329837672190487149 / 12500000000000000000000000000 : ℝ) := by
  have hprev := log_bound_199
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 199) (by norm_num) 4
  have e : Real.log (200 : ℝ) = Real.log (199 : ℝ) + Real.log (1 + ((199 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((199 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_201 : (5303304907621426420013503574469 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 201 ∧ Real.log 201 ≤ (165728278428044565230854618919 / 31250000000000000000000000000 : ℝ) := by
  have hprev := log_bound_200
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 200) (by norm_num) 4
  have e : Real.log (201 : ℝ) = Real.log (200 : ℝ) + Real.log (1 + ((200 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((200 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_202 : (5308267696963555429249615936971 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 202 ∧ Real.log 202 ≤ (2654133849519777548311733650579 / 500000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_201
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 201) (by norm_num) 4
  have e : Real.log (202 : ℝ) = Real.log (201 : ℝ) + Real.log (1 + ((201 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((201 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_203 : (132830149465103450030920239159 / 25000000000000000000000000000 : ℝ) ≤ Real.log 203 ∧ Real.log 203 ≤ (664150747585017208576333469119 / 125000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_202
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 202) (by norm_num) 4
  have e : Real.log (203 : ℝ) = Real.log (202 : ℝ) + Real.log (1 + ((202 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((202 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_204 : (664764999175820882428428520387 / 125000000000000000000000000000 : ℝ) ≤ Real.log 204 ∧ Real.log 204 ≤ (1329529998870641681700323219057 / 250000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_203
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 203) (by norm_num) 4
  have e : Real.log (204 : ℝ) = Real.log (203 : ℝ) + Real.log (1 + ((203 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((203 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_205 : (2661504989350379423707853038887 / 500000000000000000000000000000 : ℝ) ≤ Real.log 205 ∧ Real.log 205 ≤ (5323009980776758514789577035769 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_204
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 204) (by norm_num) 4
  have e : Real.log (205 : ℝ) = Real.log (204 : ℝ) + Real.log (1 + ((204 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((204 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_206 : (5327876168351931749134017143953 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 206 ∧ Real.log 206 ≤ (332992260651745713531743379911 / 62500000000000000000000000000 : ℝ) := by
  have hprev := log_bound_205
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 205) (by norm_num) 4
  have e : Real.log (206 : ℝ) = Real.log (205 : ℝ) + Real.log (1 + ((205 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((205 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_207 : (1066543758565543948509085075483 / 200000000000000000000000000000 : ℝ) ≤ Real.log 207 ∧ Real.log 207 ≤ (5332718794903719409919308033173 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_206
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 206) (by norm_num) 4
  have e : Real.log (207 : ℝ) = Real.log (206 : ℝ) + Real.log (1 + ((206 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((206 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_208 : (5337538079263668642670597390523 / 1000000000000000000000000000000 : ℝ) ≤ Real.log 208 ∧ Real.log 208 ≤ (5337538081339668310044485523999 / 1000000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_207
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 207) (by norm_num) 4
  have e : Real.log (208 : ℝ) = Real.log (207 : ℝ) + Real.log (1 + ((207 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((207 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

theorem log_bound_209 : (1335583562881790418254787972529 / 250000000000000000000000000000 : ℝ) ≤ Real.log 209 ∧ Real.log 209 ≤ (1335583563400790335098261317337 / 250000000000000000000000000000 : ℝ) := by
  have hprev := log_bound_208
  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := 208) (by norm_num) 4
  have e : Real.log (209 : ℝ) = Real.log (208 : ℝ) + Real.log (1 + ((208 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set y := Real.log (1 + ((208 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]

end PsiOmega.Num

#print axioms PsiOmega.Num.log_bound_209
