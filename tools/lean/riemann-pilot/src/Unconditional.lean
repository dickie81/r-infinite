import Mathlib
import Concave
import Saturation

/-! # Saturation without RH: verified zeros, a zero-counting bound, and monotonicity

`Saturation.lean` proved the pinning step from the explicit formula with every zero on the line,
i.e. from RH. Here RH is replaced by inputs that are theorems, or a numerically observed property
of the ground state.
* The unconditional explicit formula `Q = Σ_ρ ĝ(t_ρ)²`, summed over all nontrivial zeros with
  multiplicity (named input `hQ`).
* Verified RH up to height `H` (named input `hRH`: zeros with `|Re t| ≤ H` are real; Platt–Trudgian,
  `H = 3·10¹²`).
* The critical strip, `|Im t| ≤ ½` (named input `hstrip`).
* A zero-counting bound, giving `Σ_{|Re t| > H} (Re t)⁻² ≤ S` (named input `hS`).
* The ground state is even, `≥ 0` and non-increasing on `[0, a]`. That is observed numerically at
  every support tested; it is not proved.

Proved here:
* `norm_ghatC_le_of_antitone`: `‖ĝ(z)‖ ≤ 2 g(0) cosh(a|Im z|)/‖z‖`, by layer cake.
* `sq_le_of_explicit_tail`: every zero `t_j` with `|Re t_j| ≤ H` satisfies
  `‖ĝ(t_j)‖² ≤ Q + B² S`, where `B` bounds `‖ĝ(t)‖·|Re t|` above `H`.
* `ghatC_im_eq_zero`: `ĝ` is real on the real line for even `g`.
* `pinned_unconditional`: combining these with the slope lemma of `Saturation.lean`, `ĝ` has a zero
  within `√(Q + B²S)/m` of every verified zero near which `|ĝ'| ≥ m`, where
  `B = 2 g(0) cosh(a/2)`. -/

open Real MeasureTheory Complex Set

noncomputable section

namespace Pilot1ca


theorem sq_norm_of_im_zero {w : ℂ} (h : w.im = 0) : ‖w‖ ^ 2 = w.re ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, h]; ring

theorem neg_sq_norm_le_re_sq (w : ℂ) : -(‖w‖ ^ 2) ≤ (w ^ 2).re := by
  rw [Complex.sq_norm, Complex.normSq_apply, sq, mul_re]; nlinarith [sq_nonneg w.im]

theorem sq_norm_le_of_le_div {w : ℂ} {B x : ℝ} (h : ‖w‖ ≤ B / |x|) :
    ‖w‖ ^ 2 ≤ B ^ 2 * (1 / x ^ 2) := by
  have h0 : 0 ≤ B / |x| := (norm_nonneg _).trans h
  calc ‖w‖ ^ 2 ≤ (B / |x|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = B ^ 2 * (1 / x ^ 2) := by rw [div_pow, sq_abs]; ring

theorem sq_le_of_explicit_tail {ι : Type*} {t : ι → ℂ} {F : ℂ → ℂ} {Q H B S : ℝ}
    (hsum : Summable fun i => F (t i) ^ 2) (hQ : (Q : ℂ) = ∑' i, F (t i) ^ 2)
    (hRH : ∀ i, |(t i).re| ≤ H → (t i).im = 0) (hreal : ∀ i, (t i).im = 0 → (F (t i)).im = 0)
    (hdecay : ∀ i, H < |(t i).re| → ‖F (t i)‖ ≤ B / |(t i).re|)
    (hS : Summable fun i => if H < |(t i).re| then 1 / (t i).re ^ 2 else 0)
    (hSle : (∑' i, if H < |(t i).re| then 1 / (t i).re ^ 2 else 0) ≤ S)
    (j : ι) (hj : |(t j).re| ≤ H) : ‖F (t j)‖ ^ 2 ≤ Q + B ^ 2 * S := by
  classical
  set s : ι → ℝ := fun i => if H < |(t i).re| then 1 / (t i).re ^ 2 else 0 with hs
  set r : ι → ℝ := fun i => (F (t i) ^ 2).re with hr
  have hrs : Summable r := Complex.reCLM.summable hsum
  have hQr : Q = ∑' i, r i := by
    have := congrArg Complex.re hQ
    simp only [ofReal_re] at this
    rw [this, Complex.re_tsum hsum]
  set l : ι → ℝ := fun i => (if i = j then ‖F (t j)‖ ^ 2 else 0) + (-(B ^ 2)) * s i with hl
  have hle : ∀ i, l i ≤ r i := by
    intro i
    simp only [hl, hr, hs]
    by_cases hij : i = j
    · subst hij
      have him := hreal i (hRH i hj)
      have e : (F (t i) ^ 2).re = (F (t i)).re ^ 2 := by rw [sq, mul_re, him]; ring
      simp only [not_lt.2 hj, ↓reduceIte, mul_zero, add_zero]
      rw [e, sq_norm_of_im_zero him]
    · simp only [hij, ↓reduceIte, zero_add]
      by_cases hh : H < |(t i).re|
      · simp only [hh, ↓reduceIte]
        have := sq_norm_le_of_le_div (hdecay i hh)
        have := neg_sq_norm_le_re_sq (F (t i))
        linarith
      · simp only [hh, ↓reduceIte, mul_zero]
        have him := hreal i (hRH i (not_lt.1 hh))
        rw [sq, mul_re, him, mul_zero, sub_zero]
        exact mul_self_nonneg _
  have hls : Summable l := by
    refine Summable.add ?_ (hS.mul_left _)
    exact summable_of_ne_finset_zero (s := {j}) (fun i hi => by
      simp only [Finset.mem_singleton] at hi; simp [hi])
  have htl : ∑' i, l i = ‖F (t j)‖ ^ 2 + (-(B ^ 2)) * ∑' i, s i := by
    rw [Summable.tsum_add (summable_of_ne_finset_zero (s := {j}) (fun i hi => by
      simp only [Finset.mem_singleton] at hi; simp [hi])) (hS.mul_left _), tsum_ite_eq, tsum_mul_left]
  have := hls.tsum_le_tsum hle hrs
  rw [htl, ← hQr] at this
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hSle hB2]



theorem norm_sin_le_cosh (w : ℂ) : ‖Complex.sin w‖ ≤ Real.cosh w.im := by
  have h := two_sin w
  have e1 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by rw [Complex.norm_exp]; simp
  have e2 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by rw [Complex.norm_exp]; simp
  have : ‖(2 : ℂ) * Complex.sin w‖ ≤ Real.exp w.im + Real.exp (-w.im) := by
    rw [h, norm_mul, norm_I, mul_one]
    calc ‖Complex.exp (-w * I) - Complex.exp (w * I)‖
        ≤ ‖Complex.exp (-w * I)‖ + ‖Complex.exp (w * I)‖ := norm_sub_le _ _
      _ = _ := by rw [e1, e2]
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by simp] at this
  rw [Real.cosh_eq]; linarith

/-- The interval integral agrees off two points. -/
theorem intervalIntegral_congr_off_two {f f' : ℝ → ℂ} {p q c d : ℝ}
    (h : ∀ x ∈ Ioc p q, x ≠ c → x ≠ d → f x = f' x) (hpq : p ≤ q) :
    ∫ x in p..q, f x = ∫ x in p..q, f' x := by
  apply intervalIntegral.integral_congr_ae
  have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by rw [ae_iff]; simp
  have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ d := by rw [ae_iff]; simp
  filter_upwards [h1, h2] with x hx1 hx2 hmem
  rw [uIoc_of_le hpq] at hmem
  exact h x hmem hx1 hx2

/-- **Decay of `ĝ` for even, non-increasing profiles.** If `g` is even and non-increasing and
`≥ 0` on `[0, a]`, then `‖ĝ(z)‖ ≤ 2 g(0) cosh(a |Im z|)/‖z‖`. Layer cake: `g = ∫₀^{g(0)} 1[λ < g] dλ`.
Each level set is a symmetric interval `(−r, r)` (up to its endpoints), whose transform is
`2 sin(zr)/z`, with `|sin(zr)| ≤ cosh(r Im z)`. -/
theorem norm_ghatC_le_of_antitone {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hev : ∀ u, g (-u) = g u)
    (hmono : AntitoneOn g (Icc 0 a)) (hnn : ∀ u ∈ Icc 0 a, 0 ≤ g u) {z : ℂ} (hz : z ≠ 0) :
    ‖ghatC g a z‖ ≤ 2 * g 0 * Real.cosh (a * |z.im|) / ‖z‖ := by
  set cl : ℝ → ℝ := fun s => max 0 (min s a) with hcl
  have hclm : ∀ s, cl s ∈ Icc 0 a := fun s => ⟨le_max_left _ _, max_le ha.le (min_le_right _ _)⟩
  set gt : ℝ → ℝ := fun s => g (cl s) with hgt
  have hgtm : Antitone gt := fun x y hxy =>
    hmono (hclm x) (hclm y) (max_le_max le_rfl (min_le_min hxy le_rfl))
  set M := g 0
  have h0m : (0 : ℝ) ∈ Icc 0 a := ⟨le_rfl, ha.le⟩
  have hgtM : ∀ s, gt s ≤ M := fun s => hmono h0m (hclm s) (hclm s).1
  have hgt0 : ∀ s, 0 ≤ gt s := fun s => hnn _ (hclm s)
  have hM0 : 0 ≤ M := hnn 0 h0m
  set gc : ℝ → ℝ := fun u => gt |u| with hgc
  have hgc_meas : Measurable gc := hgtm.measurable.comp measurable_id.abs
  -- `ĝ` with `g` replaced by `gc` (equal on `[−a, a]`)
  have hcongr : ghatC g a z = ∫ u in (-a)..a, (gc u : ℂ) * Complex.exp (I * z * u) := by
    unfold ghatC
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by linarith)] at hu
    have hua : |u| ≤ a := abs_le.2 ⟨hu.1, hu.2⟩
    simp only [hgc, hgt, hcl]
    rw [min_eq_left hua, max_eq_right (abs_nonneg u)]
    congr 2
    rcases le_or_gt 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, hev]
  rw [hcongr]
  have hL := layer_fubini (E := ℂ) (by linarith : -a ≤ a) hgc_meas (fun u => hgt0 |u|)
    (fun u => hgtM |u|) (w := fun u : ℝ => Complex.exp (I * z * u)) (by fun_prop)
    (C := Real.exp (‖z‖ * a)) (fun u hu => by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.2
      have e : (I * z * (u : ℂ)).re = -(z.im * u) := by simp [mul_re]
      rw [e]
      calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
        _ = |z.im| * |u| := abs_mul _ _
        _ ≤ ‖z‖ * a := mul_le_mul (abs_im_le_norm z) (abs_le.2 ⟨hu.1.le, hu.2⟩) (abs_nonneg _)
            (norm_nonneg _))
  simp only [Complex.real_smul] at hL
  rw [hL]
  set F : ℝ → ℝ → ℂ := fun u l => (Iio (gc u)).indicator (fun _ => Complex.exp (I * z * u)) l with hF
  -- each layer is `2 sin(zr)/z`, of norm at most `2 cosh(a |Im z|)/‖z‖`
  have hbound : ∀ l ∈ Ioc (0 : ℝ) M,
      ‖∫ u in (-a)..a, F u l‖ ≤ 2 * Real.cosh (a * |z.im|) / ‖z‖ := by
    intro l hl
    set T := {s ∈ Icc 0 a | l < gt s} with hT
    have hpos : 0 ≤ 2 * Real.cosh (a * |z.im|) / ‖z‖ := by positivity
    by_cases hTe : T.Nonempty
    · have hbdd : BddAbove T := ⟨a, fun s hs => hs.1.2⟩
      set r := sSup T with hr
      have hr0 : 0 ≤ r := le_csSup_of_le hbdd hTe.some_mem hTe.some_mem.1.1
      have hra : r ≤ a := csSup_le hTe fun s hs => hs.1.2
      have hc : ∫ u in (-a)..a, F u l = ∫ u in (-a)..a, (Ioo (-r) r).indicator
          (fun u : ℝ => Complex.exp (I * z * u)) u := by
        apply intervalIntegral_congr_off_two (c := r) (d := -r) _ (by linarith)
        intro u hu h1 h2
        have hua : |u| ∈ Icc 0 a := ⟨abs_nonneg u, abs_le.2 ⟨hu.1.le, hu.2⟩⟩
        simp only [hF, Set.indicator, mem_Iio, mem_Ioo, hgc]
        by_cases hin : |u| < r
        · obtain ⟨s, hs, hus⟩ := exists_lt_of_lt_csSup hTe hin
          have : l < gt |u| := hs.2.trans_le (hgtm hus.le)
          have hin' : -r < u ∧ u < r := abs_lt.1 hin
          simp [this, hin']
        · have hgt' : r < |u| := by
            rcases lt_or_gt_of_ne (show |u| ≠ r from fun h => by
              rcases abs_eq (hr0) |>.1 h with h' | h'
              · exact h1 h'
              · exact h2 h') with h | h
            · exact absurd h hin
            · exact h
          have hnot : ¬ l < gt |u| := fun h => (not_le.2 hgt') (le_csSup hbdd ⟨hua, h⟩)
          have hout : ¬ (-r < u ∧ u < r) := fun h => hin (abs_lt.2 h)
          simp [hnot, hout]
      rw [hc]
      have hsub : Ioo (-r) r ⊆ Ioc (-a) a := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [intervalIntegral.integral_of_le (by linarith), setIntegral_indicator measurableSet_Ioo,
        Set.inter_eq_right.2 hsub, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith), integral_rect hz]
      rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
      have hs := norm_sin_le_cosh (z * r)
      have him : (z * (r : ℂ)).im = z.im * r := by simp [mul_im]
      rw [him] at hs
      have hch : Real.cosh (z.im * r) ≤ Real.cosh (a * |z.im|) := by
        rw [Real.cosh_le_cosh, abs_mul, abs_of_nonneg hr0, abs_mul, abs_of_nonneg ha.le, abs_abs]
        nlinarith [abs_nonneg z.im]
      have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
      apply div_le_div_of_nonneg_right _ hzn.le
      linarith
    · have hz0 : ∫ u in (-a)..a, F u l = ∫ u in (-a)..a, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le (by linarith)] at hu
        have hua : |u| ∈ Icc 0 a := ⟨abs_nonneg u, abs_le.2 ⟨hu.1, hu.2⟩⟩
        have : ¬ l < gt |u| := fun h => hTe ⟨|u|, hua, h⟩
        simp [hF, Set.indicator, hgc, this]
      rw [hz0, intervalIntegral.integral_zero, norm_zero]; exact hpos
  calc ‖∫ l in Ioc 0 M, ∫ u in (-a)..a, F u l‖
      ≤ (2 * Real.cosh (a * |z.im|) / ‖z‖) * (volume (Ioc (0 : ℝ) M)).toReal :=
        norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top hbound
    _ = 2 * M * Real.cosh (a * |z.im|) / ‖z‖ := by
        rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]; ring


/-- `ĝ` is real on the real line for even integrable `g`. -/
theorem ghatC_im_eq_zero {g : ℝ → ℝ} {a : ℝ} (hev : ∀ u, g (-u) = g u)
    (hint : IntervalIntegrable g volume (-a) a) (x : ℝ) : (ghatC g a x).im = 0 := by
  have hgC : IntervalIntegrable (fun u => ((g u : ℝ) : ℂ)) volume (-a) a := ⟨hint.1.ofReal, hint.2.ofReal⟩
  have hc : IntervalIntegrable (fun u : ℝ => ((g u : ℝ) : ℂ) * Complex.exp (I * x * u)) volume (-a) a :=
    hgC.mul_continuousOn (by fun_prop : Continuous fun u : ℝ => Complex.exp (I * x * u)).continuousOn
  unfold ghatC
  rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm hc]
  simp only [Complex.imCLM_apply]
  set f : ℝ → ℝ := fun u => (((g u : ℝ) : ℂ) * Complex.exp (I * x * u)).im with hf
  have hform : ∀ u, f u = g u * Real.sin (x * u) := by
    intro u
    have e2 : (I * (x : ℂ) * (u : ℂ)) = ((x * u : ℝ) : ℂ) * I := by push_cast; ring
    simp only [hf, e2, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hodd : ∀ u, f (-u) = -f u := by
    intro u
    rw [hform, hform, hev, mul_neg, Real.sin_neg, mul_neg]
  have h := intervalIntegral.integral_comp_neg (a := -a) (b := a) f
  simp only [neg_neg] at h
  have : ∫ u in (-a)..a, f u = -∫ u in (-a)..a, f u := by
    conv_lhs => rw [← h]
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun u _ => hodd u
  linarith

/-- **Pinning without RH.** For a ground state `g` (even, `≥ 0`, non-increasing on `[0, a]`) and the
family `t` of nontrivial zeros, under the named inputs listed in the module docstring: if `t_j` is
real with `|t_j| ≤ H`, and the real function `x ↦ Re ĝ(x)` has slope at least `m` in absolute value,
of fixed sign, on `[t_j − r, t_j + r]` with `√(Q + B²S)/m ≤ r`, where `B = 2 g(0) cosh(a/2)`, then
`ĝ` has a real zero within `√(Q + B²S)/m` of `t_j`. -/
theorem pinned_unconditional {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hev : ∀ u, g (-u) = g u)
    (hmono : AntitoneOn g (Icc 0 a)) (hnn : ∀ u ∈ Icc 0 a, 0 ≤ g u)
    (hint : IntervalIntegrable g volume (-a) a)
    {ι : Type*} {t : ι → ℂ} {Q H S : ℝ} (hH : 0 ≤ H)
    (hsum : Summable fun i => ghatC g a (t i) ^ 2) (hQ : (Q : ℂ) = ∑' i, ghatC g a (t i) ^ 2)
    (hRH : ∀ i, |(t i).re| ≤ H → (t i).im = 0) (hstrip : ∀ i, |(t i).im| ≤ 1 / 2)
    (hS : Summable fun i => if H < |(t i).re| then 1 / (t i).re ^ 2 else 0)
    (hSle : (∑' i, if H < |(t i).re| then 1 / (t i).re ^ 2 else 0) ≤ S)
    (j : ι) (hj : |(t j).re| ≤ H) {m r : ℝ} (hm : 0 < m)
    (hr : Real.sqrt (Q + (2 * g 0 * Real.cosh (a / 2)) ^ 2 * S) / m ≤ r)
    (hc : ContinuousOn (fun x : ℝ => (ghatC g a x).re) (Icc ((t j).re - r) ((t j).re + r)))
    (hd : DifferentiableOn ℝ (fun x : ℝ => (ghatC g a x).re) (Ioo ((t j).re - r) ((t j).re + r)))
    (hslope : (∀ x ∈ Ioo ((t j).re - r) ((t j).re + r), m ≤ deriv (fun x : ℝ => (ghatC g a x).re) x) ∨
      (∀ x ∈ Ioo ((t j).re - r) ((t j).re + r), deriv (fun x : ℝ => (ghatC g a x).re) x ≤ -m)) :
    ∃ x ∈ Icc ((t j).re - Real.sqrt (Q + (2 * g 0 * Real.cosh (a / 2)) ^ 2 * S) / m)
      ((t j).re + Real.sqrt (Q + (2 * g 0 * Real.cosh (a / 2)) ^ 2 * S) / m), (ghatC g a x).re = 0 := by
  set B := 2 * g 0 * Real.cosh (a / 2)
  have hdecay : ∀ i, H < |(t i).re| → ‖ghatC g a (t i)‖ ≤ B / |(t i).re| := by
    intro i hi
    have hre : 0 < |(t i).re| := lt_of_le_of_lt hH hi
    have hz : t i ≠ 0 := fun h => by rw [h] at hre; simp at hre
    have h1 := norm_ghatC_le_of_antitone ha hev hmono hnn hz
    have hB0 : 0 ≤ 2 * g 0 := by have := hnn 0 ⟨le_rfl, ha.le⟩; linarith
    have hch : Real.cosh (a * |(t i).im|) ≤ Real.cosh (a / 2) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_of_pos ha, abs_abs, abs_of_pos (by linarith : (0 : ℝ) < a / 2)]
      nlinarith [hstrip i, abs_nonneg (t i).im]
    have hnz : |(t i).re| ≤ ‖t i‖ := Complex.abs_re_le_norm _
    calc ‖ghatC g a (t i)‖ ≤ 2 * g 0 * Real.cosh (a * |(t i).im|) / ‖t i‖ := h1
      _ ≤ 2 * g 0 * Real.cosh (a / 2) / ‖t i‖ := by gcongr
      _ ≤ B / |(t i).re| := by
          apply div_le_div_of_nonneg_left (by positivity) hre hnz
  have hreal : ∀ i, (t i).im = 0 → (ghatC g a (t i)).im = 0 := by
    intro i hi
    have : t i = ((t i).re : ℂ) := Complex.ext (by simp) (by simp [hi])
    rw [this]; exact ghatC_im_eq_zero hev hint _
  have hsq := sq_le_of_explicit_tail hsum hQ hRH hreal hdecay hS hSle j hj
  have htj : t j = ((t j).re : ℂ) := Complex.ext (by simp) (by simp [hRH j hj])
  have hsmall : |(ghatC g a ((t j).re : ℂ)).re| ≤ Real.sqrt (Q + B ^ 2 * S) := by
    rw [← htj]
    calc |(ghatC g a (t j)).re| ≤ ‖ghatC g a (t j)‖ := Complex.abs_re_le_norm _
      _ = Real.sqrt (‖ghatC g a (t j)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (Q + B ^ 2 * S) := Real.sqrt_le_sqrt hsq
  rcases hslope with h | h
  · exact zero_near_of_deriv_ge hm (Real.sqrt_nonneg _) hr hc hd h hsmall
  · exact zero_near_of_deriv_le hm (Real.sqrt_nonneg _) hr hc hd h hsmall

end Pilot1ca

#print axioms Pilot1ca.sq_le_of_explicit_tail
#print axioms Pilot1ca.norm_ghatC_le_of_antitone
#print axioms Pilot1ca.ghatC_im_eq_zero
#print axioms Pilot1ca.pinned_unconditional
