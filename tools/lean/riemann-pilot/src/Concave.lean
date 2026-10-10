import Mathlib
import Polya

/-! # Pólya's theorem for even concave probes, with no representation hypothesis

`realRooted_of_concaveOn`: let `g` be even, concave and `≥ 0` on `(−a, a)`, with `g(0) > 0`. Then
`ĝ(z) = ∫_{−a}^{a} g(u) e^{izu} du` has only real zeros. Nothing is assumed about `g` at `±a` or
outside. `realRooted_of_ae_concaveOn` is the same for any probe equal to such a `g` a.e. on `[−a, a]`.

This removes `Polya.lean`'s named input, the trapezoid-mixture representation of a concave
function. The measure `−g''` is never built. The proof uses only the one-sided derivative Mathlib
gives for convex functions.

* **At a support `b < a`.** `h = −g'₊` is `≥ 0` and nondecreasing on `[0, b]`
  (`monotoneOn_negRD`, `negRD_zero_nonneg`). Integration by parts with right derivatives gives
  `zĝ_b(z)/2 = g(b) sin(zb) + ∫₀^b h(t) sin(zt) dt` (`ghatC_byParts`). Dividing by
  `sin(zb)/z`, the imaginary part times `Im z` is `g(b)(Im z)² + ∫₀^b h w`. Here
  `∫_c^b w = Im z · Im[(cos zc − cos zb)/sin zb] ≥ 0` for every `c` (`tail_W`,
  `trap_ratio_mul_pos`). The layer-cake inequality (`layer_nonneg`) turns that into `∫₀^b h w ≥ 0`:
  it writes `h = ∫ 1[λ < h] dλ`, applies Fubini, and uses that each superlevel set of a monotone `h`
  is a final segment of `[0, b]`. Since `g(b) > 0` (`concave_pos`), `ĝ_b` has no non-real zero
  (`realRooted_concave_lt`).
* **The limit `b → a`.** `‖ĝ_a − ĝ_b‖ ≤ 2g(0)e^{‖z‖a}(a − b)`. So `ĝ_{b_n} → ĝ_a` locally
  uniformly, `ĝ_a(0) = ∫g > 0`, and `hurwitz_real` applies. -/

open Real MeasureTheory Complex Set

noncomputable section

namespace Pilot1ca

variable {a : ℝ} {g : ℝ → ℝ}

/-! ## Elementary facts about an even concave `g ≥ 0` on `(−a, a)` -/

theorem concave_le_zero_val (hc : ConcaveOn ℝ (Ioo (-a) a) g) (hev : ∀ t, g (-t) = g t)
    {t : ℝ} (ht : t ∈ Ioo (-a) a) : g t ≤ g 0 := by
  have ht' : -t ∈ Ioo (-a) a := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have := hc.2 ht ht' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, hev] at this
  have e : 1 / 2 * t + 1 / 2 * -t = 0 := by ring
  rw [e] at this; linarith

theorem concave_pos (hc : ConcaveOn ℝ (Ioo (-a) a) g) (hev : ∀ t, g (-t) = g t)
    (hnn : ∀ t ∈ Ioo (-a) a, 0 ≤ g t) (h0 : 0 < g 0) {t : ℝ} (ht : t ∈ Ioo (-a) a) : 0 < g t := by
  wlog htn : 0 ≤ t generalizing t
  · have := this (t := -t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ (by linarith)
    rwa [hev] at this
  set a' := (t + a) / 2 with ha'd
  have ha' : a' ∈ Ioo (-a) a := ⟨by linarith [ht.2], by linarith [ht.2]⟩
  have h0m : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  have hpos : 0 < a' := by linarith [ht.2]
  set θ := 1 - t / a' with hθd
  have hθ : 0 < θ := by
    have : t / a' < 1 := (div_lt_one hpos).2 (by linarith [ht.2])
    linarith
  have hθ1 : 0 ≤ 1 - θ := by simp only [θ]; have := div_nonneg htn hpos.le; linarith
  have := hc.2 h0m ha' hθ.le hθ1 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add] at this
  have e : (1 - θ) * a' = t := by simp only [θ]; field_simp; ring
  rw [e] at this
  have := hnn a' ha'
  nlinarith

/-! ## The right derivative `h = −g'₊` -/

/-- `h(x) = −g'(x+)`, the right derivative of the convex function `−g`. -/
def negRD (g : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin (-g) (Ioi x) x

theorem hasDerivWithinAt_negRD (hc : ConcaveOn ℝ (Ioo (-a) a) g) {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    HasDerivWithinAt g (-negRD g x) (Ioi x) x := by
  have h := hc.neg.hasDerivWithinAt_rightDeriv_of_mem_interior (by rwa [isOpen_Ioo.interior_eq])
  simpa [negRD] using h.neg

theorem monotoneOn_negRD (hc : ConcaveOn ℝ (Ioo (-a) a) g) : MonotoneOn (negRD g) (Ioo (-a) a) := by
  have := hc.neg.monotoneOn_rightDeriv
  rwa [isOpen_Ioo.interior_eq] at this

theorem negRD_zero_nonneg (hc : ConcaveOn ℝ (Ioo (-a) a) g) (hev : ∀ t, g (-t) = g t)
    (ha : 0 < a) : 0 ≤ negRD g 0 := by
  have h0 : (0 : ℝ) ∈ interior (Ioo (-a) a) := by
    rw [isOpen_Ioo.interior_eq]; exact ⟨by linarith, ha⟩
  unfold negRD
  rw [hc.neg.rightDeriv_eq_sInf_slope_of_mem_interior h0]
  apply le_csInf
  · refine ⟨_, ⟨a / 2, ⟨⟨by linarith, by linarith⟩, by linarith⟩, rfl⟩⟩
  · rintro _ ⟨y, ⟨hy, hy0⟩, rfl⟩
    rw [slope_def_field]
    apply div_nonneg _ (by linarith)
    have := concave_le_zero_val hc hev hy
    simp only [Pi.neg_apply]; linarith

/-! ## The transform at support `b < a` -/

theorem ghatC_even_cos (hev : ∀ t, g (-t) = g t) {b : ℝ} (hb : 0 ≤ b)
    (hg : ContinuousOn g (Icc (-b) b)) (z : ℂ) :
    ghatC g b z = ∫ t in (0 : ℝ)..b, (g t : ℂ) * (2 * Complex.cos (z * t)) := by
  have hcont : ∀ w : ℂ, ContinuousOn (fun t : ℝ => (g t : ℂ) * Complex.exp (w * t)) (Icc (-b) b) :=
    fun w => (continuous_ofReal.comp_continuousOn hg).mul (by fun_prop)
  have hii : ∀ w : ℂ, ∀ x y : ℝ, x ∈ Icc (-b) b → y ∈ Icc (-b) b →
      IntervalIntegrable (fun t : ℝ => (g t : ℂ) * Complex.exp (w * t)) volume x y :=
    fun w x y hx hy => ((hcont w).mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  have hb0 : (0 : ℝ) ∈ Icc (-b) b := ⟨by linarith, hb⟩
  have hbm : -b ∈ Icc (-b) b := ⟨le_rfl, by linarith⟩
  have hbp : b ∈ Icc (-b) b := ⟨by linarith, le_rfl⟩
  unfold ghatC
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii (I * z) _ _ hbm hb0)
    (hii (I * z) _ _ hb0 hbp)]
  have hneg : ∫ t in (-b)..0, (g t : ℂ) * Complex.exp (I * z * t)
      = ∫ t in (0 : ℝ)..b, (g t : ℂ) * Complex.exp (-(I * z) * t) := by
    rw [← neg_zero, ← intervalIntegral.integral_comp_neg, neg_zero]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hev]; push_cast; ring_nf
  rw [hneg, ← intervalIntegral.integral_add (hii _ _ _ hb0 hbp) (hii _ _ _ hb0 hbp)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  have := two_cos (z * t)
  rw [← mul_add, this, add_comm]
  congr 2 <;> ring_nf

/-- **The transform by parts** (`0 < b < a`, `z ≠ 0`):
`ĝ_b(z) = 2 g(b) sin(zb)/z + 2∫₀^b h(t) sin(zt)/z dt` with `h = −g'₊ ≥ 0`. -/
theorem ghatC_byParts (hc : ConcaveOn ℝ (Ioo (-a) a) g) (hev : ∀ t, g (-t) = g t) {b : ℝ}
    (hb : 0 < b) (hba : b < a) {z : ℂ} (hz : z ≠ 0) :
    ghatC g b z = 2 * ((g b : ℂ) * (Complex.sin (z * b) / z)
      + ∫ t in (0 : ℝ)..b, (negRD g t : ℂ) * (Complex.sin (z * t) / z)) := by
  have hS : Icc (-b) b ⊆ Ioo (-a) a := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgc : ContinuousOn g (Icc (-b) b) := (hc.continuousOn isOpen_Ioo).mono hS
  rw [ghatC_even_cos hev hb.le hgc]
  have hsub : uIcc 0 b ⊆ Ioo (-a) a := by
    rw [uIcc_of_le hb.le]; exact fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hu : ContinuousOn (fun t : ℝ => (g t : ℂ)) (uIcc 0 b) :=
    continuous_ofReal.comp_continuousOn ((hc.continuousOn isOpen_Ioo).mono hsub)
  have hv : ContinuousOn (fun t : ℝ => Complex.sin (z * t) / z) (uIcc 0 b) := by
    fun_prop
  have huu : ∀ x ∈ Ioo (min 0 b) (max 0 b),
      HasDerivWithinAt (fun t : ℝ => (g t : ℂ)) ((-negRD g x : ℝ) : ℂ) (Ioi x) x := by
    intro x hx
    rw [min_eq_left hb.le, max_eq_right hb.le] at hx
    exact (hasDerivWithinAt_negRD hc ⟨by linarith [hx.1], by linarith [hx.2]⟩).ofReal_comp
  have hvv : ∀ x ∈ Ioo (min 0 b) (max 0 b),
      HasDerivWithinAt (fun t : ℝ => Complex.sin (z * t) / z) (Complex.cos (z * x)) (Ioi x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => z * (y : ℂ)) (z * 1) x := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul z).comp_ofReal (z := x)
    have h2 : HasDerivAt (fun t : ℝ => Complex.sin (z * t) / z)
        (Complex.cos (z * x) * (z * 1) / z) x := by
      have h3 := HasDerivAt.comp (h₂ := Complex.sin) x (Complex.hasDerivAt_sin (z * x)) h1
      exact h3.div_const z
    convert h2.hasDerivWithinAt using 1
    field_simp
  have hmono : MonotoneOn (negRD g) (uIcc 0 b) := (monotoneOn_negRD hc).mono hsub
  have hu' : IntervalIntegrable (fun t : ℝ => ((-negRD g t : ℝ) : ℂ)) volume 0 b := by
    have := (hmono.intervalIntegrable (μ := volume)).neg
    exact ⟨this.1.ofReal, this.2.ofReal⟩
  have hv' : IntervalIntegrable (fun t : ℝ => Complex.cos (z * t)) volume 0 b :=
    (by fun_prop : Continuous fun t : ℝ => Complex.cos (z * t)).intervalIntegrable _ _
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hu hv huu hvv hu' hv'
  have e1 : ∫ t in (0 : ℝ)..b, (g t : ℂ) * (2 * Complex.cos (z * t))
      = 2 * ∫ t in (0 : ℝ)..b, (g t : ℂ) * Complex.cos (z * t) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
  rw [e1, ibp]
  have e2 : ∫ t in (0 : ℝ)..b, ((-negRD g t : ℝ) : ℂ) * (Complex.sin (z * t) / z)
      = -∫ t in (0 : ℝ)..b, (negRD g t : ℂ) * (Complex.sin (z * t) / z) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext t; push_cast; ring
  rw [e2]
  simp

/-! ## The layer-cake inequality -/


/-- The interval integral agrees off one point. -/
theorem intervalIntegral_congr_off_point {f f' : ℝ → ℝ} {p q c : ℝ}
    (h : ∀ x ∈ Ioc p q, x ≠ c → f x = f' x) (hpq : p ≤ q) :
    ∫ x in p..q, f x = ∫ x in p..q, f' x := by
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
    rw [ae_iff]; simp
  filter_upwards [hne] with x hx hmem
  rw [uIoc_of_le hpq] at hmem
  exact h x hmem hx

/-- **Layer-cake Fubini.** For a measurable profile `0 ≤ c ≤ H` and a bounded measurable `w`,
`∫_p^q c(s)·w(s) ds = ∫_{(0, H]} ∫_p^q 1[l < c(s)] w(s) ds dl`. -/
theorem layer_fubini {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q H C : ℝ} (hpq : p ≤ q) {c : ℝ → ℝ} (hcm : Measurable c) (hc0 : ∀ s, 0 ≤ c s)
    (hcH : ∀ s, c s ≤ H) {w : ℝ → E} (hw : Measurable w) (hwC : ∀ s ∈ Ioc p q, ‖w s‖ ≤ C) :
    ∫ s in p..q, c s • w s = ∫ l in Ioc 0 H, ∫ s in p..q, (Iio (c s)).indicator (fun _ => w s) l := by
  set F : ℝ → ℝ → E := fun s l => (Iio (c s)).indicator (fun _ => w s) l with hF
  have hlayer : ∀ s, c s • w s = ∫ l in Ioc 0 H, F s l := by
    intro s
    simp only [hF]
    rw [setIntegral_indicator measurableSet_Iio, setIntegral_const]
    have hset : Ioc 0 H ∩ Iio (c s) = Ioo 0 (c s) := by
      ext l; simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, (h3.trans_le (hcH s)).le⟩, h3⟩
    rw [hset, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [hc0 s]), sub_zero]
  have hfin : IsFiniteMeasure (volume.restrict (uIoc p q)) := by
    rw [uIoc_of_le hpq]; exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hfin2 : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) H)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hmeasF : Measurable (Function.uncurry F) := by
    have e : Function.uncurry F = {x : ℝ × ℝ | x.2 < c x.1}.indicator (fun x => w x.1) := by
      funext ⟨s, l⟩; simp [hF, Set.indicator]
    rw [e]
    exact (hw.comp measurable_fst).indicator (measurableSet_lt measurable_snd (hcm.comp measurable_fst))
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc p q)).prod (volume.restrict (Ioc 0 H))) := by
    refine Integrable.of_bound hmeasF.aestronglyMeasurable C ?_
    rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_uIoc.prod measurableSet_Ioc) ?_
    rintro ⟨s, l⟩ ⟨hs, _⟩
    rw [uIoc_of_le hpq] at hs
    exact (norm_indicator_le_norm_self (fun _ => w s) l).trans (hwC s hs)
  have e1 : ∫ s in p..q, c s • w s = ∫ s in p..q, ∫ l in Ioc 0 H, F s l := by
    congr 1; funext s; exact hlayer s
  rw [e1, intervalIntegral_integral_swap hint]

/-- **The layer-cake inequality.** If `h ≥ 0` is nondecreasing on `[0, b]` and every tail integral
`∫_c^b w` (`c ∈ [0, b]`) is `≥ 0`, then `∫₀^b h w ≥ 0`. -/
theorem layer_nonneg {b : ℝ} (hb : 0 < b) {h : ℝ → ℝ} (hmono : MonotoneOn h (Icc 0 b))
    (hnn : 0 ≤ h 0) {w : ℝ → ℝ} (hw : Continuous w)
    (htail : ∀ c ∈ Icc 0 b, 0 ≤ ∫ s in c..b, w s) : 0 ≤ ∫ s in (0 : ℝ)..b, h s * w s := by
  set cl : ℝ → ℝ := fun s => max 0 (min s b) with hcl
  have hclm : ∀ s, cl s ∈ Icc 0 b := fun s => ⟨le_max_left _ _, max_le hb.le (min_le_right _ _)⟩
  have hclmono : Monotone cl := fun x y hxy => max_le_max le_rfl (min_le_min hxy le_rfl)
  set hc : ℝ → ℝ := fun s => h (cl s) with hhc
  have hcm : Monotone hc := fun x y hxy => hmono (hclm x) (hclm y) (hclmono hxy)
  set H := h b
  have hcnn : ∀ s, 0 ≤ hc s := fun s => hnn.trans (hmono ⟨le_rfl, hb.le⟩ (hclm s) (hclm s).1)
  have hcH : ∀ s, hc s ≤ H := fun s => hmono (hclm s) ⟨hb.le, le_rfl⟩ (hclm s).2
  -- replace `h` by the clamped `hc`
  have e0 : ∫ s in (0 : ℝ)..b, h s * w s = ∫ s in (0 : ℝ)..b, hc s * w s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hb.le] at hs
    simp only [hhc, hcl, min_eq_left hs.2, max_eq_right hs.1]
  rw [e0]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hw.continuousOn (s := Icc 0 b))
  have hL := layer_fubini (E := ℝ) hb.le hcm.measurable hcnn hcH hw.measurable
    (fun s hs => hC s ⟨hs.1.le, hs.2⟩)
  simp only [smul_eq_mul] at hL
  rw [hL]
  set F : ℝ → ℝ → ℝ := fun s l => (Iio (hc s)).indicator (fun _ => w s) l with hF
  -- each layer contributes a tail integral
  refine setIntegral_nonneg measurableSet_Ioc fun l hl => ?_
  set T := {s ∈ Icc 0 b | l < hc s} with hT
  by_cases hTe : T.Nonempty
  · have hbdd : BddBelow T := ⟨0, fun s hs => hs.1.1⟩
    set c := sInf T with hc_def
    have hc0 : 0 ≤ c := le_csInf hTe fun s hs => hs.1.1
    have hcb : c ≤ b := by
      obtain ⟨s, hs⟩ := hTe
      exact (csInf_le hbdd hs).trans hs.1.2
    have hcongr : ∫ s in (0 : ℝ)..b, F s l = ∫ s in (0 : ℝ)..b, (Ioc c b).indicator w s := by
      apply intervalIntegral_congr_off_point (c := c) _ hb.le
      intro s hs hsc
      simp only [hF, Set.indicator, mem_Iio, mem_Ioc]
      rcases lt_or_gt_of_ne hsc with hlt | hgt
      · have hnot : s ∉ T := notMem_of_lt_csInf hlt hbdd
        have : ¬ l < hc s := fun h' => hnot ⟨⟨hs.1.le, hs.2⟩, h'⟩
        simp [this, not_lt.2 hlt.le]
      · obtain ⟨t, ht, hts⟩ := exists_lt_of_csInf_lt hTe hgt
        have : l < hc s := ht.2.trans_le (hcm hts.le)
        simp [this, hgt, hs.2]
    rw [hcongr, intervalIntegral.integral_of_le hb.le, setIntegral_indicator measurableSet_Ioc]
    have hset : Ioc 0 b ∩ Ioc c b = Ioc c b := by
      ext s; simp only [mem_inter_iff, mem_Ioc]
      constructor
      · rintro ⟨_, h2⟩; exact h2
      · rintro ⟨h1, h2⟩; exact ⟨⟨hc0.trans_lt h1, h2⟩, h1, h2⟩
    rw [hset, ← intervalIntegral.integral_of_le hcb]
    exact htail c ⟨hc0, hcb⟩
  · have hz : ∫ s in (0 : ℝ)..b, F s l = ∫ s in (0 : ℝ)..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hb.le] at hs
      have : ¬ l < hc s := fun h' => hTe ⟨s, hs, h'⟩
      simp [hF, Set.indicator, this]
    rw [hz, intervalIntegral.integral_zero]


/-! ## Real-rootedness at support `b < a` -/

/-- `∫_c^b z sin(zs)/sin(zb) ds = (cos zc − cos zb)/sin zb`. -/
theorem tail_W (z : ℂ) (b c : ℝ) :
    ∫ s in c..b, z * Complex.sin (z * s) / Complex.sin (z * b)
      = (Complex.cos (z * c) - Complex.cos (z * b)) / Complex.sin (z * b) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun s : ℝ => -Complex.cos (z * s) / Complex.sin (z * b))
      (z * Complex.sin (z * x) / Complex.sin (z * b)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => z * (y : ℂ)) (z * 1) x := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul z).comp_ofReal (z := x)
    have h3 := HasDerivAt.comp (h₂ := Complex.cos) x (Complex.hasDerivAt_cos (z * x)) h1
    have h4 : HasDerivAt (fun s : ℝ => -Complex.cos (z * s) / Complex.sin (z * b))
        (-(-Complex.sin (z * x) * (z * 1)) / Complex.sin (z * b)) x := h3.neg.div_const _
    rw [show z * Complex.sin (z * x) / Complex.sin (z * b)
      = -(-Complex.sin (z * x) * (z * 1)) / Complex.sin (z * b) by ring]
    exact h4
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous fun s : ℝ => z * Complex.sin (z * s) / Complex.sin (z * b)
      ).intervalIntegrable _ _)]
  ring

/-- **Pólya at support `b < a`.** For `g` even, concave and `≥ 0` on `(−a, a)` with `g(0) > 0`, the
transform over `[−b, b]` is real-rooted. -/
theorem realRooted_concave_lt (hc : ConcaveOn ℝ (Ioo (-a) a) g) (hev : ∀ t, g (-t) = g t)
    (hnn : ∀ t ∈ Ioo (-a) a, 0 ≤ g t) (h0 : 0 < g 0) {b : ℝ} (hb : 0 < b) (hba : b < a) :
    RealRooted b g := by
  have ha : 0 < a := hb.trans hba
  intro z hz0
  by_contra hy
  have hz : z ≠ 0 := by rintro rfl; exact hy (by simp)
  have hs : Complex.sin (z * b) ≠ 0 := sin_ne_zero_of_im (by simp; exact ⟨hy, hb.ne'⟩)
  set W : ℝ → ℂ := fun t => z * Complex.sin (z * t) / Complex.sin (z * b) with hW
  have hWc : Continuous W := by simp only [hW]; fun_prop
  have hsub : uIcc 0 b ⊆ Ioo (-a) a := by
    rw [uIcc_of_le hb.le]; exact fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmono : MonotoneOn (negRD g) (uIcc 0 b) := (monotoneOn_negRD hc).mono hsub
  have hhi : IntervalIntegrable (fun t => (negRD g t : ℂ)) volume 0 b := by
    have := hmono.intervalIntegrable (μ := volume)
    exact ⟨this.1.ofReal, this.2.ofReal⟩
  -- `g(b) z + ∫₀^b h W = 0`
  have hform := ghatC_byParts hc hev hb hba hz
  rw [hz0] at hform
  have hkey : (g b : ℂ) * z + ∫ t in (0 : ℝ)..b, (negRD g t : ℂ) * W t = 0 := by
    have e : ∫ t in (0 : ℝ)..b, (negRD g t : ℂ) * W t
        = (z ^ 2 / Complex.sin (z * b)) * ∫ t in (0 : ℝ)..b, (negRD g t : ℂ) * (Complex.sin (z * t) / z) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext t; simp only [hW]; field_simp
    rw [e]
    have : (g b : ℂ) * z + z ^ 2 / Complex.sin (z * b) *
        ∫ t in (0 : ℝ)..b, (negRD g t : ℂ) * (Complex.sin (z * t) / z)
        = (z ^ 2 / (2 * Complex.sin (z * b))) * (2 * ((g b : ℂ) * (Complex.sin (z * b) / z)
          + ∫ t in (0 : ℝ)..b, (negRD g t : ℂ) * (Complex.sin (z * t) / z))) := by
      field_simp
    rw [this, ← hform, mul_zero]
  -- take `Im z · Im(·)`
  have hint : IntervalIntegrable (fun t => (negRD g t : ℂ) * W t) volume 0 b :=
    hhi.mul_continuousOn hWc.continuousOn
  have him : ((∫ t in (0 : ℝ)..b, (negRD g t : ℂ) * W t)).im
      = ∫ t in (0 : ℝ)..b, negRD g t * (W t).im := by
    rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm hint]
    congr 1; funext t; simp
  have h2 := congrArg (fun w => z.im * w.im) hkey
  simp only [add_im, zero_im, mul_zero, im_ofReal_mul, him] at h2
  -- the layer-cake inequality
  set w : ℝ → ℝ := fun t => z.im * (W t).im with hw
  have hwc : Continuous w := continuous_const.mul (Complex.continuous_im.comp hWc)
  have hlay : 0 ≤ ∫ t in (0 : ℝ)..b, negRD g t * w t := by
    refine layer_nonneg hb (hmono.mono (by rw [uIcc_of_le hb.le])) (negRD_zero_nonneg hc hev ha)
      hwc fun c hc' => ?_
    have htw : ∫ s in c..b, w s = z.im * ((Complex.cos (z * c) - Complex.cos (z * b))
        / Complex.sin (z * b)).im := by
      have hI : (∫ s in c..b, W s).im = ∫ s in c..b, (W s).im := by
        rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm
          (hWc.intervalIntegrable _ _)]
        rfl
      simp only [hw]
      rw [intervalIntegral.integral_const_mul, ← hI, ← tail_W]
    rw [htw]
    rcases eq_or_lt_of_le hc'.2 with hcb | hcb
    · rw [hcb, sub_self, zero_div, zero_im, mul_zero]
    · exact (trap_ratio_mul_pos hy hcb (by linarith [hc'.1])).le
  have hgb : 0 < g b := concave_pos hc hev hnn h0 ⟨by linarith, hba⟩
  have hy2 : 0 < z.im * z.im := mul_self_pos.2 hy
  have e3 : z.im * ∫ t in (0 : ℝ)..b, negRD g t * (W t).im = ∫ t in (0 : ℝ)..b, negRD g t * w t := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; simp only [hw]; ring
  rw [mul_add, e3] at h2
  nlinarith

/-! ## The limit `b → a` (Hurwitz) -/

theorem intervalIntegrable_concave (ha : 0 < a) (hc : ConcaveOn ℝ (Ioo (-a) a) g)
    (hev : ∀ t, g (-t) = g t) (hnn : ∀ t ∈ Ioo (-a) a, 0 ≤ g t) :
    IntervalIntegrable g volume (-a) a := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)]
  refine IntegrableOn.of_bound measure_Ioo_lt_top
    ((hc.continuousOn isOpen_Ioo).aestronglyMeasurable measurableSet_Ioo) (g 0) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn t ht)]
  exact concave_le_zero_val hc hev ht

/-- **Pólya's theorem for even concave probes.** An even function, concave and `≥ 0` on `(−a, a)`
and not identically zero (`g(0) > 0`), has a real-rooted transform over `[−a, a]`. Nothing about its
values at `±a` is assumed. -/
theorem realRooted_of_concaveOn (ha : 0 < a) (hc : ConcaveOn ℝ (Ioo (-a) a) g)
    (hev : ∀ t, g (-t) = g t) (hnn : ∀ t ∈ Ioo (-a) a, 0 ≤ g t) (h0 : 0 < g 0) :
    RealRooted a g := by
  set bs : ℕ → ℝ := fun n => a * (n + 1) / (n + 2) with hbs
  have hbpos : ∀ n, 0 < bs n := fun n => by simp only [hbs]; positivity
  have hblt : ∀ n, bs n < a := fun n => by
    simp only [hbs]; rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hgint := intervalIntegrable_concave ha hc hev hnn
  have hgintb : ∀ n, IntervalIntegrable g volume (-(bs n)) (bs n) := fun n =>
    ((hc.continuousOn isOpen_Ioo).mono fun t (ht : t ∈ uIcc (-(bs n)) (bs n)) => by
      rw [uIcc_of_le (by linarith [hbpos n])] at ht
      exact ⟨by linarith [ht.1, hblt n], by linarith [ht.2, hblt n]⟩).intervalIntegrable
  -- `ĝ_{b_n} → ĝ_a` locally uniformly
  have hbound : ∀ n (z : ℂ), ‖ghatC g a z - ghatC g (bs n) z‖
      ≤ 2 * (g 0 * Real.exp (‖z‖ * a) * (a - bs n)) := by
    intro n z
    set b := bs n
    have hb := hbpos n
    have hba := hblt n
    set f : ℝ → ℂ := fun u => (g u : ℂ) * Complex.exp (I * z * u) with hf
    have hgC : IntervalIntegrable (fun u => (g u : ℂ)) volume (-a) a := ⟨hgint.1.ofReal, hgint.2.ofReal⟩
    have hfi : IntervalIntegrable f volume (-a) a :=
      hgC.mul_continuousOn (by fun_prop : Continuous fun u : ℝ => Complex.exp (I * z * u)).continuousOn
    have hsub : ∀ p q, p ∈ Icc (-a) a → q ∈ Icc (-a) a → IntervalIntegrable f volume p q :=
      fun p q hp hq => hfi.mono_set (uIcc_subset_uIcc (by rwa [uIcc_of_le (by linarith)])
        (by rwa [uIcc_of_le (by linarith)]))
    have m1 : -a ∈ Icc (-a) a := ⟨le_rfl, by linarith⟩
    have m2 : -b ∈ Icc (-a) a := ⟨by linarith, by linarith⟩
    have m3 : b ∈ Icc (-a) a := ⟨by linarith, by linarith⟩
    have m4 : a ∈ Icc (-a) a := ⟨by linarith, le_rfl⟩
    have hsplit : ghatC g a z - ghatC g b z
        = (∫ u in (-a)..(-b), f u) + ∫ u in b..a, f u := by
      unfold ghatC
      rw [← intervalIntegral.integral_add_adjacent_intervals (hsub _ _ m1 m2) (hsub _ _ m2 m4),
        ← intervalIntegral.integral_add_adjacent_intervals (hsub _ _ m2 m3) (hsub _ _ m3 m4)]
      ring
    have hpt : ∀ u, |u| < a → ‖f u‖ ≤ g 0 * Real.exp (‖z‖ * a) := by
      intro u hu
      have hmem : u ∈ Ioo (-a) a := abs_lt.1 hu
      simp only [hf]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn u hmem),
        Complex.norm_exp]
      apply mul_le_mul (concave_le_zero_val hc hev hmem) _ (Real.exp_pos _).le h0.le
      apply Real.exp_le_exp.2
      have e : (I * z * (u : ℂ)).re = -(z.im * u) := by simp [mul_re]
      rw [e]
      calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
        _ = |z.im| * |u| := abs_mul _ _
        _ ≤ ‖z‖ * a := mul_le_mul (abs_im_le_norm z) hu.le (abs_nonneg _) (norm_nonneg _)
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a := by rw [ae_iff]; simp
    have n1 : ‖∫ u in (-a)..(-b), f u‖ ≤ g 0 * Real.exp (‖z‖ * a) * (a - b) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := -a) (b := -b)
        (C := g 0 * Real.exp (‖z‖ * a)) (f := f) (Filter.Eventually.of_forall fun u hu => by
          rw [uIoc_of_le (by linarith)] at hu
          exact hpt u (abs_lt.2 ⟨hu.1, by linarith [hu.2]⟩))
      rwa [show |-b - -a| = a - b by rw [abs_of_nonneg (by linarith)]; ring] at this
    have n2 : ‖∫ u in b..a, f u‖ ≤ g 0 * Real.exp (‖z‖ * a) * (a - b) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := b) (b := a)
        (C := g 0 * Real.exp (‖z‖ * a)) (f := f) (hne.mono fun u hua hu => by
          rw [uIoc_of_le (by linarith)] at hu
          exact hpt u (abs_lt.2 ⟨by linarith [hu.1], lt_of_le_of_ne hu.2 hua⟩))
      rwa [abs_of_nonneg (by linarith)] at this
    rw [hsplit]
    calc _ ≤ ‖∫ u in (-a)..(-b), f u‖ + ‖∫ u in b..a, f u‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hconv : TendstoLocallyUniformly (fun n => ghatC g (bs n)) (ghatC g a) Filter.atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set M := 2 * (g 0 * Real.exp (max R 0 * a))
    have hlim : Filter.Tendsto (fun n : ℕ => M * (a - bs n)) Filter.atTop (nhds 0) := by
      have e : (fun n : ℕ => M * (a - bs n)) = fun n : ℕ => M * a * (1 / ((n : ℝ) + 2)) := by
        funext n; simp only [hbs]; field_simp; ring
      rw [e]
      have : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
        refine h.congr fun n => ?_
        simp only [Function.comp_apply]; push_cast; ring
      simpa using this.const_mul (M * a)
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn z hz
    rw [dist_eq_norm]
    have hzR : ‖z‖ ≤ max R 0 := by
      have := hR hz; rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    calc ‖ghatC g a z - ghatC g (bs n) z‖ ≤ 2 * (g 0 * Real.exp (‖z‖ * a) * (a - bs n)) :=
          hbound n z
      _ ≤ M * (a - bs n) := by
          simp only [M]
          have : Real.exp (‖z‖ * a) ≤ Real.exp (max R 0 * a) :=
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hzR ha.le)
          have h1 : 0 ≤ a - bs n := by linarith [hblt n]
          have h2 := h0.le
          nlinarith [mul_le_mul_of_nonneg_left this h2, mul_nonneg h2 (Real.exp_pos (‖z‖ * a)).le]
      _ < ε := hn
  -- `ĝ_a(0) = ∫ g > 0`
  have hnz : ghatC g a 0 ≠ 0 := by
    have e : ghatC g a 0 = ((∫ u in (-a)..a, g u : ℝ) : ℂ) := by
      unfold ghatC; rw [← intervalIntegral.integral_ofReal]; simp
    rw [e, Complex.ofReal_ne_zero]
    exact (intervalIntegral.intervalIntegral_pos_of_pos_on hgint
      (fun x hx => concave_pos hc hev hnn h0 hx) (by linarith)).ne'
  exact hurwitz_real (fun n => ghatC_differentiable (hgintb n)) (ghatC_differentiable hgint)
    hconv ⟨0, hnz⟩ (fun n => realRooted_concave_lt hc hev hnn h0 (hbpos n) (hblt n))

/-- **For probes**: a function equal a.e. on `[−a, a]` to an even, concave, nonnegative function
with positive centre value is real-rooted. -/
theorem realRooted_of_ae_concaveOn (ha : 0 < a) (hc : ConcaveOn ℝ (Ioo (-a) a) g)
    (hev : ∀ t, g (-t) = g t) (hnn : ∀ t ∈ Ioo (-a) a, 0 ≤ g t) (h0 : 0 < g 0) {p : ℝ → ℝ}
    (hp : ∀ᵐ u ∂volume, |u| ≤ a → p u = g u) : RealRooted a p := by
  have he : ghatC p a = ghatC g a := by
    funext z
    unfold ghatC
    refine intervalIntegral.integral_congr_ae (hp.mono fun u hu hmem => ?_)
    rw [uIoc_of_le (by linarith)] at hmem
    rw [hu (abs_le.2 ⟨hmem.1.le, hmem.2⟩)]
  intro z hz
  rw [he] at hz
  exact realRooted_of_concaveOn ha hc hev hnn h0 z hz

end Pilot1ca

#print axioms Pilot1ca.ghatC_byParts
#print axioms Pilot1ca.layer_fubini
#print axioms Pilot1ca.layer_nonneg
#print axioms Pilot1ca.realRooted_concave_lt
#print axioms Pilot1ca.realRooted_of_concaveOn
#print axioms Pilot1ca.realRooted_of_ae_concaveOn
