import Mathlib
import Compactness

/-! # Existence of the ground state, stage 3: the minimiser

For `a > 0` a ground state of Weil's form at support `δ = 2a` exists:

* the pole term, `‖g‖²` and the autocorrelation are continuous under `L²` convergence (they are
  `L²` inner products);
* the archimedean energy is lower semicontinuous (Fatou);
* the `L²` limit is made a probe by `symCut`, the symmetrise-and-cut-off map, which fixes probes
  and does not increase `‖·‖²`;
* `c·1_{[−a,a]}` is a probe with `‖·‖² = 1`, so the infimum is over a non-empty set.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## `L²` inner products -/

theorem integral_mul_eq_inner {f h : ℝ → ℝ} (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) :
    ∫ t, f t * h t = @inner ℝ _ _ (hf.toLp f) (hh.toLp h) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hh.coeFn_toLp] with t h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem norm_toLp_sub_sq {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = normSq (fun t => f t - g t) := by
  rw [← MemLp.toLp_sub, L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (hf.sub hg)] with t ht
  rw [ht]; rfl

theorem tendsto_toLp {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ} (hf : ∀ j, MemLp (f j) 2 volume)
    (hF : MemLp F 2 volume)
    (hlim : Tendsto (fun j => normSq (fun t => f j t - F t)) atTop (𝓝 0)) :
    Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hF.toLp F)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have : (fun j => ‖(hf j).toLp (f j) - hF.toLp F‖)
      = fun j => Real.sqrt (normSq (fun t => f j t - F t)) := by
    funext j
    rw [← norm_toLp_sub_sq (hf j) hF, Real.sqrt_sq (norm_nonneg _)]
  rw [this]
  have h := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [Real.sqrt_zero] at h
  exact h

/-- **`∫ f_j h_j → ∫ f h`** when `f_j → f` and `h_j → h` in `L²`. -/
theorem tendsto_integral_mul {f h : ℕ → ℝ → ℝ} {F H : ℝ → ℝ} (hf : ∀ j, MemLp (f j) 2 volume)
    (hh : ∀ j, MemLp (h j) 2 volume) (hF : MemLp F 2 volume) (hH : MemLp H 2 volume)
    (hfl : Tendsto (fun j => normSq (fun t => f j t - F t)) atTop (𝓝 0))
    (hhl : Tendsto (fun j => normSq (fun t => h j t - H t)) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ t, f j t * h j t) atTop (𝓝 (∫ t, F t * H t)) := by
  simp_rw [integral_mul_eq_inner (hf _) (hh _), integral_mul_eq_inner hF hH]
  exact (tendsto_toLp hf hF hfl).inner (tendsto_toLp hh hH hhl)

theorem memLp_shift {g : ℝ → ℝ} (hg : MemLp g 2 volume) (u : ℝ) :
    MemLp (fun t => g (t + u)) 2 volume :=
  hg.comp_measurePreserving (measurePreserving_add_right volume u)

theorem normSq_shift (g : ℝ → ℝ) (u : ℝ) : normSq (fun t => g (t + u)) = normSq g :=
  integral_add_right_eq_self (fun t => g t ^ 2) u

theorem normSq_neg (g : ℝ → ℝ) : normSq (fun t => g (-t)) = normSq g :=
  integral_neg_eq_self (fun t => g t ^ 2) volume

/-! ## Symmetrise and cut off -/

/-- `S f (u) = 1_{|u| ≤ a}·(f(u) + f(−u))/2`. -/
def symCut (a : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := if |u| ≤ a then (f u + f (-u)) / 2 else 0

theorem symCut_probe {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) : symCut a g = g := by
  funext u
  unfold symCut
  split_ifs with hu
  · rw [hp.even]; ring
  · exact (hp.supp u (lt_of_not_ge hu)).symm

theorem symCut_even (a : ℝ) (f : ℝ → ℝ) (u : ℝ) : symCut a f (-u) = symCut a f u := by
  unfold symCut; rw [abs_neg, neg_neg, add_comm]

theorem symCut_supp (a : ℝ) (f : ℝ → ℝ) (u : ℝ) (hu : a < |u|) : symCut a f u = 0 := by
  unfold symCut; simp [not_le.2 hu]

theorem memLp_neg {f : ℝ → ℝ} (hf : MemLp f 2 volume) : MemLp (fun t => f (-t)) 2 volume :=
  hf.comp_measurePreserving (Measure.measurePreserving_neg volume)

theorem memLp_symCut (a : ℝ) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    MemLp (symCut a f) 2 volume := by
  have h1 : MemLp (fun u => (f u + f (-u)) / 2) 2 volume := by
    have := (hf.add (memLp_neg hf)).const_mul (1 / 2 : ℝ)
    convert this using 1
    funext u; simp only [Pi.add_apply]; ring
  have : symCut a f = Set.indicator {u | |u| ≤ a} (fun u => (f u + f (-u)) / 2) := by
    funext u; unfold symCut; simp [Set.indicator_apply]
  rw [this]
  exact h1.indicator (measurableSet_le continuous_abs.measurable measurable_const)

/-- `S` does not increase `‖·‖²`. -/
theorem normSq_symCut_le (a : ℝ) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    normSq (symCut a f) ≤ normSq f := by
  have hI := hf.integrable_sq
  have hJ : Integrable (fun t => f (-t) ^ 2) := (memLp_neg hf).integrable_sq
  have hK : Integrable (fun t => (f t ^ 2 + f (-t) ^ 2) / 2) := (hI.add hJ).div_const 2
  unfold normSq
  calc (∫ t, symCut a f t ^ 2) ≤ ∫ t, (f t ^ 2 + f (-t) ^ 2) / 2 := by
        refine integral_mono (memLp_symCut a hf).integrable_sq hK fun t => ?_
        unfold symCut
        split_ifs
        · nlinarith [sq_nonneg (f t - f (-t))]
        · nlinarith [sq_nonneg (f t), sq_nonneg (f (-t))]
    _ = ∫ t, f t ^ 2 := by
        rw [integral_div, integral_add hI hJ, integral_neg_eq_self (fun t => f t ^ 2)]
        ring

theorem symCut_sub (a : ℝ) (f g : ℝ → ℝ) :
    symCut a (fun t => f t - g t) = fun t => symCut a f t - symCut a g t := by
  funext u; unfold symCut; split_ifs <;> ring

/-- **The `L²` limit of probes, symmetrised and cut off, is still their limit.** -/
theorem normSq_sub_symCut_le {a : ℝ} {g G : ℝ → ℝ} (hp : Probe a g) (hG : MemLp G 2 volume) :
    normSq (fun t => g t - symCut a G t) ≤ normSq (fun t => g t - G t) := by
  have := normSq_symCut_le a (hp.memL2.sub hG) (f := fun t => g t - G t)
  rwa [symCut_sub, symCut_probe hp] at this

/-! ## Fatou -/

/-- **Fatou, real form**: non-negative integrable `f_j → F` pointwise on `s`, with `∫_s f_j → A`,
give `F` integrable on `s` and `∫_s F ≤ A`. -/
theorem fatou_real {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hf : ∀ j, IntegrableOn (f j) s) (hnn : ∀ j, ∀ x ∈ s, 0 ≤ f j x)
    (hlim : ∀ x ∈ s, Tendsto (fun j => f j x) atTop (𝓝 (F x))) {A : ℝ}
    (hA : Tendsto (fun j => ∫ x in s, f j x) atTop (𝓝 A)) :
    IntegrableOn F s ∧ ∫ x in s, F x ≤ A := by
  have hlim' : ∀ᵐ x ∂(volume.restrict s), Tendsto (fun j => f j x) atTop (𝓝 (F x)) :=
    (ae_restrict_iff' hs).2 (Eventually.of_forall hlim)
  have hFm : AEStronglyMeasurable F (volume.restrict s) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun j => (hf j).aestronglyMeasurable) hlim'
  have hnn' : ∀ j, 0 ≤ᵐ[volume.restrict s] f j := fun j =>
    (ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx => hnn j x hx)
  have hF0 : 0 ≤ᵐ[volume.restrict s] F :=
    (ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx =>
      ge_of_tendsto' (hlim x hx) fun j => hnn j x hx)
  have hA0 : 0 ≤ A := ge_of_tendsto' hA fun j => setIntegral_nonneg hs (hnn j)
  have hlin : ∀ j, ∫⁻ x in s, ENNReal.ofReal (f j x) = ENNReal.ofReal (∫ x in s, f j x) :=
    fun j => (ofReal_integral_eq_lintegral_ofReal (hf j) (hnn' j)).symm
  have key : ∫⁻ x in s, ENNReal.ofReal (F x) ≤ ENNReal.ofReal A := by
    calc ∫⁻ x in s, ENNReal.ofReal (F x)
        = ∫⁻ x in s, liminf (fun j => ENNReal.ofReal (f j x)) atTop := by
          refine lintegral_congr_ae (hlim'.mono fun x hx => ?_)
          exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ liminf (fun j => ∫⁻ x in s, ENNReal.ofReal (f j x)) atTop :=
          lintegral_liminf_le' fun j => (hf j).aemeasurable.ennreal_ofReal
      _ = ENNReal.ofReal A := by
          simp_rw [hlin]
          exact ((ENNReal.continuous_ofReal.tendsto _).comp hA).liminf_eq
  have hfin : ∫⁻ x in s, ENNReal.ofReal (F x) < ⊤ := key.trans_lt ENNReal.ofReal_lt_top
  have hint : IntegrableOn F s := ⟨hFm, (hasFiniteIntegral_iff_ofReal hF0).2 hfin⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hF0 hFm]
  calc (∫⁻ x in s, ENNReal.ofReal (F x)).toReal ≤ (ENNReal.ofReal A).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top key
    _ = A := ENNReal.toReal_ofReal hA0

/-! ## Measurability and `L²` membership helpers -/

theorem autocorr_stronglyMeasurable {g : ℝ → ℝ} (hg : Measurable g) :
    StronglyMeasurable (autocorr g) := by
  have : StronglyMeasurable (fun p : ℝ × ℝ => g p.2 * g (p.2 + p.1)) :=
    ((hg.comp measurable_snd).mul (hg.comp (measurable_snd.add measurable_fst))).stronglyMeasurable
  exact this.integral_prod_right'

theorem memLp_indicator_of_continuous {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ}
    (hs : MeasurableSet s) (hfin : volume s ≠ ⊤) {C : ℝ} (hC : ∀ x ∈ s, |f x| ≤ C) :
    MemLp (s.indicator f) 2 volume := by
  rw [memLp_indicator_iff_restrict hs]
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.2 hfin
  exact MemLp.of_bound hf.aestronglyMeasurable C
    ((ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs]; exact hC x hx))

/-! ## An admissible probe: `c·1_{[−a,a]}`, `c = (2a)^{−1/2}` -/

/-- The normalised box `c·1_{[−a, a]}`. -/
def box (a : ℝ) : ℝ → ℝ := Set.indicator (Icc (-a) a) fun _ => 1 / Real.sqrt (2 * a)

theorem box_apply (a u : ℝ) : box a u = if |u| ≤ a then 1 / Real.sqrt (2 * a) else 0 := by
  unfold box; simp [Set.indicator_apply, abs_le]

theorem box_memLp (a : ℝ) : MemLp (box a) 2 volume :=
  memLp_indicator_of_continuous continuous_const measurableSet_Icc measure_Icc_lt_top.ne
    (C := |1 / Real.sqrt (2 * a)|) fun _ _ => le_rfl

theorem box_measurable (a : ℝ) : Measurable (box a) :=
  measurable_const.indicator measurableSet_Icc

theorem normSq_box {a : ℝ} (ha : 0 < a) : normSq (box a) = 1 := by
  unfold normSq
  have : (fun t => box a t ^ 2) = Set.indicator (Icc (-a) a) fun _ => (1 / Real.sqrt (2 * a)) ^ 2 := by
    funext t; unfold box; by_cases ht : t ∈ Icc (-a) a <;> simp [ht]
  rw [this, integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, div_pow, Real.sq_sqrt (by linarith)]
  field_simp; ring

/-- `f(0) − f(u) ≤ c²u` for the box: the shifted box differs from it on two intervals of length `u`. -/
theorem box_autocorr_diff_le {a : ℝ} {u : ℝ} (hu : 0 < u) :
    autocorr (box a) 0 - autocorr (box a) u ≤ (1 / Real.sqrt (2 * a)) ^ 2 * u := by
  set c := 1 / Real.sqrt (2 * a) with hc
  have hb := box_memLp a
  rw [show autocorr (box a) 0 - autocorr (box a) u
      = normSq (fun t => box a t - box a (t + u)) / 2 by
    rw [normSq_sub_shift hb u]; ring]
  set B : ℝ → ℝ := fun t => c ^ 2 * ((Icc (a - u) a).indicator 1 t
    + (Icc (-a - u) (-a)).indicator 1 t) with hB
  have hBint : Integrable B := by
    refine ((integrable_indicator_iff measurableSet_Icc).2 ?_).add
      ((integrable_indicator_iff measurableSet_Icc).2 ?_) |>.const_mul (c ^ 2)
    · exact integrableOn_const (measure_Icc_lt_top.ne)
    · exact integrableOn_const (measure_Icc_lt_top.ne)
  have hpt : ∀ t, (box a t - box a (t + u)) ^ 2 ≤ B t := by
    intro t
    simp only [hB, box_apply, Set.indicator_apply, Set.mem_Icc, Pi.one_apply]
    rw [← hc]
    by_cases h1 : |t| ≤ a <;> by_cases h2 : |t + u| ≤ a
    · simp only [h1, h2, ite_true, sub_self]
      have := sq_nonneg c
      split_ifs <;> nlinarith
    · simp only [h1, h2, ite_true, ite_false, sub_zero]
      have ht : a - u ≤ t ∧ t ≤ a := by
        rw [abs_le] at h1; rw [not_le, lt_abs] at h2
        constructor
        · rcases h2 with h2 | h2 <;> linarith
        · exact h1.2
      simp only [ht, and_self, ite_true]
      split_ifs <;> nlinarith [sq_nonneg c]
    · simp only [h1, h2, ite_true, ite_false, zero_sub, neg_sq]
      have ht : -a - u ≤ t ∧ t ≤ -a := by
        rw [abs_le] at h2; rw [not_le, lt_abs] at h1
        constructor
        · linarith [h2.1]
        · rcases h1 with h1 | h1
          · linarith [h2.2]
          · linarith
      simp only [ht, and_self, ite_true]
      split_ifs <;> nlinarith [sq_nonneg c]
    · simp only [h1, h2, ite_false, sub_self]
      have := sq_nonneg c
      split_ifs <;> nlinarith
  have hle : normSq (fun t => box a t - box a (t + u)) ≤ ∫ t, B t :=
    integral_mono ((hb.sub (memLp_shift hb u)).integrable_sq) hBint hpt
  have hBv : ∫ t, B t = c ^ 2 * (2 * u) := by
    rw [hB, integral_const_mul, integral_add ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const measure_Icc_lt_top.ne))
      ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)),
      integral_indicator_one measurableSet_Icc, integral_indicator_one measurableSet_Icc,
      Measure.real, Measure.real, Real.volume_Icc, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hBv] at hle
  linarith

/-- `u·e^{u/2}/sinh u ≤ 16e^{−u/4}` for `u > 0`. -/
theorem u_archK_le {u : ℝ} (hu : 0 < u) :
    u * (Real.exp (u / 2) / Real.sinh u) ≤ 16 * Real.exp (-(1 / 4) * u) := by
  have hsh : 0 < Real.sinh u := Real.sinh_pos_iff.2 hu
  rw [← mul_div_assoc, div_le_iff₀ hsh]
  have e1 : Real.exp (u / 2) = Real.exp (-(1 / 4) * u) * Real.exp (3 / 4 * u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1]
  have hE := Real.exp_pos (-(1 / 4) * u)
  suffices h : u * Real.exp (3 / 4 * u) ≤ 16 * Real.sinh u by nlinarith
  rcases le_or_gt u 1 with h1 | h1
  · have hs : u ≤ Real.sinh u := Real.self_le_sinh_iff.2 hu.le
    have : Real.exp (3 / 4 * u) ≤ 16 := by
      calc Real.exp (3 / 4 * u) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
        _ ≤ 16 := by have := Real.exp_one_lt_d9; linarith
    nlinarith
  · -- `sinh u ≥ e^u/4` and `u ≤ 4e^{u/4}`
    have hs : Real.exp u / 4 ≤ Real.sinh u := by
      rw [Real.sinh_eq]
      have : Real.exp (-u) ≤ Real.exp u / 2 := by
        have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
        have h3 : 2 ≤ Real.exp u * Real.exp u := by
          rw [← Real.exp_add]
          have := Real.add_one_le_exp (u + u); linarith
        nlinarith [Real.exp_pos u, Real.exp_pos (-u)]
      linarith
    have hl : u ≤ 4 * Real.exp (1 / 4 * u) := by
      have := Real.add_one_le_exp (1 / 4 * u); linarith
    have e2 : Real.exp u = Real.exp (3 / 4 * u) * Real.exp (1 / 4 * u) := by
      rw [← Real.exp_add]; congr 1; ring
    have := Real.exp_pos (3 / 4 * u)
    nlinarith [mul_le_mul_of_nonneg_left hl this.le]

theorem box_probe (a : ℝ) : Probe a (box a) := by
  refine ⟨fun u => by rw [box_apply, box_apply, abs_neg], fun u hu => by
    rw [box_apply]; simp [not_le.2 hu], box_memLp a, ?_⟩
  set c := 1 / Real.sqrt (2 * a)
  have hm : AEStronglyMeasurable (archIntegrand (box a)) (volume.restrict (Ioi 0)) := by
    have h1 := (autocorr_stronglyMeasurable (box_measurable a)).measurable
    have : Measurable (archIntegrand (box a)) := by
      unfold archIntegrand
      exact ((measurable_const.sub h1).mul
        ((Real.measurable_exp.comp (measurable_id.div_const 2)).div Real.measurable_sinh))
    exact this.aestronglyMeasurable
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    (c ^ 2 * 16)) hm ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
  have hu0 : 0 < u := hu
  have hK : 0 < Real.exp (u / 2) / Real.sinh u :=
    div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu0)
  rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg (box_memLp a) hu0)]
  unfold archIntegrand
  calc (autocorr (box a) 0 - autocorr (box a) u) * (Real.exp (u / 2) / Real.sinh u)
      ≤ (c ^ 2 * u) * (Real.exp (u / 2) / Real.sinh u) :=
        mul_le_mul_of_nonneg_right (box_autocorr_diff_le hu0) hK.le
    _ = c ^ 2 * (u * (Real.exp (u / 2) / Real.sinh u)) := by ring
    _ ≤ c ^ 2 * (16 * Real.exp (-(1 / 4) * u)) :=
        mul_le_mul_of_nonneg_left (u_archK_le hu0) (sq_nonneg c)
    _ = c ^ 2 * 16 * Real.exp (-(1 / 4) * u) := by ring

/-! ## The minimiser -/

/-- The non-archimedean part of `Q`: the pole, constant and prime terms. -/
def nonArch (a : ℝ) (g : ℝ → ℝ) : ℝ :=
  2 * poleR g a ^ 2 + ((Complex.digamma (1 / 4)).re - Real.log π) * normSq g
    - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * autocorr g (Real.log n)

theorem weilQ_eq_nonArch_add (a : ℝ) (g : ℝ → ℝ) : weilQ a g = nonArch a g + archE g := by
  unfold weilQ nonArch archE; ring

/-- The pole weight `1_{(−a, a]}·e^{−u/2}`: `ĝ(i/2) = ∫ g·w`. -/
def poleW (a : ℝ) : ℝ → ℝ := Set.indicator (Ioc (-a) a) fun u => Real.exp (-(u / 2))

theorem poleW_memLp (a : ℝ) : MemLp (poleW a) 2 volume :=
  memLp_indicator_of_continuous (by fun_prop) measurableSet_Ioc measure_Ioc_lt_top.ne
    (C := Real.exp (a / 2)) fun x hx => by
      rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (by linarith [hx.1])

theorem poleR_eq {a : ℝ} (ha : 0 ≤ a) (g : ℝ → ℝ) : poleR g a = ∫ t, g t * poleW a t := by
  unfold poleR poleW
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_indicator measurableSet_Ioc]
  congr 1; funext t
  by_cases ht : t ∈ Ioc (-a) a <;> simp [ht]

theorem normSq_eq_mul (g : ℝ → ℝ) : normSq g = ∫ t, g t * g t := by
  unfold normSq; congr 1; funext t; ring

/-- **A ground state of Weil's form exists at every support `δ = 2a > 0`.** -/
theorem exists_groundState {a : ℝ} (ha : 0 < a) : ∃ g, IsGroundState a g := by
  set Sv : Set ℝ := {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ weilQ a h = q} with hSv
  have hne : Sv.Nonempty := ⟨_, box a, box_probe a, normSq_box ha, rfl⟩
  have hbdd : BddBelow Sv := by
    refine ⟨weilConst - 2 * primeWeight a, ?_⟩
    rintro q ⟨h, hp, hn, rfl⟩
    have := weilQ_ge hp; rwa [hn, mul_one] at this
  obtain ⟨q, hqa, hq, hqS⟩ := exists_seq_tendsto_sInf hne hbdd
  choose h hp hn hQ using hqS
  set lam := sInf Sv with hlam
  -- the non-archimedean part is bounded below, so the archimedean energy is bounded above
  have hNA : ∀ g, Probe a g → normSq g = 1 → weilConst - 2 * primeWeight a ≤ nonArch a g := by
    intro g hpg hng
    have hpole : 0 ≤ 2 * poleR g a ^ 2 := by positivity
    have hprime := (le_abs_self _).trans (abs_prime_sum_le hpg)
    unfold nonArch weilConst
    rw [hng] at hprime ⊢
    linarith
  have hC : ∀ j, archE (h j) ≤ q 0 - (weilConst - 2 * primeWeight a) := by
    intro j
    have e := weilQ_eq_nonArch_add a (h j)
    have := hNA (h j) (hp j) (hn j)
    have hqj : q j ≤ q 0 := hqa (Nat.zero_le j)
    rw [hQ j] at e
    linarith
  obtain ⟨φ, hφ, G, hG, hlim⟩ := exists_convergent_subseq ha hp (B := 1) (fun j => (hn j).le) hC
  set G' := symCut a G with hG'def
  have hG' : MemLp G' 2 volume := memLp_symCut a hG
  have hlim' : Tendsto (fun j => normSq (fun t => h (φ j) t - G' t)) atTop (𝓝 0) :=
    squeeze_zero (fun j => integral_nonneg fun t => sq_nonneg _)
      (fun j => normSq_sub_symCut_le (hp (φ j)) hG) hlim
  have hmem : ∀ j, MemLp (h (φ j)) 2 volume := fun j => (hp (φ j)).memL2
  -- continuity of the non-archimedean terms
  have hnorm : Tendsto (fun j => normSq (h (φ j))) atTop (𝓝 (normSq G')) := by
    simp_rw [normSq_eq_mul]
    exact tendsto_integral_mul hmem hmem hG' hG' hlim' hlim'
  have hnormG : normSq G' = 1 := by
    have h1 : Tendsto (fun j => normSq (h (φ j))) atTop (𝓝 1) := by
      simp only [hn]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hnorm h1
  have hw0 : Tendsto (fun _ : ℕ => normSq (fun t => poleW a t - poleW a t)) atTop (𝓝 0) := by
    simp only [sub_self]; simp [normSq]
  have hpoleT : Tendsto (fun j => poleR (h (φ j)) a) atTop (𝓝 (poleR G' a)) := by
    simp_rw [poleR_eq ha.le]
    exact tendsto_integral_mul hmem (fun _ => poleW_memLp a) hG' (poleW_memLp a) hlim' hw0
  have hauto : ∀ u, Tendsto (fun j => autocorr (h (φ j)) u) atTop (𝓝 (autocorr G' u)) := by
    intro u
    have hsh : ∀ j, normSq (fun t => h (φ j) (t + u) - G' (t + u))
        = normSq (fun t => h (φ j) t - G' t) :=
      fun j => normSq_shift (fun t => h (φ j) t - G' t) u
    unfold autocorr
    exact tendsto_integral_mul hmem (fun j => memLp_shift (hmem j) u) hG' (memLp_shift hG' u)
      hlim' (hlim'.congr fun j => (hsh j).symm)
  have hsuppG' : ∀ u, a < |u| → G' u = 0 := symCut_supp a G
  have hprimeT : Tendsto
      (fun j => ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n
        * autocorr (h (φ j)) (Real.log n)) atTop
      (𝓝 (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * autocorr G' (Real.log n))) := by
    have e1 : ∀ j, (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n
        * autocorr (h (φ j)) (Real.log n))
        = ∑ n ∈ Finset.range (primeCut a), ArithmeticFunction.vonMangoldt n / Real.sqrt n
          * autocorr (h (φ j)) (Real.log n) := fun j => prime_sum_eq (hp (φ j)).supp
    simp_rw [e1]
    rw [prime_sum_eq hsuppG']
    exact tendsto_finsetSum _ fun n _ => (hauto _).const_mul _
  have hnonArch : Tendsto (fun j => nonArch a (h (φ j))) atTop (𝓝 (nonArch a G')) := by
    unfold nonArch
    exact (((hpoleT.pow 2).const_mul 2).add (hnorm.const_mul _)).sub (hprimeT.const_mul 2)
  -- the archimedean energies converge to `λ − nonArch(G')`
  have hqφ : Tendsto (fun j => q (φ j)) atTop (𝓝 lam) := hq.comp hφ.tendsto_atTop
  have hA : Tendsto (fun j => archE (h (φ j))) atTop (𝓝 (lam - nonArch a G')) := by
    have e : ∀ j, archE (h (φ j)) = q (φ j) - nonArch a (h (φ j)) := by
      intro j; rw [← hQ (φ j), weilQ_eq_nonArch_add]; ring
    simp_rw [e]
    exact hqφ.sub hnonArch
  -- Fatou: the limit's archimedean integral converges and is at most the limit
  obtain ⟨hint, hle⟩ := fatou_real measurableSet_Ioi
    (f := fun j => archIntegrand (h (φ j))) (F := archIntegrand G')
    (fun j => (hp (φ j)).arch) (fun j u hu => archIntegrand_nonneg (hmem j) hu)
    (fun u _ => by
      unfold archIntegrand
      exact ((hauto 0).sub (hauto u)).mul_const _) hA
  have hPG : Probe a G' := ⟨symCut_even a G, hsuppG', hG', hint⟩
  refine ⟨G', hPG, hnormG, fun h' hp' hn' => ?_⟩
  have hQG : weilQ a G' ≤ lam := by
    rw [weilQ_eq_nonArch_add]; unfold archE; linarith
  exact hQG.trans (csInf_le hbdd ⟨h', hp', hn', rfl⟩)

/-- Ground states at every support of a sequence `a_n > 0`: the family the chain of
`rh_of_groundStates_dodging` quantifies over is non-empty. -/
theorem exists_groundStates {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) :
    ∃ g : ℕ → ℝ → ℝ, ∀ n, IsGroundState (a n) (g n) :=
  ⟨fun n => (exists_groundState (ha n)).choose, fun n => (exists_groundState (ha n)).choose_spec⟩

end Pilot1ca

#print axioms Pilot1ca.tendsto_integral_mul
#print axioms Pilot1ca.normSq_sub_symCut_le
#print axioms Pilot1ca.fatou_real
#print axioms Pilot1ca.normSq_box
#print axioms Pilot1ca.box_probe
#print axioms Pilot1ca.exists_groundState
#print axioms Pilot1ca.exists_groundStates
