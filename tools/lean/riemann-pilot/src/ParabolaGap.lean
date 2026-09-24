import Mathlib
import FourierGap

/-! # Pushing the certified gap to `a = 0.36` with a parabola trial

Round 20 compared every probe orthogonal to `w` against the box. Its energy overshoots `λ₁` by
about `0.19` near `a = 0.35`. The parabola `g = C(1 − t²/a²)` is nearly optimal (within `0.01` of
`λ₁` numerically), and its autocorrelation is an explicit polynomial:
`f(u) = (2a − u)³(4a² + 6au + u²)/(32a⁵)` on `[0, 2a]`. With `K ≤ 1/u + ½` its near-field energy is
`≤ 31/30 + 7a/12`, and its pole term is `≤ (10/3)a(1 + a²/40 + a⁴/3584)²`.

On the segment `0.35 ≤ a ≤ 0.36` the round-20 lower bound (five modes, tail level `τ = 2.7` over six
certified `Cin` levels, prime defect `≤ 0.06026|n|`) beats the parabola by `1/50`. Result: `λ_⊥ ≥ λ₁ + 1/50` and
a unique ground state of `Q` for every `0 < a ≤ 0.36`.

This is the reach of the cos-free method: past `a ≈ 0.363` the prime `n = 2`'s defects in modes
`k ≈ 10–40` pull the tail level below what the low modes need (see the README's frontier map).
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## A. The parabola trial `g = C(1 − t²/a²)` on `[−a, a]` -/

def parC (a : ℝ) : ℝ := Real.sqrt (15 / (16 * a))

def par (a : ℝ) : ℝ → ℝ := (Icc (-a) a).indicator fun t => parC a * (1 - t ^ 2 / a ^ 2)

theorem par_apply (a t : ℝ) : par a t = if |t| ≤ a then parC a * (1 - t ^ 2 / a ^ 2) else 0 := by
  unfold par; simp [Set.indicator_apply, abs_le]

theorem parC_sq {a : ℝ} (ha : 0 < a) : parC a ^ 2 = 15 / (16 * a) := by
  unfold parC; rw [Real.sq_sqrt (by positivity)]

theorem parC_nonneg (a : ℝ) : 0 ≤ parC a := Real.sqrt_nonneg _

theorem par_nonneg {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 ≤ par a t := by
  rw [par_apply]; split_ifs with h
  · have ht : t ^ 2 ≤ a ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    have : t ^ 2 / a ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact ht
    exact mul_nonneg (parC_nonneg a) (by linarith)
  · exact le_rfl

theorem par_measurable (a : ℝ) : Measurable (par a) :=
  (Measurable.indicator (by fun_prop) measurableSet_Icc)

theorem par_memLp (a : ℝ) : MemLp (par a) 2 volume := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -a) (b := a)).exists_bound_of_continuousOn
    (show Continuous (fun t : ℝ => parC a * (1 - t ^ 2 / a ^ 2)) by fun_prop).continuousOn
  exact memLp_indicator_of_continuous (by fun_prop) measurableSet_Icc measure_Icc_lt_top.ne
    (C := C) fun x hx => by simpa [Real.norm_eq_abs] using hC x hx

/-- `∫_{α}^{β} (c₀ + c₁t + c₂t² + c₃t³ + c₄t⁴)`. -/
theorem integral_quartic (α β c₀ c₁ c₂ c₃ c₄ : ℝ) :
    (∫ t in α..β, (c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4))
      = c₀ * (β - α) + c₁ * (β ^ 2 - α ^ 2) / 2 + c₂ * (β ^ 3 - α ^ 3) / 3
        + c₃ * (β ^ 4 - α ^ 4) / 4 + c₄ * (β ^ 5 - α ^ 5) / 5 := by
  have i0 : IntervalIntegrable (fun _ : ℝ => c₀) volume α β := intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => c₁ * t) volume α β := (by fun_prop : Continuous _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t : ℝ => c₂ * t ^ 2) volume α β := (by fun_prop : Continuous _).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun t : ℝ => c₃ * t ^ 3) volume α β := (by fun_prop : Continuous _).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun t : ℝ => c₄ * t ^ 4) volume α β := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h1 : (∫ t in α..β, c₁ * t) = c₁ * (β ^ 2 - α ^ 2) / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rw [intervalIntegral.integral_add (((i0.add i1).add i2).add i3) i4,
    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2, intervalIntegral.integral_add i0 i1]
  rw [h1]
  simp only [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul,
    integral_pow]
  ring

theorem normSq_par {a : ℝ} (ha : 0 < a) : normSq (par a) = 1 := by
  unfold normSq
  have e : (fun t => par a t ^ 2) = (Icc (-a) a).indicator fun t => (parC a * (1 - t ^ 2 / a ^ 2)) ^ 2 := by
    funext t; unfold par; by_cases ht : t ∈ Icc (-a) a <;> simp [ht]
  rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have e2 : (fun t => (parC a * (1 - t ^ 2 / a ^ 2)) ^ 2)
      = fun t => parC a ^ 2 + 0 * t + (-2 * parC a ^ 2 / a ^ 2) * t ^ 2 + 0 * t ^ 3
        + (parC a ^ 2 / a ^ 4) * t ^ 4 := by
    funext t; field_simp; ring
  rw [e2, integral_quartic, parC_sq ha]
  field_simp; ring

/-- **The autocorrelation of the parabola**: `f(u) = (2a − u)³(4a² + 6au + u²)/(32a⁵)` on `[0, 2a]`. -/
theorem autocorr_par {a : ℝ} (ha : 0 < a) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 2 * a) :
    autocorr (par a) u = (2 * a - u) ^ 3 * (4 * a ^ 2 + 6 * a * u + u ^ 2) / (32 * a ^ 5) := by
  unfold autocorr
  set p : ℝ → ℝ := fun t => parC a ^ 2 * ((1 - t ^ 2 / a ^ 2) * (1 - (t + u) ^ 2 / a ^ 2))
  have e : (fun t => par a t * par a (t + u)) = (Icc (-a) (a - u)).indicator p := by
    funext t
    rw [par_apply, par_apply]
    by_cases h1 : t ∈ Icc (-a) (a - u)
    · have ha1 : |t| ≤ a := abs_le.2 ⟨h1.1, by linarith [h1.2]⟩
      have ha2 : |t + u| ≤ a := abs_le.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
      simp only [ha1, ha2, ite_true, Set.indicator_of_mem h1, p]; ring
    · rw [Set.indicator_of_notMem h1]
      simp only [mem_Icc, not_and_or, not_le] at h1
      rcases h1 with h1 | h1
      · have : ¬ |t| ≤ a := by rw [not_le, lt_abs]; right; linarith
        simp [this]
      · have : ¬ |t + u| ≤ a := by rw [not_le, lt_abs]; left; linarith
        simp [this]
  rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have e2 : p = fun t => (parC a ^ 2 * (1 - u ^ 2 / a ^ 2)) + (parC a ^ 2 * (-2 * u / a ^ 2)) * t
      + (parC a ^ 2 * ((u ^ 2 - 2 * a ^ 2) / a ^ 4)) * t ^ 2 + (parC a ^ 2 * (2 * u / a ^ 4)) * t ^ 3
      + (parC a ^ 2 / a ^ 4) * t ^ 4 := by
    funext t; simp only [p]; field_simp; ring
  rw [e2, integral_quartic, parC_sq ha]
  field_simp; ring

theorem autocorr_par_zero_gt {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 2 * a < u) : autocorr (par a) u = 0 :=
  autocorr_eq_zero (fun v hv => by
      rw [par_apply]; split_ifs with h
      · exact absurd h (not_le.2 hv)
      · rfl)
    (by rw [abs_of_pos (by linarith)]; exact hu)

theorem par_autocorr_diff_le {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 0 < u) :
    autocorr (par a) 0 - autocorr (par a) u ≤ 3 / a * u := by
  rw [autocorr_zero, normSq_par ha]
  rcases le_or_gt u (2 * a) with h | h
  · rw [autocorr_par ha hu.le h]
    set v := u / a with hv
    have hv0 : 0 < v := by positivity
    have hv2 : v ≤ 2 := by rw [hv, div_le_iff₀ ha]; linarith
    have key : 1 - (2 * a - u) ^ 3 * (4 * a ^ 2 + 6 * a * u + u ^ 2) / (32 * a ^ 5)
        = u * ((5 * v / 4 - 5 * v ^ 2 / 8 + v ^ 4 / 32) / a) := by
      rw [hv]; field_simp; ring
    rw [key, show 3 / a * u = u * (3 / a) by ring]
    apply mul_le_mul_of_nonneg_left _ hu.le
    apply div_le_div_of_nonneg_right _ ha.le
    nlinarith [pow_le_pow_left₀ hv0.le hv2 4, sq_nonneg v]
  · rw [autocorr_par_zero_gt ha h, sub_zero, div_mul_eq_mul_div, le_div_iff₀ ha]; nlinarith

theorem par_probe {a : ℝ} (ha : 0 < a) : Probe a (par a) := by
  refine ⟨fun u => by rw [par_apply, par_apply, abs_neg]; ring_nf, fun u hu => by
    rw [par_apply]; simp [not_le.2 hu], par_memLp a, ?_⟩
  have hm : AEStronglyMeasurable (archIntegrand (par a)) (volume.restrict (Ioi 0)) := by
    have h1 := (autocorr_stronglyMeasurable (par_measurable a)).measurable
    have : Measurable (archIntegrand (par a)) := by
      unfold archIntegrand
      exact ((measurable_const.sub h1).mul
        ((Real.measurable_exp.comp (measurable_id.div_const 2)).div Real.measurable_sinh))
    exact this.aestronglyMeasurable
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    (3 / a * 16)) hm ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
  have hu0 : 0 < u := hu
  have hK : 0 < Real.exp (u / 2) / Real.sinh u :=
    div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu0)
  rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg (par_memLp a) hu0)]
  unfold archIntegrand
  calc (autocorr (par a) 0 - autocorr (par a) u) * (Real.exp (u / 2) / Real.sinh u)
      ≤ (3 / a * u) * (Real.exp (u / 2) / Real.sinh u) :=
        mul_le_mul_of_nonneg_right (par_autocorr_diff_le ha hu0) hK.le
    _ = 3 / a * (u * (Real.exp (u / 2) / Real.sinh u)) := by ring
    _ ≤ 3 / a * (16 * Real.exp (-(1 / 4) * u)) :=
        mul_le_mul_of_nonneg_left (u_archK_le hu0) (by positivity)
    _ = 3 / a * 16 * Real.exp (-(1 / 4) * u) := by ring


theorem integral_mono5 (α β c : ℝ) : (∫ t in α..β, c * t ^ 5) = c * (β ^ 6 - α ^ 6) / 6 := by
  rw [intervalIntegral.integral_const_mul, integral_pow]; ring

theorem integral_mono6 (α β c : ℝ) : (∫ t in α..β, c * t ^ 6) = c * (β ^ 7 - α ^ 7) / 7 := by
  rw [intervalIntegral.integral_const_mul, integral_pow]; ring

/-- **The parabola's near-field energy**: `∫_{(0,2a]} A_par ≤ 31/30 + 7a/12`. -/
theorem nearField_par_le {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioc 0 (2 * a), archIntegrand (par a) u) ≤ 31 / 30 + 7 * a / 12 := by
  set P : ℝ → ℝ := fun u => (0 + 5 / (4 * a ^ 2) * u + (5 / (8 * a ^ 2) - 5 / (8 * a ^ 3)) * u ^ 2
    + (-(5 / (16 * a ^ 3))) * u ^ 3 + 1 / (32 * a ^ 5) * u ^ 4) + 1 / (64 * a ^ 5) * u ^ 5 with hP
  have hpt : ∀ u ∈ Ioc 0 (2 * a), archIntegrand (par a) u ≤ P u := by
    intro u hu
    have hK := kerK_le' hu.1
    have hf1 : autocorr (par a) u ≤ 1 := by
      have := (le_abs_self _).trans (abs_autocorr_le (par_memLp a) u); rwa [normSq_par ha] at this
    have e : archIntegrand (par a) u = (1 - autocorr (par a) u) * kerK u := by
      unfold archIntegrand kerK; rw [autocorr_zero, normSq_par ha]
    rw [e]
    refine (mul_le_mul_of_nonneg_left hK (by linarith)).trans (le_of_eq ?_)
    rw [autocorr_par ha hu.1.le hu.2, hP]
    have := hu.1.ne'
    field_simp; ring
  have hc : Continuous P := by rw [hP]; fun_prop
  have hmono := setIntegral_mono_on ((par_probe ha).arch.mono_set Ioc_subset_Ioi_self)
    hc.integrableOn_Ioc measurableSet_Ioc hpt
  have hR : (∫ u in Ioc 0 (2 * a), P u) = 31 / 30 + 7 * a / 12 := by
    rw [← intervalIntegral.integral_of_le (by linarith), hP,
      intervalIntegral.integral_add ((by fun_prop : Continuous _).intervalIntegrable _ _)
        ((by fun_prop : Continuous _).intervalIntegrable _ _),
      integral_quartic, integral_mono5]
    field_simp; ring
  linarith

/-- The pole value of the parabola is in `[0, C(4a/3 + a³/30 + a⁵/2688)]`. -/
theorem poleR_par_le {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    0 ≤ poleR (par a) a ∧ poleR (par a) a ≤ parC a * (4 * a / 3 + a ^ 3 / 30 + a ^ 5 / 2688) := by
  set h : ℝ → ℝ := fun u => parC a * (1 - u ^ 2 / a ^ 2)
  have hp : poleR (par a) a = ∫ u in (-a)..a, h u * Real.exp (-(u / 2)) := by
    unfold poleR
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith)] at hu
    simp only [par_apply, abs_le.2 ⟨hu.1, hu.2⟩, ite_true, h]
  have hh0 : ∀ u ∈ Icc (-a) a, 0 ≤ h u := by
    intro u hu
    have : u ^ 2 ≤ a ^ 2 := by nlinarith [hu.1, hu.2]
    have : u ^ 2 / a ^ 2 ≤ 1 := by rwa [div_le_one (by positivity)]
    exact mul_nonneg (parC_nonneg a) (by linarith)
  -- symmetrise: `∫ h e^{−u/2} = ∫ h cosh(u/2)`
  have hsym : (∫ u in (-a)..a, h u * Real.exp (-(u / 2))) = ∫ u in (-a)..a, h u * Real.cosh (u / 2) := by
    have h1 := intervalIntegral.integral_comp_neg (a := -a) (b := a) (fun u => h u * Real.exp (-(u / 2)))
    rw [neg_neg] at h1
    have e1 : (fun u => h (-u) * Real.exp (-(-u / 2))) = fun u => h u * Real.exp (u / 2) := by
      funext u; simp only [h]; ring_nf
    rw [e1] at h1
    have i1 : IntervalIntegrable (fun u => h u * Real.exp (-(u / 2))) volume (-a) a :=
      (by fun_prop : Continuous _).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun u => h u * Real.exp (u / 2)) volume (-a) a :=
      (by fun_prop : Continuous _).intervalIntegrable _ _
    have e2 : (∫ u in (-a)..a, h u * Real.cosh (u / 2))
        = ((∫ u in (-a)..a, h u * Real.exp (u / 2)) + ∫ u in (-a)..a, h u * Real.exp (-(u / 2))) / 2 := by
      rw [← intervalIntegral.integral_add i2 i1, ← intervalIntegral.integral_div]
      refine intervalIntegral.integral_congr fun u _ => ?_
      rw [Real.cosh_eq]; ring
    rw [e2, h1]; ring
  rw [hp, hsym]
  have hlo : (0 : ℝ) ≤ ∫ u in (-a)..a, h u * Real.cosh (u / 2) :=
    intervalIntegral.integral_nonneg (by linarith) fun u hu =>
      mul_nonneg (hh0 u hu) (Real.cosh_pos _).le
  refine ⟨hlo, ?_⟩
  set B : ℝ → ℝ := fun u => parC a * ((1 + 0 * u + (1 / 8 - 1 / a ^ 2) * u ^ 2 + 0 * u ^ 3
      + (5 / 1536 - 1 / (8 * a ^ 2)) * u ^ 4) + (-(5 / (1536 * a ^ 2))) * u ^ 6) with hB
  have hmono := intervalIntegral.integral_mono_on (by linarith : -a ≤ a)
    ((by fun_prop : Continuous (fun u => h u * Real.cosh (u / 2))).intervalIntegrable (μ := volume) _ _)
    ((by rw [hB]; fun_prop : Continuous B).intervalIntegrable (μ := volume) _ _) (fun u hu => by
      have hc := cosh_le_taylor (y := u / 2) (by
        rw [abs_div, abs_two]; have := abs_le.2 ⟨hu.1, hu.2⟩; linarith)
      have e : B u = h u * (1 + (u / 2) ^ 2 / 2 + 5 * (u / 2) ^ 4 / 96) := by
        simp only [hB, h]; field_simp; ring
      rw [e]; exact mul_le_mul_of_nonneg_left hc (hh0 u hu))
  have hBv : (∫ u in (-a)..a, B u) = parC a * (4 * a / 3 + a ^ 3 / 30 + a ^ 5 / 2688) := by
    rw [hB, intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      ((by fun_prop : Continuous _).intervalIntegrable _ _)
      ((by fun_prop : Continuous _).intervalIntegrable _ _), integral_quartic, integral_mono6]
    field_simp; ring
  linarith

theorem pole_par_le {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    2 * poleR (par a) a ^ 2 ≤ 15 / (8 * a) * (4 * a / 3 + a ^ 3 / 30 + a ^ 5 / 2688) ^ 2 := by
  obtain ⟨h0, h1⟩ := poleR_par_le ha ha2
  have := pow_le_pow_left₀ h0 h1 2
  rw [mul_pow, parC_sq ha] at this
  have e : 15 / (8 * a) * (4 * a / 3 + a ^ 3 / 30 + a ^ 5 / 2688) ^ 2
      = 2 * (15 / (16 * a) * (4 * a / 3 + a ^ 3 / 30 + a ^ 5 / 2688) ^ 2) := by ring
  rw [e]; linarith

theorem autocorr_par_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ) : 0 ≤ autocorr (par a) u :=
  integral_nonneg fun t => mul_nonneg (par_nonneg ha t) (par_nonneg ha _)


/-! ## B. The segment `0.35 ≤ a ≤ 0.36` -/

theorem primeD_smallC {a : ℝ} (ha1 : 0.35 ≤ a) (ha2 : a ≤ 0.36) (n : ℤ) :
    primeD a (Real.log 2) n ≤ 0.06026 * |(n : ℝ)| := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have ha0 : 0 < a := by linarith
  refine (primeD_le ha0 n).trans ?_
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * a - Real.log 2), div_le_iff₀ (by linarith)]
  have hπ := Real.pi_lt_d6
  have hn0 := abs_nonneg (n : ℝ)
  have hε : 2 * a - Real.log 2 ≤ 0.0268528197 := by linarith
  have hε0 : 0 ≤ 2 * a - Real.log 2 := by linarith
  have h1 : π * |(n : ℝ)| * (2 * a - Real.log 2) ≤ 3.141593 * |(n : ℝ)| * 0.0268528197 := by
    have := mul_le_mul (mul_le_mul_of_nonneg_right hπ.le hn0) hε hε0 (by positivity)
    linarith
  nlinarith

theorem errK_le036 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.36) : errK a ≤ 0.0374 := by
  unfold errK
  have h2 : a ^ 2 ≤ 0.36 ^ 2 := pow_le_pow_left₀ ha.le ha2 2
  have h3 : a ^ 3 ≤ 0.36 ^ 3 := pow_le_pow_left₀ ha.le ha2 3
  have h4 : a ^ 4 ≤ 0.36 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have h5 : a ^ 5 ≤ 0.36 ^ 5 := pow_le_pow_left₀ ha.le ha2 5
  norm_num at h2 h3 h4 h5 ⊢; linarith

theorem tailC_pos {a : ℝ} (ha1 : 0.35 ≤ a) (ha2 : a ≤ 0.36) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 0.9803)
    {n : ℤ} (hn : 6 ≤ n) : 2.7 ≤ modeE a n - c * primeD a (Real.log 2) n := by
  have ha : 0 < a := by linarith
  have herr := errK_le036 ha ha2
  have hnr : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hD := primeD_smallC ha1 ha2 n
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at hD
  have br := fun (M N Cv : ℝ) (hM : 0 ≤ M) (hMn : M ≤ n) (hnN : (n : ℝ) ≤ N)
      (hcv : Cv ≤ Cin (M * π / 2)) =>
    tail_branch ha (by linarith) hc0 hn hM hMn hcv
      (hD.trans (mul_le_mul_of_nonneg_left hnN (by norm_num : (0 : ℝ) ≤ 0.06026)))
  rcases le_or_gt n 6 with h | h
  · have := br 6 6 2.7801 (by norm_num) hnr (by exact_mod_cast h)
      (by rw [show (6 : ℝ) * π / 2 = π * 6 / 2 by ring]; exact cin_val6)
    linarith
  rcases le_or_gt n 10 with h | h
  · have := br 7 10 3.033953 (by norm_num) (by exact_mod_cast (show (7 : ℤ) ≤ n by omega))
      (by exact_mod_cast h) (by rw [show (7 : ℝ) * π / 2 = 14 * π / 4 by ring]; exact cinH7)
    linarith
  rcases le_or_gt n 17 with h | h
  · have := br 11 17 3.453456 (by norm_num) (by exact_mod_cast (show (11 : ℤ) ≤ n by omega))
      (by exact_mod_cast h) (by rw [show (11 : ℝ) * π / 2 = 22 * π / 4 by ring]; exact cinH11)
    linarith
  rcases le_or_gt n 24 with h | h
  · have := br 18 24 3.886992 (by norm_num) (by exact_mod_cast (show (18 : ℤ) ≤ n by omega))
      (by exact_mod_cast h) (by rw [show (18 : ℝ) * π / 2 = 36 * π / 4 by ring]; exact cinH18)
    linarith
  rcases le_or_gt n 29 with h | h
  · have := br 25 29 4.191228 (by norm_num) (by exact_mod_cast (show (25 : ℤ) ≤ n by omega))
      (by exact_mod_cast h) (by rw [show (25 : ℝ) * π / 2 = 50 * π / 4 by ring]; exact cinH25)
    linarith
  · have := tail_branch ha (by linarith) hc0 hn (M := 30) (Cv := 4.398497) (by norm_num)
      (by exact_mod_cast (show (30 : ℤ) ≤ n by omega))
      (by rw [show (30 : ℝ) * π / 2 = 60 * π / 4 by ring]; exact cinH30)
      (primeD_le_two a (Real.log 2) n)
    linarith


theorem tailC_all {a : ℝ} (ha1 : 0.35 ≤ a) (ha2 : a ≤ 0.36) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 0.9803)
    (n : ℤ) (hn : n ∉ lowS) : 2.7 ≤ modeE a n - c * primeD a (Real.log 2) n := by
  rcases not_mem_lowS hn with h | h
  · exact tailC_pos ha1 ha2 hc0 hc h
  · have e := modeE_neg a (-n)
    have e2 := primeD_neg a (Real.log 2) (-n)
    rw [neg_neg] at e e2
    rw [e, e2]; exact tailC_pos ha1 ha2 hc0 hc (by omega)


theorem pm_leC1 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.36) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 1 ≤ (0.00323 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval1).trans (by norm_num)

theorem termC1 {a : ℝ} (ha1 : 0.35 ≤ a) (ha2 : a ≤ 0.36)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc1 : 0.98 ≤ c) :
    ((0.5408 : ℝ) + a * 0.36338 - errK a - c * (0.06026 * 1) - 2.7) * 0.00323
      ≤ (modeE a 1 - c * primeD a (Real.log 2) 1 - 2.7) * pm a g 1 := by
  have ha : 0 < a := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hD := primeD_smallC ha1 ha2 1
  rw [show |(((1 : ℤ) : ℝ))| = 1 by norm_num] at hD
  have h := term_mode ha (by linarith) (k := 1) (by norm_num) (Cv := 0.5408) (D := 0.36338)
    (X := c * (0.06026 * 1)) (Y := c * primeD a (Real.log 2) 1) (τ := 2.7) (P := 0.00323)
    (by simpa using cin_val1) dlo1 (mul_le_mul_of_nonneg_left hD hc0)
    (by linarith [errK_nonneg ha.le, mul_nonneg hc0 (show (0 : ℝ) ≤ 0.06026 * 1 by norm_num)])
    (pm_leC1 ha ha2 hp hn h0)
  linarith

theorem pm_leC2 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.36) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 2 ≤ (0.02547 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval2).trans (by norm_num)

theorem termC2 {a : ℝ} (ha1 : 0.35 ≤ a) (ha2 : a ≤ 0.36)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc1 : 0.98 ≤ c) :
    ((1.6214 : ℝ) + a * 1 - errK a - c * (0.06026 * 2) - 2.7) * 0.02547
      ≤ (modeE a 2 - c * primeD a (Real.log 2) 2 - 2.7) * pm a g 2 := by
  have ha : 0 < a := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hD := primeD_smallC ha1 ha2 2
  rw [show |(((2 : ℤ) : ℝ))| = 2 by norm_num] at hD
  have h := term_mode ha (by linarith) (k := 2) (by norm_num) (Cv := 1.6214) (D := 1)
    (X := c * (0.06026 * 2)) (Y := c * primeD a (Real.log 2) 2) (τ := 2.7) (P := 0.02547)
    (by simpa using cin_val2) dlo2 (mul_le_mul_of_nonneg_left hD hc0)
    (by linarith [errK_nonneg ha.le, mul_nonneg hc0 (show (0 : ℝ) ≤ 0.06026 * 2 by norm_num)])
    (pm_leC2 ha ha2 hp hn h0)
  linarith

theorem pm_leC3 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.36) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 3 ≤ (0.0799 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval3).trans (by norm_num)

theorem termC3 {a : ℝ} (ha1 : 0.35 ≤ a) (ha2 : a ≤ 0.36)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc1 : 0.98 ≤ c) :
    ((2.2965 : ℝ) + a * 1.212206 - errK a - c * (0.06026 * 3) - 2.7) * 0.0799
      ≤ (modeE a 3 - c * primeD a (Real.log 2) 3 - 2.7) * pm a g 3 := by
  have ha : 0 < a := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hD := primeD_smallC ha1 ha2 3
  rw [show |(((3 : ℤ) : ℝ))| = 3 by norm_num] at hD
  have h := term_mode ha (by linarith) (k := 3) (by norm_num) (Cv := 2.2965) (D := 1.212206)
    (X := c * (0.06026 * 3)) (Y := c * primeD a (Real.log 2) 3) (τ := 2.7) (P := 0.0799)
    (by simpa using cin_val3) dlo3 (mul_le_mul_of_nonneg_left hD hc0)
    (by linarith [errK_nonneg ha.le, mul_nonneg hc0 (show (0 : ℝ) ≤ 0.06026 * 3 by norm_num)])
    (pm_leC3 ha ha2 hp hn h0)
  linarith

theorem pm_leC4 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.36) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 4 ≤ (0.13125 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval4).trans (by norm_num)

theorem termC4 {a : ℝ} (ha1 : 0.35 ≤ a) (ha2 : a ≤ 0.36)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc1 : 0.98 ≤ c) :
    ((2.4081 : ℝ) + a * 1 - errK a - c * (0.06026 * 4) - 2.7) * 0.13125
      ≤ (modeE a 4 - c * primeD a (Real.log 2) 4 - 2.7) * pm a g 4 := by
  have ha : 0 < a := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hD := primeD_smallC ha1 ha2 4
  rw [show |(((4 : ℤ) : ℝ))| = 4 by norm_num] at hD
  have h := term_mode ha (by linarith) (k := 4) (by norm_num) (Cv := 2.4081) (D := 1)
    (X := c * (0.06026 * 4)) (Y := c * primeD a (Real.log 2) 4) (τ := 2.7) (P := 0.13125)
    (by simpa using cin_val4) dlo4 (mul_le_mul_of_nonneg_left hD hc0)
    (by linarith [errK_nonneg ha.le, mul_nonneg hc0 (show (0 : ℝ) ≤ 0.06026 * 4 by norm_num)])
    (pm_leC4 ha ha2 hp hn h0)
  linarith

theorem pm_leC5 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.36) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 5 ≤ (0.13951 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval5).trans (by norm_num)

theorem termC5 {a : ℝ} (ha1 : 0.35 ≤ a) (ha2 : a ≤ 0.36)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc1 : 0.98 ≤ c) :
    ((2.4848 : ℝ) + a * 0.872676 - errK a - c * (0.06026 * 5) - 2.7) * 0.13951
      ≤ (modeE a 5 - c * primeD a (Real.log 2) 5 - 2.7) * pm a g 5 := by
  have ha : 0 < a := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hD := primeD_smallC ha1 ha2 5
  rw [show |(((5 : ℤ) : ℝ))| = 5 by norm_num] at hD
  have h := term_mode ha (by linarith) (k := 5) (by norm_num) (Cv := 2.4848) (D := 0.872676)
    (X := c * (0.06026 * 5)) (Y := c * primeD a (Real.log 2) 5) (τ := 2.7) (P := 0.13951)
    (by simpa using cin_val5) dlo5 (mul_le_mul_of_nonneg_left hD hc0)
    (by linarith [errK_nonneg ha.le, mul_nonneg hc0 (show (0 : ℝ) ≤ 0.06026 * 5 by norm_num)])
    (pm_leC5 ha ha2 hp hn h0)
  linarith

theorem pole_par_lin {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.36) :
    15 / (8 * a) * (4 * a / 3 + a ^ 3 / 30 + a ^ 5 / 2688) ^ 2 ≤ 3.356 * a := by
  have e : 15 / (8 * a) * (4 * a / 3 + a ^ 3 / 30 + a ^ 5 / 2688) ^ 2
      = 10 / 3 * a * (1 + a ^ 2 / 40 + a ^ 4 / 3584) ^ 2 := by field_simp; ring
  rw [e]
  have h2 : a ^ 2 ≤ 0.36 ^ 2 := pow_le_pow_left₀ ha.le ha2 2
  have h4 : a ^ 4 ≤ 0.36 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have hx : 1 + a ^ 2 / 40 + a ^ 4 / 3584 ≤ 1.00327 := by norm_num at h2 h4 ⊢; linarith
  have hx0 : 0 ≤ 1 + a ^ 2 / 40 + a ^ 4 / 3584 := by positivity
  have := pow_le_pow_left₀ hx0 hx 2
  nlinarith

/-- **The gap on the segment `0.35 ≤ a ≤ 0.36`**, against the parabola trial. -/
theorem weilQ_perp_ge_seg {a : ℝ} (ha1 : 0.35 ≤ a) (ha2 : a ≤ 0.36)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) :
    weilQ a (par a) + 1 / 50 ≤ weilQ a g := by
  have ha : 0 < a := by linarith
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hlo : Real.log 2 ≤ 2 * a := by linarith
  set c := 2 * (Real.log 2 / Real.sqrt 2) with hcdef
  obtain ⟨-, -, hs1, hs2, -⟩ := num_atoms
  have hce : c = Real.sqrt 2 * Real.log 2 := by
    rw [hcdef]; field_simp; rw [Real.sq_sqrt (by norm_num)]
  have hc0 : 0 ≤ c := by positivity
  have hc : c ≤ 0.9803 := by rw [hce]; nlinarith
  have hc1 : 0.98 ≤ c := by rw [hce]; nlinarith
  have hQ : ∀ h, Probe a h → normSq h = 1 →
      weilQ a h = 2 * poleR h a ^ 2 + weilConst + archE h - c * autocorr h (Real.log 2) := by
    intro h hh hhn
    rw [weilQ_eq', primeS_eq_two (by linarith) hh, hhn, hcdef]; ring
  rw [hQ g hp hn, hQ _ (par_probe ha) (normSq_par ha), h0, archE_split ha hp hn,
    archE_split ha (par_probe ha) (normSq_par ha)]
  have hu0 : 0 ≤ Real.log 2 := by linarith
  have hE := energy_prime_trunc ha hp hn hu0 hlo hc0 lowS (tailC_all ha1 ha2 hc0 hc)
  have hsum : ∑ n ∈ lowS, (modeE a n - c * primeD a (Real.log 2) n - 2.7) * pm a g n
      = (modeE a 0 - c * primeD a (Real.log 2) 0 - 2.7) * pm a g 0
        + 2 * ((modeE a 1 - c * primeD a (Real.log 2) 1 - 2.7) * pm a g 1
          + (modeE a 2 - c * primeD a (Real.log 2) 2 - 2.7) * pm a g 2
          + (modeE a 3 - c * primeD a (Real.log 2) 3 - 2.7) * pm a g 3
          + (modeE a 4 - c * primeD a (Real.log 2) 4 - 2.7) * pm a g 4
          + (modeE a 5 - c * primeD a (Real.log 2) 5 - 2.7) * pm a g 5) :=
    sum_lowS_even fun k => by simp only [modeE_neg, primeD_neg, pm_neg ha hp]
  rw [hsum] at hE
  have h0t : (0 - 0 - 2.7) * (a ^ 4 / 240)
      ≤ (modeE a 0 - c * primeD a (Real.log 2) 0 - 2.7) * pm a g 0 := by
    rw [modeE_zero, show primeD a (Real.log 2) 0 = 0 by simp [primeD]]
    have := pm_zero_le ha (by linarith) hp hn h0
    nlinarith [pm_nonneg ha g 0]
  have t1 := termC1 ha1 ha2 hp hn h0 hc1
  have t2 := termC2 ha1 ha2 hp hn h0 hc1
  have t3 := termC3 ha1 ha2 hp hn h0 hc1
  have t4 := termC4 ha1 ha2 hp hn h0 hc1
  have t5 := termC5 ha1 ha2 hp hn h0 hc1
  have hB := nearField_par_le ha
  have hP := (pole_par_le ha (by linarith)).trans (pole_par_lin ha ha2)
  have hcf : 0 ≤ c * autocorr (par a) (Real.log 2) := mul_nonneg hc0 (autocorr_par_nonneg ha _)
  have herr := errK_le036 ha ha2
  have ha4 : a ^ 4 ≤ 0.36 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  linarith

/-- **Certified lower bound orthogonally to `w` for every `0 < a ≤ 0.36`**: `λ_⊥ ≥ λ₁ + 1/50`. -/
theorem weilQ0_perp_ge_036 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.36) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : lam a + 1 / 50 ≤ weilQ0 a g := by
  rcases le_or_gt a 0.35 with h | h
  · have := weilQ0_perp_ge_035 ha h hp hn h0; linarith
  · have hQ := weilQ_perp_ge_seg h.le ha2 hp hn h0
    have hQ0 : weilQ0 a g = weilQ a g := by unfold weilQ0; rw [h0]; ring
    have hlam := lam_le (par_probe ha) (normSq_par ha)
    rw [hQ0]; linarith

/-- **The ground state of `Q` is unique up to sign for every `0 < a ≤ 0.36`.** -/
theorem groundState_unique_036 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.36) {g h : ℝ → ℝ}
    (hg : IsGroundState a g) (hh : IsGroundState a h) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t := by
  refine groundState_unique ha (fun v hv hv0 => ?_) hg hh
  have h1 := weilQ0_perp_ge_036 ha ha2 hv.1 hv.2.1 hv0
  have h3 : weilQ0 a v = weilQ a v := by unfold weilQ0; rw [hv0]; ring
  have h2 : weilQ a v = lam a := by
    have := ((isGroundState_iff ha).1 hv).1.2; rw [this, hv.2.1, mul_one]
  linarith

end Pilot1ca

#print axioms Pilot1ca.normSq_par
#print axioms Pilot1ca.autocorr_par
#print axioms Pilot1ca.par_probe
#print axioms Pilot1ca.nearField_par_le
#print axioms Pilot1ca.poleR_par_le
#print axioms Pilot1ca.pole_par_le
#print axioms Pilot1ca.primeD_smallC
#print axioms Pilot1ca.tailC_all
#print axioms Pilot1ca.termC5
#print axioms Pilot1ca.weilQ_perp_ge_seg
#print axioms Pilot1ca.weilQ0_perp_ge_036
#print axioms Pilot1ca.groundState_unique_036
