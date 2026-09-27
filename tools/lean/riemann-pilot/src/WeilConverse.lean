import Mathlib
import ExplicitBridge

/-! # The converse: an off-line zero makes Weil's form negative somewhere (round 131)

Round 129 proved RH ⇒ `Q ≥ 0` at every support. This file proves the converse for a zero family
with finitely many off-line members.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## C1. Twin probes: `ĝ_λ(z) = 2cos(λz)ĝ₀(z)` -/

/-- The symmetrised translate `g₀(u − λ) + g₀(u + λ)`. -/
def twin (g₀ : ℝ → ℝ) (l : ℝ) (u : ℝ) : ℝ := g₀ (u - l) + g₀ (u + l)

theorem autocorr_shift (g : ℝ → ℝ) (c u : ℝ) : autocorr (fun t => g (t + c)) u = autocorr g u := by
  unfold autocorr
  have := integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun t => g t * g (t + u)) c
  rw [← this]; congr 1; funext t; ring_nf

theorem archIntegrand_shift (g : ℝ → ℝ) (c u : ℝ) :
    archIntegrand (fun t => g (t + c)) u = archIntegrand g u := by
  unfold archIntegrand; rw [autocorr_shift, autocorr_shift]

theorem twin_probe {b : ℝ} {g₀ : ℝ → ℝ} (hp : Probe b g₀) {l : ℝ} (hl : 0 ≤ l) :
    Probe (l + b) (twin g₀ l) := by
  have m1 : MemLp (fun t => g₀ (t + -l)) 2 volume := memLp_shift hp.memL2 (-l)
  have m2 : MemLp (fun t => g₀ (t + l)) 2 volume := memLp_shift hp.memL2 l
  refine ⟨fun u => ?_, fun u hu => ?_, ?_, ?_⟩
  · unfold twin
    rw [show -u - l = -(u + l) by ring, show -u + l = -(u - l) by ring, hp.even, hp.even, add_comm]
  · unfold twin
    have h1 : b < |u - l| := by
      have := abs_sub_abs_le_abs_sub u l; rw [abs_of_nonneg hl] at this; linarith
    have h2 : b < |u + l| := by
      have := abs_sub_abs_le_abs_sub u (-l); rw [abs_neg, abs_of_nonneg hl, sub_neg_eq_add] at this
      linarith
    rw [hp.supp _ h1, hp.supp _ h2, add_zero]
  · convert m1.add m2 using 1; funext t; simp [twin, sub_eq_add_neg]
  · have e : twin g₀ l = fun t => g₀ (t + -l) + g₀ (t + l) := by
      funext t; simp [twin, sub_eq_add_neg]
    rw [e]
    have m3 : MemLp (fun t => g₀ (t + -l) + g₀ (t + l)) 2 volume := m1.add m2
    refine Integrable.mono' ((hp.arch.const_mul 4)) (measurable_archIntegrand m3).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
    have hu' : (0 : ℝ) < u := hu
    rw [Real.norm_of_nonneg (archIntegrand_nonneg m3 hu')]
    have := archIntegrand_add_le m1 m2 hu'
    rw [archIntegrand_shift, archIntegrand_shift] at this
    linarith

theorem integrable_shift_exp {b : ℝ} {g₀ : ℝ → ℝ} (hp : Probe b g₀) (c : ℝ) (z : ℂ) :
    Integrable (fun u : ℝ => ((g₀ (u + c) : ℝ) : ℂ) * Complex.exp (Complex.I * z * u)) := by
  set R := b + |c|
  have hsupp : ∀ u, R < |u| → g₀ (u + c) = 0 := fun u hu => hp.supp _ (by
    have := abs_sub_abs_le_abs_sub u (-c); rw [sub_neg_eq_add, abs_neg] at this; linarith)
  have hon : IntegrableOn (fun u : ℝ => ((g₀ (u + c) : ℝ) : ℂ) * Complex.exp (Complex.I * z * u))
      (Icc (-R) R) := by
    have hi : Integrable (fun u => g₀ (u + c)) := by
      have := (probe_integrable hp).comp_add_right c; simpa using this
    exact (hi.ofReal.integrableOn).mul_continuousOn (by fun_prop) isCompact_Icc
  refine (integrableOn_iff_integrable_of_support_subset fun u hu => ?_).1 hon
  rw [Function.mem_support] at hu
  by_contra h
  have : R < |u| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
    · exact lt_of_lt_of_le h (le_abs_self u)
  exact hu (by rw [hsupp u this]; simp)

/-- **The twin transform**: `ĝ_λ(z) = 2cos(λz)·ĝ₀(z)`. -/
theorem ghatC_twin {b : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀) {l : ℝ} (hl : 0 ≤ l)
    (z : ℂ) : ghatC (twin g₀ l) (l + b) z = 2 * Complex.cos (l * z) * ghatC g₀ b z := by
  rw [ghatC_eq_integral (by linarith) (twin_probe hp hl).supp, ghatC_eq_integral hb hp.supp]
  have h1 := integrable_shift_exp hp (-l) z
  have h2 := integrable_shift_exp hp l z
  have e : (fun u : ℝ => ((twin g₀ l u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u))
      = fun u => ((g₀ (u + -l) : ℝ) : ℂ) * Complex.exp (Complex.I * z * u)
        + ((g₀ (u + l) : ℝ) : ℂ) * Complex.exp (Complex.I * z * u) := by
    funext u; simp only [twin, sub_eq_add_neg]; push_cast; ring
  rw [e, integral_add h1 h2]
  have s : ∀ c : ℝ, (∫ u : ℝ, ((g₀ (u + c) : ℝ) : ℂ) * Complex.exp (Complex.I * z * u))
      = Complex.exp (-(Complex.I * z * c)) * ∫ u : ℝ, ((g₀ u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u) := by
    intro c
    rw [← integral_const_mul]
    have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun u : ℝ => Complex.exp (-(Complex.I * z * c)) * (((g₀ u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u))) c
    rw [← this]; congr 1; funext u
    rw [mul_left_comm, ← Complex.exp_add]; push_cast; congr 2; ring
  rw [s, s, ← add_mul, Complex.cos]
  congr 1
  push_cast
  ring_nf

/-! ## C2. Exponential integrals on `[0, T]` against the weight `1 + cos(μx + θ)` -/

/-- `1/‖z‖` off `0`, and `0` at `0`. -/
def invB (z : ℂ) : ℝ := if z = 0 then 0 else 1 / ‖z‖

theorem invB_nonneg (z : ℂ) : 0 ≤ invB z := by unfold invB; split_ifs <;> positivity

/-- `∫_0^T e^{sx} dx` is `T` if `s = 0`, and has norm `≤ 2/‖s‖` if `Re s ≤ 0`. -/
theorem int_exp_bound {s : ℂ} (hs : s.re ≤ 0) {T : ℝ} (hT : 0 ≤ T) :
    ‖(∫ x in (0 : ℝ)..T, cexp (s * x)) - (if s = 0 then (T : ℂ) else 0)‖ ≤ 2 * invB s := by
  unfold invB
  split_ifs with h
  · subst h; simp
  · rw [integral_exp_mul_complex h, sub_zero, norm_div]
    have hb : ∀ x : ℝ, 0 ≤ x → ‖cexp (s * x)‖ ≤ 1 := fun x hx => by
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.2
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith
    have h0 := norm_sub_le (cexp (s * T)) (cexp (s * ((0 : ℝ) : ℂ)))
    have hs0 : 0 < ‖s‖ := norm_pos_iff.2 h
    rw [div_le_iff₀ hs0]
    have e : 2 * (1 / ‖s‖) * ‖s‖ = 2 := by field_simp
    rw [e]; linarith [hb T hT, hb 0 le_rfl]

/-- The weight `1 + cos(μx + θ) ≥ 0`. -/
def wt (μ θ x : ℝ) : ℝ := 1 + Real.cos (μ * x + θ)

theorem wt_nonneg (μ θ x : ℝ) : 0 ≤ wt μ θ x := by
  unfold wt; linarith [Real.neg_one_le_cos (μ * x + θ)]

/-- The part of `∫_0^T Re(c e^{sx})(1 + cos(μx + θ)) dx` that grows linearly in `T`, per unit `T`. -/
def mainT (c s : ℂ) (μ θ : ℝ) : ℝ :=
  (if s = 0 then c.re else 0)
  + (if s + μ * I = 0 then (c * cexp (θ * I) / 2).re else 0)
  + (if s - μ * I = 0 then (c * cexp (-(θ * I)) / 2).re else 0)

/-- The bounded remainder. -/
def errT (c s : ℂ) (μ : ℝ) : ℝ := ‖c‖ * (2 * invB s + invB (s + μ * I) + invB (s - μ * I))

theorem wt_identity (c s : ℂ) (μ θ x : ℝ) :
    (c * cexp (s * x)).re * wt μ θ x
      = (c * cexp (s * x) + c * cexp (θ * I) / 2 * cexp ((s + μ * I) * x)
          + c * cexp (-(θ * I)) / 2 * cexp ((s - μ * I) * x)).re := by
  have h1 : cexp (θ * I) * cexp ((s + μ * I) * x) = cexp (s * x) * cexp ((μ * x + θ : ℝ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : cexp (-(θ * I)) * cexp ((s - μ * I) * x)
      = cexp (s * x) * cexp (-((μ * x + θ : ℝ) * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have hw : ((wt μ θ x : ℝ) : ℂ) = 1 + (cexp ((μ * x + θ : ℝ) * I) + cexp (-((μ * x + θ : ℝ) * I))) / 2 := by
    unfold wt; push_cast; rw [Complex.cos, neg_mul]
  rw [← Complex.re_mul_ofReal, hw]
  congr 1
  calc c * cexp (s * x) * (1 + (cexp ((μ * x + θ : ℝ) * I) + cexp (-((μ * x + θ : ℝ) * I))) / 2)
      = c * cexp (s * x) + c / 2 * (cexp (s * x) * cexp ((μ * x + θ : ℝ) * I))
        + c / 2 * (cexp (s * x) * cexp (-((μ * x + θ : ℝ) * I))) := by ring
    _ = _ := by rw [← h1, ← h2]; ring

/-- **The weighted integral**: `|∫_0^T Re(c e^{sx})(1 + cos(μx + θ)) dx − T·main| ≤ err` for
`Re s ≤ 0`. -/
theorem int_wt (c s : ℂ) (μ θ : ℝ) (hs : s.re ≤ 0) {T : ℝ} (hT : 0 ≤ T) :
    |(∫ x in (0 : ℝ)..T, (c * cexp (s * x)).re * wt μ θ x) - T * mainT c s μ θ| ≤ errT c s μ := by
  have hc : ∀ u : ℂ, IntervalIntegrable (fun x : ℝ => cexp (u * x)) volume 0 T :=
    fun u => (by fun_prop : Continuous fun x : ℝ => cexp (u * x)).intervalIntegrable _ _
  simp_rw [wt_identity c s μ θ]
  have hG : IntervalIntegrable (fun x : ℝ => c * cexp (s * x) + c * cexp (θ * I) / 2 * cexp ((s + μ * I) * x)
      + c * cexp (-(θ * I)) / 2 * cexp ((s - μ * I) * x)) volume 0 T :=
    (((hc s).const_mul c).add ((hc _).const_mul _)).add ((hc _).const_mul _)
  have hre := intervalIntegral.intervalIntegral_re hG
  simp only [RCLike.re_to_complex] at hre
  rw [hre, intervalIntegral.integral_add (((hc s).const_mul c).add ((hc _).const_mul _))
      ((hc _).const_mul _), intervalIntegral.integral_add ((hc s).const_mul c) ((hc _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have r1 : (s + μ * I).re ≤ 0 := by simpa using hs
  have r2 : (s - μ * I).re ≤ 0 := by simpa using hs
  set A := ∫ x in (0 : ℝ)..T, cexp (s * x)
  set B := ∫ x in (0 : ℝ)..T, cexp ((s + μ * I) * x)
  set C := ∫ x in (0 : ℝ)..T, cexp ((s - μ * I) * x)
  set a : ℂ := if s = 0 then (T : ℂ) else 0
  set b : ℂ := if s + μ * I = 0 then (T : ℂ) else 0
  set d : ℂ := if s - μ * I = 0 then (T : ℂ) else 0
  have hA := int_exp_bound hs hT
  have hB := int_exp_bound r1 hT
  have hC := int_exp_bound r2 hT
  have hmain : (T : ℝ) * mainT c s μ θ
      = (c * a + c * cexp (θ * I) / 2 * b + c * cexp (-(θ * I)) / 2 * d).re := by
    unfold mainT
    simp only [a, b, d]
    split_ifs <;> simp [Complex.mul_re] <;> ring
  rw [hmain, ← Complex.sub_re]
  have e : c * A + c * cexp (θ * I) / 2 * B + c * cexp (-(θ * I)) / 2 * C
      - (c * a + c * cexp (θ * I) / 2 * b + c * cexp (-(θ * I)) / 2 * d)
      = c * (A - a) + c * cexp (θ * I) / 2 * (B - b) + c * cexp (-(θ * I)) / 2 * (C - d) := by ring
  rw [e]
  refine (Complex.abs_re_le_norm _).trans ?_
  have n1 : ‖cexp (θ * I)‖ = 1 := by rw [Complex.norm_exp]; simp
  have n2 : ‖cexp (-(θ * I))‖ = 1 := by rw [Complex.norm_exp]; simp
  calc ‖c * (A - a) + c * cexp (θ * I) / 2 * (B - b) + c * cexp (-(θ * I)) / 2 * (C - d)‖
      ≤ ‖c * (A - a)‖ + ‖c * cexp (θ * I) / 2 * (B - b)‖ + ‖c * cexp (-(θ * I)) / 2 * (C - d)‖ :=
        norm_add₃_le
    _ = ‖c‖ * ‖A - a‖ + ‖c‖ / 2 * ‖B - b‖ + ‖c‖ / 2 * ‖C - d‖ := by
        simp only [norm_mul, norm_div, n1, n2, mul_one, Complex.norm_ofNat]
    _ ≤ ‖c‖ * (2 * invB s) + ‖c‖ / 2 * (2 * invB (s + μ * I)) + ‖c‖ / 2 * (2 * invB (s - μ * I)) := by
        gcongr
    _ = errT c s μ := by unfold errT; ring

/-! ## C3. The twin form is bounded by a summable on-line part plus a finite off-line sum -/

section Zeros

variable {ι : Type*} {ρ : ι → ℂ}

/-- The ordinate `t_i = (ρ_i − ½)/i`. -/
abbrev ordi (ρ : ι → ℂ) (i : ι) : ℂ := (ρ i - 1 / 2) / Complex.I

theorem norm_cos_real_le (x : ℝ) {t : ℂ} (ht : t.im = 0) : ‖Complex.cos (x * t)‖ ≤ 1 := by
  have e : (x : ℂ) * t = ((x * t.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [ht]
  rw [e, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

/-- **Upper bound for the twin form.** With the explicit formula for `g₀` and for its twin, and every
zero outside `F` on the line: `Q(twin) ≤ 4Σ‖ĝ₀(t_i)²‖ + Σ_{i∈F} Re(2cos(λt_i)ĝ₀(t_i))²`. -/
theorem weilQ_twin_le {b : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀) {l : ℝ} (hl : 0 ≤ l)
    (hEF0 : WeilExplicit ρ (fun z => ghatC g₀ b z ^ 2) (hsq g₀ b))
    (hEF : WeilExplicit ρ (fun z => ghatC (twin g₀ l) (l + b) z ^ 2) (hsq (twin g₀ l) (l + b)))
    (F : Finset ι) (hF : ∀ i ∉ F, (ρ i).re = 1 / 2) :
    weilQ (l + b) (twin g₀ l)
      ≤ (∑' i, 4 * ‖ghatC g₀ b (ordi ρ i) ^ 2‖)
        + ∑ i ∈ F, ((2 * Complex.cos (l * ordi ρ i) * ghatC g₀ b (ordi ρ i)) ^ 2).re := by
  classical
  have hlb : 0 < l + b := by linarith
  have h := Complex.hasSum_re (weilQ_eq_zero_sum (twin_probe hp hl) hlb hEF)
  rw [Complex.ofReal_re] at h
  simp_rw [ghatC_twin hb hp hl] at h
  have hN : Summable fun i => ‖ghatC g₀ b (ordi ρ i) ^ 2‖ :=
    summable_norm_iff.2 (weilQ_eq_zero_sum hp hb hEF0).summable
  set q : ι → ℝ := fun i => ((2 * Complex.cos (l * ordi ρ i) * ghatC g₀ b (ordi ρ i)) ^ 2).re
  have hfin0 : HasSum (fun i => if i ∈ F then q i else 0)
      (∑ i ∈ F, (if i ∈ F then q i else 0)) :=
    hasSum_sum_of_ne_finset_zero (fun i hi => by simp [hi])
  have hfin : HasSum (fun i => if i ∈ F then q i else 0) (∑ i ∈ F, q i) := by
    rwa [Finset.sum_congr rfl fun i hi => ite_eq_left_iff.2 (fun h => absurd hi h)] at hfin0
  have hu := hfin.add (hN.mul_left 4).hasSum
  suffices hle : ∀ i, q i ≤ (if i ∈ F then q i else 0) + 4 * ‖ghatC g₀ b (ordi ρ i) ^ 2‖ by
    have := hasSum_le hle h hu; linarith
  intro i
  by_cases hi : i ∈ F
  · rw [ite_eq_left_iff.2 (fun h => absurd hi h)]; have := norm_nonneg (ghatC g₀ b (ordi ρ i) ^ 2); linarith
  · rw [ite_eq_right_iff.2 (fun h => absurd h hi), zero_add]
    have ht := ordinate_im_zero (hF i hi)
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_pow, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
    have := norm_cos_real_le l ht
    have h0 := norm_nonneg (ghatC g₀ b (ordi ρ i))
    have hc2 : ‖Complex.cos (l * ordi ρ i)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) this
    have e : (2 * ‖Complex.cos (l * ordi ρ i)‖ * ‖ghatC g₀ b (ordi ρ i)‖) ^ 2
        = 4 * ‖Complex.cos (l * ordi ρ i)‖ ^ 2 * ‖ghatC g₀ b (ordi ρ i)‖ ^ 2 := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖ghatC g₀ b (ordi ρ i)‖)]

end Zeros

/-! ## C4. One zero's contribution: three exponentials -/

theorem member_identity (t G : ℂ) (Y x : ℝ) :
    ((2 * Complex.cos (x * t) * G) ^ 2).re * Real.exp (-2 * Y * x)
      = (2 * G ^ 2 * cexp ((-2 * Y : ℝ) * x)).re + (G ^ 2 * cexp ((2 * I * t - 2 * Y) * x)).re
        + (G ^ 2 * cexp ((-2 * I * t - 2 * Y) * x)).re := by
  rw [← Complex.re_mul_ofReal, ← Complex.add_re, ← Complex.add_re]
  congr 1
  rw [Complex.cos, neg_mul, Complex.ofReal_exp]
  have e1 : cexp ((-2 * Y : ℝ) * x) = cexp (((-2 * Y * x : ℝ)) : ℂ) := by push_cast; ring_nf
  have e2 : cexp ((2 * I * t - 2 * Y) * x)
      = cexp (x * t * I) * cexp (x * t * I) * cexp (((-2 * Y * x : ℝ)) : ℂ) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have e3 : cexp ((-2 * I * t - 2 * Y) * x)
      = cexp (-(x * t * I)) * cexp (-(x * t * I)) * cexp (((-2 * Y * x : ℝ)) : ℂ) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have e4 : cexp (x * t * I) * cexp (-(x * t * I)) = 1 := by rw [← Complex.exp_add]; simp
  rw [e1, e2, e3]
  linear_combination (2 * G ^ 2 * cexp (((-2 * Y * x : ℝ)) : ℂ)) * e4

/-- **One zero's weighted integral**: `q(x)e^{−2Yx}` against the weight is `T·main + O(1)`, the three
exponents being `−2Y`, `2it − 2Y`, `−2it − 2Y` (real parts `≤ 0` when `|Im t| ≤ Y`). -/
theorem member_int (t G : ℂ) {Y : ℝ} (hY : 0 ≤ Y) (ht : |t.im| ≤ Y) (μ θ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    |(∫ x in (0 : ℝ)..T,
        ((2 * Complex.cos (x * t) * G) ^ 2).re * Real.exp (-2 * Y * x) * wt μ θ x)
      - T * (mainT (2 * G ^ 2) (-2 * Y : ℝ) μ θ + mainT (G ^ 2) (2 * I * t - 2 * Y) μ θ
          + mainT (G ^ 2) (-2 * I * t - 2 * Y) μ θ)|
      ≤ errT (2 * G ^ 2) (-2 * Y : ℝ) μ + errT (G ^ 2) (2 * I * t - 2 * Y) μ
        + errT (G ^ 2) (-2 * I * t - 2 * Y) μ := by
  have hcont : ∀ (c s : ℂ), IntervalIntegrable (fun x : ℝ => (c * cexp (s * x)).re * wt μ θ x)
      volume 0 T := fun c s => by
    unfold wt; exact Continuous.intervalIntegrable (by fun_prop) _ _
  have e : (fun x : ℝ => ((2 * Complex.cos (x * t) * G) ^ 2).re * Real.exp (-2 * Y * x) * wt μ θ x)
      = fun x => ((2 * G ^ 2 * cexp ((-2 * Y : ℝ) * x)).re * wt μ θ x
        + (G ^ 2 * cexp ((2 * I * t - 2 * Y) * x)).re * wt μ θ x)
        + (G ^ 2 * cexp ((-2 * I * t - 2 * Y) * x)).re * wt μ θ x := by
    funext x; rw [member_identity]; ring
  rw [e, intervalIntegral.integral_add ((hcont _ _).add (hcont _ _)) (hcont _ _),
    intervalIntegral.integral_add (hcont _ _) (hcont _ _)]
  have r1 : ((-2 * Y : ℝ) : ℂ).re ≤ 0 := by simp; linarith
  have r2 : (2 * I * t - 2 * Y).re ≤ 0 := by
    simp; have := neg_abs_le t.im; linarith
  have r3 : (-2 * I * t - 2 * Y).re ≤ 0 := by
    simp; have := le_abs_self t.im; linarith
  have b1 := int_wt (2 * G ^ 2) ((-2 * Y : ℝ) : ℂ) μ θ r1 hT
  have b2 := int_wt (G ^ 2) (2 * I * t - 2 * Y) μ θ r2 hT
  have b3 := int_wt (G ^ 2) (-2 * I * t - 2 * Y) μ θ r3 hT
  have := abs_add_three
    ((∫ x in (0 : ℝ)..T, (2 * G ^ 2 * cexp ((-2 * Y : ℝ) * x)).re * wt μ θ x)
      - T * mainT (2 * G ^ 2) (-2 * Y : ℝ) μ θ)
    ((∫ x in (0 : ℝ)..T, (G ^ 2 * cexp ((2 * I * t - 2 * Y) * x)).re * wt μ θ x)
      - T * mainT (G ^ 2) (2 * I * t - 2 * Y) μ θ)
    ((∫ x in (0 : ℝ)..T, (G ^ 2 * cexp ((-2 * I * t - 2 * Y) * x)).re * wt μ θ x)
      - T * mainT (G ^ 2) (-2 * I * t - 2 * Y) μ θ)
  calc _ = |_ + _ + _| := by congr 1; ring
    _ ≤ _ := this
    _ ≤ _ := by linarith

/-! ## C5. The main term: only the orbit of `t* = x* + iY` survives, with a fixed sign -/

theorem mainT_cases {c s : ℂ} {μ θ K : ℝ} (hμ : μ ≠ 0) (h0 : s ≠ 0)
    (hp : s + μ * I = 0 → (c * cexp (θ * I) / 2).re = -K)
    (hm : s - μ * I = 0 → (c * cexp (-(θ * I)) / 2).re = -K) (hK : 0 ≤ K) :
    mainT c s μ θ ≤ 0 ∧ ((s + μ * I = 0 ∨ s - μ * I = 0) → mainT c s μ θ = -K) := by
  have hboth : ¬ (s + μ * I = 0 ∧ s - μ * I = 0) := by
    rintro ⟨h1, h2⟩
    have : (μ : ℂ) * I * 2 = 0 := by linear_combination h1 - h2
    simp [hμ] at this
  unfold mainT
  constructor
  · by_cases hb : s + μ * I = 0
    · have hd : ¬ s - μ * I = 0 := fun hd => hboth ⟨hb, hd⟩
      simp only [h0, hb, hd, ↓reduceIte, hp hb]; linarith
    · by_cases hd : s - μ * I = 0
      · simp only [h0, hb, hd, ↓reduceIte, hm hd]; linarith
      · simp only [h0, hb, hd, ↓reduceIte]; norm_num
  · rintro (h | h)
    · have hd : ¬ s - μ * I = 0 := fun hd => hboth ⟨h, hd⟩
      simp only [h0, h, hd, ↓reduceIte, hp h]; ring
    · have hb : ¬ s + μ * I = 0 := fun hb => hboth ⟨hb, h⟩
      simp only [h0, hb, h, ↓reduceIte, hm h]; ring

theorem mainT_real_neg {c : ℂ} {Y μ θ : ℝ} (hY : 0 < Y) : mainT c ((-2 * Y : ℝ) : ℂ) μ θ = 0 := by
  have h0 : ((-2 * Y : ℝ) : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1 : ((-2 * Y : ℝ) : ℂ) + μ * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : ((-2 * Y : ℝ) : ℂ) - μ * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold mainT
  simp only [h0, h1, h2, ↓reduceIte]; ring

/-- The transform of the box of half-width `1` does not vanish off the real line. -/
theorem ghat_box_ne {z : ℂ} (hz : z.im ≠ 0) : ghatC (box 1) 1 z ≠ 0 := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have e : ghatC (box 1) 1 z
      = ((1 / Real.sqrt 2 : ℝ) : ℂ) * ∫ u in (-1 : ℝ)..1, cexp (I * z * u) := by
    unfold ghatC
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by norm_num)] at hu
    have h1 : |u| ≤ 1 := abs_le.2 hu
    simp only [box_apply, h1, ↓reduceIte]
    norm_num
  rw [e, integral_rect hz0]
  refine mul_ne_zero (by simp) (div_ne_zero (mul_ne_zero two_ne_zero ?_) hz0)
  exact sin_ne_zero_of_im (by simpa using hz)

/-- **One zero's main term.** For the twin family built on the box, with `t* = x* + iY`,
`μ = 2x*` and `θ` chosen so that `Re(ĝ(t*)² e^{iθ}) = −|ĝ(t*)²|`: every zero with `Re t ≠ 0` has a
main term `≤ 0`, and a zero in the orbit `{±x* ± iY}` has main term `≤ −|ĝ(t*)²|/2`. -/
theorem member_main {t : ℂ} (htre : t.re ≠ 0) {Y xs θ : ℝ} (hY : 0 < Y) (hxs : 0 < xs)
    (hθ : ((ghatC (box 1) 1 (xs + Y * I)) ^ 2 * cexp (θ * I)).re
      = -‖(ghatC (box 1) 1 (xs + Y * I)) ^ 2‖) :
    let w := ghatC (box 1) 1 t ^ 2
    let K := ‖(ghatC (box 1) 1 (xs + Y * I)) ^ 2‖ / 2
    let M := mainT (2 * w) ((-2 * Y : ℝ) : ℂ) (2 * xs) θ + mainT w (2 * I * t - 2 * Y) (2 * xs) θ
      + mainT w (-2 * I * t - 2 * Y) (2 * xs) θ
    M ≤ 0 ∧ ((t.re = xs ∨ t.re = -xs) → (t.im = Y ∨ t.im = -Y) → M ≤ -K) := by
  intro w K M
  have hev := (box_probe 1).even
  set ts : ℂ := xs + Y * I
  set ws := ghatC (box 1) 1 ts ^ 2
  have hK : 0 ≤ K := by positivity
  have hμ : (2 * xs : ℝ) ≠ 0 := by positivity
  -- the four orbit points and their values
  have vneg : ghatC (box 1) 1 (-ts) ^ 2 = ws := by rw [ghatC_even hev]
  have vconj : ghatC (box 1) 1 ((starRingEnd ℂ) ts) ^ 2 = (starRingEnd ℂ) ws := by
    rw [ghatC_conj hev (by norm_num), map_pow]
  have vnconj : ghatC (box 1) 1 (-(starRingEnd ℂ) ts) ^ 2 = (starRingEnd ℂ) ws := by
    rw [ghatC_even hev, vconj]
  have cθ : (starRingEnd ℂ) (cexp (θ * I)) = cexp (-(θ * I)) := by
    rw [← Complex.exp_conj]; congr 1; simp
  have kP : (ws * cexp (θ * I) / 2).re = -K := by
    rw [Complex.div_ofNat_re, hθ]; show -‖ws‖ / 2 = -(‖ws‖ / 2); ring
  have kM : ((starRingEnd ℂ) ws * cexp (-(θ * I)) / 2).re = -K := by
    rw [← cθ, ← map_mul, Complex.div_ofNat_re, Complex.conj_re, hθ]
    show -‖ws‖ / 2 = -(‖ws‖ / 2); ring
  have ext : ∀ {u : ℂ}, u.re = t.re → u.im = t.im → t = u := fun h1 h2 =>
    Complex.ext h1.symm h2.symm
  -- second exponent `2it − 2Y`
  have A2 := mainT_cases (c := w) (s := 2 * I * t - 2 * Y) (θ := θ) hμ
    (fun h => htre (by have := congrArg Complex.im h; simp at this; linarith))
    (fun h => by
      have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
      simp at h1 h2
      have : t = -ts := ext (by simp [ts]; linarith) (by simp [ts]; linarith)
      simp only [w, this, vneg]; exact kP)
    (fun h => by
      have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
      simp at h1 h2
      have : t = (starRingEnd ℂ) ts := ext (by simp [ts]; linarith) (by simp [ts]; linarith)
      simp only [w, this, vconj]; exact kM) hK
  have A3 := mainT_cases (c := w) (s := -2 * I * t - 2 * Y) (θ := θ) hμ
    (fun h => htre (by have := congrArg Complex.im h; simp at this; linarith))
    (fun h => by
      have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
      simp at h1 h2
      have : t = ts := ext (by simp [ts]; linarith) (by simp [ts]; linarith)
      simp only [w, this]; exact kP)
    (fun h => by
      have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
      simp at h1 h2
      have : t = -(starRingEnd ℂ) ts := ext (by simp [ts]; linarith) (by simp [ts]; linarith)
      simp only [w, this, vnconj]; exact kM) hK
  have A1 : mainT (2 * w) ((-2 * Y : ℝ) : ℂ) (2 * xs) θ = 0 := mainT_real_neg hY
  refine ⟨by simp only [M]; linarith [A2.1, A3.1], fun hr hi => ?_⟩
  simp only [M]
  rw [A1]
  rcases hr with hr | hr <;> rcases hi with hi | hi
  · have := A3.2 (Or.inl (Complex.ext (by simp [hr, hi]) (by simp [hr, hi])))
    linarith [A2.1]
  · have := A2.2 (Or.inr (Complex.ext (by simp [hr, hi]) (by simp [hr, hi])))
    linarith [A3.1]
  · have := A3.2 (Or.inr (Complex.ext (by simp [hr, hi]) (by simp [hr, hi])))
    linarith [A2.1]
  · have := A2.2 (Or.inl (Complex.ext (by simp [hr, hi]) (by simp [hr, hi])))
    linarith [A3.1]

theorem errT_nonneg (c s : ℂ) (μ : ℝ) : 0 ≤ errT c s μ := by
  unfold errT
  have := invB_nonneg s; have := invB_nonneg (s + μ * I); have := invB_nonneg (s - μ * I)
  positivity

theorem im_ordinate (s : ℂ) : ((s - 1 / 2) / Complex.I).im = -(s.re - 1 / 2) := by
  simp [Complex.div_I]

/-! ## C6. The converse -/

section Final

variable {ι : Type*} {ρ : ι → ℂ}

/-- **An off-line zero makes Weil's form negative.** Suppose the explicit formula holds for every probe,
every member of the zero family outside a finite set `F` lies on the critical line, no member of `F` is
real (`Im ρ ≠ 0`, true for `ζ`), and some member of `F` is off the line. Then some probe at some support
has `Q(g) < 0`.

Proof: the twin boxes at `±λ` have `ĝ_λ = 2cos(λz)ĝ₀`. If `Q(ĝ_λ) ≥ 0` for every `λ ≥ 0`, integrate the
explicit upper bound `S + Σ_{i∈F} Re(2cos(λt_i)ĝ₀(t_i))²` against `e^{−2Yλ}(1 + cos(2x*λ + θ))` over
`[0, T]`. Here `Y` is the largest `|Im t_i|`, attained at `t* = x* + iY`. Every exponential except the
orbit of `t*` integrates to `O(1)`; the orbit contributes `T·Re(ĝ₀(t*)²e^{iθ})/2 = −T|ĝ₀(t*)²|/2`. For
large `T` the integral of a nonnegative function is negative. -/
theorem exists_weilQ_neg_of_offline
    (hEF : ∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g →
      WeilExplicit ρ (fun z => ghatC g a z ^ 2) (hsq g a))
    (F : Finset ι) (hF : ∀ i ∉ F, (ρ i).re = 1 / 2)
    (hre : ∀ i ∈ F, (ρ i).im ≠ 0) (hoff : ∃ i ∈ F, (ρ i).re ≠ 1 / 2) :
    ∃ a g, 0 < a ∧ Probe a g ∧ weilQ a g < 0 := by
  classical
  by_contra hno
  have hpos : ∀ l : ℝ, 0 ≤ l → 0 ≤ weilQ (l + 1) (twin (box 1) l) := fun l hl => by
    by_contra h
    exact hno ⟨l + 1, twin (box 1) l, by linarith, twin_probe (box_probe 1) hl, not_le.1 h⟩
  obtain ⟨i0, hi0F, hi0⟩ := hoff
  obtain ⟨is, hisF, hmax⟩ := F.exists_max_image (fun i => |(ordi ρ i).im|) ⟨i0, hi0F⟩
  set Y := |(ordi ρ is).im| with hYdef
  have hY : 0 < Y := by
    have h1 : 0 < |(ordi ρ i0).im| :=
      abs_pos.2 (by rw [im_ordinate]; intro h; apply hi0; linarith)
    exact lt_of_lt_of_le h1 (hmax i0 hi0F)
  set xs := |(ordi ρ is).re| with hxsdef
  have hxs : 0 < xs := abs_pos.2 (by rw [re_ordinate]; exact hre is hisF)
  set G := ghatC (box 1) 1 with hG
  set ws := G (xs + Y * I) ^ 2 with hwsdef
  have hws : ws ≠ 0 := pow_ne_zero 2 (ghat_box_ne (by simp; exact hY.ne'))
  set θ : ℝ := π - Complex.arg ws with hθdef
  have hθ : (ws * cexp (θ * I)).re = -‖ws‖ := by
    have h1 : cexp (θ * I) = -cexp (-(Complex.arg ws * I)) := by
      rw [show (θ : ℂ) * I = π * I + (-(Complex.arg ws * I)) by rw [hθdef]; push_cast; ring,
        Complex.exp_add, Complex.exp_pi_mul_I]; ring
    have h2 : ws * cexp (-(Complex.arg ws * I)) = ‖ws‖ := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ws]
      rw [mul_assoc, ← Complex.exp_add]; simp
    rw [h1, mul_neg, h2]; simp
  set μ : ℝ := 2 * xs with hμdef
  set S := ∑' i, 4 * ‖G (ordi ρ i) ^ 2‖ with hSdef
  have hS : 0 ≤ S := tsum_nonneg fun i => by positivity
  set q : ι → ℝ → ℝ := fun i x => ((2 * Complex.cos (x * ordi ρ i) * G (ordi ρ i)) ^ 2).re
  set Mi : ι → ℝ := fun i => mainT (2 * G (ordi ρ i) ^ 2) ((-2 * Y : ℝ) : ℂ) μ θ
    + mainT (G (ordi ρ i) ^ 2) (2 * I * ordi ρ i - 2 * Y) μ θ
    + mainT (G (ordi ρ i) ^ 2) (-2 * I * ordi ρ i - 2 * Y) μ θ
  set Ei : ι → ℝ := fun i => errT (2 * G (ordi ρ i) ^ 2) ((-2 * Y : ℝ) : ℂ) μ
    + errT (G (ordi ρ i) ^ 2) (2 * I * ordi ρ i - 2 * Y) μ
    + errT (G (ordi ρ i) ^ 2) (-2 * I * ordi ρ i - 2 * Y) μ
  have hMle : ∀ i ∈ F, Mi i ≤ 0 := fun i hi =>
    (member_main (by rw [re_ordinate]; exact hre i hi) hY hxs hθ).1
  have hMs : Mi is ≤ -(‖ws‖ / 2) :=
    (member_main (by rw [re_ordinate]; exact hre is hisF) hY hxs hθ).2
      ((abs_choice (ordi ρ is).re).imp (fun h => by rw [hxsdef, h]) (fun h => by rw [hxsdef, h]; ring))
      ((abs_choice (ordi ρ is).im).imp (fun h => by rw [hYdef, h]) (fun h => by rw [hYdef, h]; ring))
  set C := errT (S : ℂ) ((-2 * Y : ℝ) : ℂ) μ + ∑ i ∈ F, Ei i
  have hwpos : 0 < ‖ws‖ := norm_pos_iff.2 hws
  set T := 2 * (C + 1) / ‖ws‖
  have hC : 0 ≤ C := add_nonneg (errT_nonneg _ _ _) (Finset.sum_nonneg fun i _ =>
    add_nonneg (add_nonneg (errT_nonneg _ _ _) (errT_nonneg _ _ _)) (errT_nonneg _ _ _))
  have hT : 0 ≤ T := by positivity
  -- continuity
  have hqc : ∀ i, Continuous fun x : ℝ => q i x * Real.exp (-2 * Y * x) * wt μ θ x := fun i => by
    simp only [q, wt]; fun_prop
  have hSc : Continuous fun x : ℝ => S * Real.exp (-2 * Y * x) * wt μ θ x := by
    simp only [wt]; fun_prop
  -- the integral is nonnegative
  have hf0 : 0 ≤ ∫ x in (0 : ℝ)..T,
      (S * Real.exp (-2 * Y * x) * wt μ θ x + ∑ i ∈ F, q i x * Real.exp (-2 * Y * x) * wt μ θ x) := by
    refine intervalIntegral.integral_nonneg hT fun x hx => ?_
    have h1 := weilQ_twin_le one_pos (box_probe 1) hx.1 (hEF 1 (box 1) one_pos (box_probe 1))
      (hEF _ _ (by linarith [hx.1]) (twin_probe (box_probe 1) hx.1)) F hF
    have h2 := hpos x hx.1
    have e : S * Real.exp (-2 * Y * x) * wt μ θ x + ∑ i ∈ F, q i x * Real.exp (-2 * Y * x) * wt μ θ x
        = (S + ∑ i ∈ F, q i x) * (Real.exp (-2 * Y * x) * wt μ θ x) := by
      rw [add_mul, Finset.sum_mul]; congr 1 <;> [ring; exact Finset.sum_congr rfl fun i _ => by ring]
    rw [e]
    exact mul_nonneg (by simp only [q, S, G] at h1 ⊢; linarith)
      (mul_nonneg (Real.exp_pos _).le (wt_nonneg _ _ _))
  -- the integral is at most `C − T|w*|/2`
  rw [intervalIntegral.integral_add (hSc.intervalIntegrable _ _)
    (by exact (continuous_finsetSum _ fun i _ => hqc i).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum fun i _ => (hqc i).intervalIntegrable _ _] at hf0
  have hSb : ∫ x in (0 : ℝ)..T, S * Real.exp (-2 * Y * x) * wt μ θ x
      ≤ errT (S : ℂ) ((-2 * Y : ℝ) : ℂ) μ := by
    have r : ((((-2 * Y : ℝ) : ℂ)).re) ≤ 0 := by simp; linarith
    have b := int_wt (S : ℂ) ((-2 * Y : ℝ) : ℂ) μ θ r hT
    rw [mainT_real_neg hY, mul_zero, sub_zero] at b
    have e : (fun x : ℝ => ((S : ℂ) * cexp (((-2 * Y : ℝ) : ℂ) * x)).re * wt μ θ x)
        = fun x => S * Real.exp (-2 * Y * x) * wt μ θ x := by
      funext x; rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    rw [e] at b
    exact (le_abs_self _).trans b
  have hmem : ∀ i ∈ F, ∫ x in (0 : ℝ)..T, q i x * Real.exp (-2 * Y * x) * wt μ θ x
      ≤ T * Mi i + Ei i := fun i hi => by
    have b := member_int (ordi ρ i) (G (ordi ρ i)) hY.le (hmax i hi) μ θ hT
    have := (le_abs_self _).trans b
    simp only [q, Mi, Ei]; linarith
  have hsum : ∑ i ∈ F, ∫ x in (0 : ℝ)..T, q i x * Real.exp (-2 * Y * x) * wt μ θ x
      ≤ T * Mi is + ∑ i ∈ F, Ei i := by
    refine (Finset.sum_le_sum hmem).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.add_sum_erase F Mi hisF]
    have : ∑ i ∈ F.erase is, Mi i ≤ 0 :=
      Finset.sum_nonpos fun i hi => hMle i (Finset.mem_of_mem_erase hi)
    nlinarith
  have hTw : T * (‖ws‖ / 2) = C + 1 := by
    simp only [T]; field_simp
  nlinarith


/-- **Weil's criterion, both directions, for a family with finitely many off-line zeros.** If every
zero outside a finite set `F` is on the line and no member of `F` is real, then: `Q ≥ 0` for every probe
at every support if and only if every zero is on the critical line. -/
theorem weil_criterion_finite
    (hEF : ∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g →
      WeilExplicit ρ (fun z => ghatC g a z ^ 2) (hsq g a))
    (F : Finset ι) (hF : ∀ i ∉ F, (ρ i).re = 1 / 2)
    (hre : ∀ i ∈ F, (ρ i).im ≠ 0) :
    (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ weilQ a g) ↔ ∀ i, (ρ i).re = 1 / 2 := by
  constructor
  · intro hQ
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := h
    have hiF : i ∈ F := by by_contra h'; exact hi (hF i h')
    obtain ⟨a, g, ha, hp, hneg⟩ := exists_weilQ_neg_of_offline hEF F hF hre ⟨i, hiF, hi⟩
    exact absurd (hQ a g ha hp) (not_le.2 hneg)
  · intro hline a g ha hp
    exact weilQ_nonneg_of_zeros_on_line hp ha (hEF a g ha hp) hline

end Final

end Pilot1ca

#print axioms Pilot1ca.ghatC_twin
#print axioms Pilot1ca.int_wt
#print axioms Pilot1ca.weilQ_twin_le
#print axioms Pilot1ca.member_main
#print axioms Pilot1ca.exists_weilQ_neg_of_offline
#print axioms Pilot1ca.weil_criterion_finite
