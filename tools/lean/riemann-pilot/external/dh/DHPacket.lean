import Mathlib
import DHBridge

/-! # The box wave packet: Weil's form of `dh` on `cos(ωu)·1_{[−a,a]}` in closed form (round 259)

Round 258's numerics showed that the Davenport–Heilbronn Weil form `Q_dh` is negative on a detuned wave
packet (`−0.50‖g‖²` at `(a, ω) = (2.4, 84.5)`) and on no monotone profile. This file is stage 1 of the
kernel-checked certificate `Q_dh(packet 2.4 84.5) < 0`: everything about the packet
`packet a ω = 1_{[−a,a]}·cos(ω·)` that is exact, for every `0 < a`, `0 < ω`.

**The probe** (`packet_probe`): even, supported in `[−a, a]`, in `L²`, with the archimedean integrand
integrable by the Lipschitz bound `f(0) − f(u) ≤ (aω²u + 1)u` (`packet_autocorr_diff_le`).
**Closed forms**: `‖g‖² = a + sin(2ωa)/(2ω)` (`packet_normSq`),
`f(u) = ½(2a − u) cos(ωu) + sin(ω(2a − u))/(2ω)` on `0 ≤ u ≤ 2a` and `0` beyond (`packet_autocorr`,
`packet_autocorr_of_abs_le`), `ĝ(z) = sin((z + ω)a)/(z + ω) + sin((z − ω)a)/(z − ω)` (`packet_ghatC`), and the
width-3 strip test `ĝ(3z)²` needs (`packet_striptest`, from `‖sin w‖ ≤ e^{|Im w|}`), so `QDHu_hasSum` and
`exists_offline_dh_of_neg_u` apply (`packet_QDHu_hasSum`, `exists_offline_dh_of_neg_packet`).
**The prime sum is finite** (`tsum_fDH_eq_sum`, `QDHu_eq_sum`): `c(0) = c(1) = 0` and `f(log n) = 0` for
`n > ⌊e^{2a}⌋`.
**The κ-structure of `c(n)`**: `u(n) = a(n)/a(1)` takes the values `0, 1, κ, −κ, −1` by `n mod 5` for `n ≥ 2`
(`uDH_chi5_eq`, `uR_eq`) with `κ = 2 sin(π/5)/(√5 + 2 sin(2π/5)) = Im ε/(1 + Re ε)`, `0.28407 < κ < 0.28408`
(`kappa_gt`, `kappa_lt`, from `sin²(π/5) = (5 − √5)/8`, `sin²(2π/5) = (5 + √5)/8`); the Dirichlet inverse and
`c(n)` are real recursions (`dinvR_of_two_le`, `fDH_eq`), so `c(n)` is an integer polynomial in `κ` with
`log d` coefficients.
**The assembled statement** (`QDHu_packet_eq`):
`Q_dh(g) = (Re ψ(¾) + log(5/π))(a + sin(2ωa)/(2ω)) + E_{3/4}(g) − 2 Σ_{2 ≤ n ≤ ⌊e^{2a}⌋} c(n) n^{−1/2} f(log n)`.
Stage 2 bounds `E_{3/4}(g)`; stage 3 evaluates the finite sum in verified arithmetic.

The five sections were built by agents to stated interfaces and re-read and recompiled by the lead; the
assembly is the lead's.
-/

open Real Complex MeasureTheory Set Filter Topology

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-! ## The packet -/

/-- The box wave packet `cos(ωu)·1_{[−a,a]}`. -/
def packet (a ω : ℝ) : ℝ → ℝ := Set.indicator (Icc (-a) a) fun u => Real.cos (ω * u)

theorem packet_apply (a ω u : ℝ) :
    packet a ω u = if |u| ≤ a then Real.cos (ω * u) else 0 := by
  unfold packet
  rw [Set.indicator_apply]
  congr 1
  simp [abs_le]

theorem packet_of_le {a ω u : ℝ} (hu : |u| ≤ a) : packet a ω u = Real.cos (ω * u) := by
  simp [packet_apply, hu]

theorem packet_of_lt {a ω u : ℝ} (hu : a < |u|) : packet a ω u = 0 := by
  simp [packet_apply, not_le.2 hu]

theorem packet_even (a ω u : ℝ) : packet a ω (-u) = packet a ω u := by
  rw [packet_apply, packet_apply, abs_neg, mul_neg, Real.cos_neg]

theorem abs_packet_le (a ω u : ℝ) : |packet a ω u| ≤ 1 := by
  rw [packet_apply]
  split_ifs
  · exact Real.abs_cos_le_one _
  · simp

/-- `κ = 2 sin(π/5)/(√5 + 2 sin(2π/5)) = Im ε/(1 + Re ε)`: the value `u(2) = a(2)/a(1)` of the
normalised Dirichlet coefficients of `dh`. -/
def kappa : ℝ := 2 * Real.sin (π / 5) / (Real.sqrt 5 + 2 * Real.sin (2 * π / 5))

/-- The normalised coefficients by residue class mod 5: `0, 1, κ, −κ, −1`. -/
def uval (r : ℕ) : ℝ :=
  if r = 1 then 1 else if r = 2 then kappa else if r = 3 then -kappa else if r = 4 then -1 else 0

/-- The real normalised coefficients `u(n) = Re (uDH χ₅ n)`. -/
def uR (n : ℕ) : ℝ := (uDH chi5 n).re

/-- The real Dirichlet inverse `Re (dinv u n)`. -/
def dinvR (n : ℕ) : ℝ := (DInv.dinv (uDH chi5) n).re

/-! ## Closed forms of the autocorrelation and the norm -/

/-- For `0 ≤ u`, `g(t) g(t + u) = 1_{[−a, a−u]}(t) cos(ωt) cos(ω(t+u))`. -/
theorem packet_mul_shift (a ω : ℝ) {u : ℝ} (hu0 : 0 ≤ u) (t : ℝ) :
    packet a ω t * packet a ω (t + u) =
      (Icc (-a) (a - u)).indicator (fun t => Real.cos (ω * t) * Real.cos (ω * (t + u))) t := by
  rw [packet_apply, packet_apply, Set.indicator_apply]
  simp only [mem_Icc]
  by_cases h1 : -a ≤ t ∧ t ≤ a - u
  · have ht : |t| ≤ a := abs_le.2 ⟨h1.1, by linarith [h1.2]⟩
    have htu : |t + u| ≤ a := abs_le.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
    simp only [ht, htu, h1, and_self, ↓reduceIte]
  · simp only [h1, ↓reduceIte]
    by_cases ht : |t| ≤ a
    · have htu : ¬ |t + u| ≤ a := by
        intro htu
        exact h1 ⟨(abs_le.1 ht).1, by linarith [(abs_le.1 htu).2]⟩
      simp only [htu, ↓reduceIte, mul_zero]
    · simp only [ht, ↓reduceIte, zero_mul]

/-- For `0 ≤ u`, the autocorrelation is the integral of `cos(ωt) cos(ω(t+u))` over `[−a, a−u]`. -/
theorem packet_autocorr_Icc (a ω : ℝ) {u : ℝ} (hu0 : 0 ≤ u) :
    autocorr (packet a ω) u =
      ∫ t in Icc (-a) (a - u), Real.cos (ω * t) * Real.cos (ω * (t + u)) := by
  unfold autocorr
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  funext t
  exact packet_mul_shift a ω hu0 t

/-- `cos(ωt) cos(ω(t+u)) = ½ cos(ωu) + ½ cos(ω(2t+u))`. -/
theorem cos_mul_cos_shift (ω t u : ℝ) :
    Real.cos (ω * t) * Real.cos (ω * (t + u)) =
      Real.cos (ω * u) / 2 + Real.cos (ω * (2 * t + u)) / 2 := by
  have h1 : ω * u = ω * (t + u) - ω * t := by ring
  have h2 : ω * (2 * t + u) = ω * (t + u) + ω * t := by ring
  rw [h1, h2, Real.cos_sub, Real.cos_add]
  ring

/-- `f(u) = ½(2a − u) cos(ωu) + sin(ω(2a − u))/(2ω)` on `0 ≤ u ≤ 2a`. -/
theorem packet_autocorr {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 2 * a) :
    autocorr (packet a ω) u = (2 * a - u) / 2 * Real.cos (ω * u) + Real.sin (ω * (2 * a - u)) / (2 * ω) := by
  -- `0 < a` belongs to the interface only: the identity needs just `0 ≤ u ≤ 2a`.
  have _ := ha
  have hle : -a ≤ a - u := by linarith
  rw [packet_autocorr_Icc a ω hu0, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hω0 : ω ≠ 0 := hω.ne'
  have hderiv : ∀ t ∈ uIcc (-a) (a - u),
      HasDerivAt (fun t => Real.cos (ω * u) * t / 2 + Real.sin (ω * (2 * t + u)) / (4 * ω))
        (Real.cos (ω * t) * Real.cos (ω * (t + u))) t := by
    intro t _
    rw [cos_mul_cos_shift]
    have hlin : HasDerivAt (fun t : ℝ => ω * (2 * t + u)) (ω * 2) t := by
      have := ((hasDerivAt_id t).const_mul 2).add_const u
      simpa using this.const_mul ω
    have h1 : HasDerivAt (fun x : ℝ => Real.cos (ω * u) * x / 2) (Real.cos (ω * u) / 2) t := by
      simpa using ((hasDerivAt_id t).const_mul (Real.cos (ω * u))).div_const 2
    have h2 : HasDerivAt (fun x : ℝ => Real.sin (ω * (2 * x + u)) / (4 * ω))
        (Real.cos (ω * (2 * t + u)) / 2) t := by
      have := ((Real.hasDerivAt_sin (ω * (2 * t + u))).comp t hlin).div_const (4 * ω)
      exact this.congr_deriv (by field_simp; ring)
    exact h1.add h2
  have hcont : Continuous fun t : ℝ => Real.cos (ω * t) * Real.cos (ω * (t + u)) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  have e1 : ω * (2 * (a - u) + u) = ω * (2 * a - u) := by ring
  have e2 : ω * (2 * -a + u) = -(ω * (2 * a - u)) := by ring
  rw [e1, e2, Real.sin_neg]
  field_simp
  ring

/-- For `u ≥ 2a` the autocorrelation vanishes (the overlap `[−a, a−u]` is null). -/
theorem packet_autocorr_of_le {a ω : ℝ} (ha : 0 < a) {u : ℝ} (hu : 2 * a ≤ u) :
    autocorr (packet a ω) u = 0 := by
  rw [packet_autocorr_Icc a ω (by linarith)]
  apply setIntegral_measure_zero
  rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
  linarith

theorem packet_autocorr_of_abs_le {a ω : ℝ} (ha : 0 < a) {u : ℝ} (hu : 2 * a ≤ |u|) :
    autocorr (packet a ω) u = 0 := by
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h] at hu
    exact packet_autocorr_of_le ha hu
  · rw [abs_of_nonpos h] at hu
    have hneg : autocorr (packet a ω) u = autocorr (packet a ω) (-u) := by
      unfold autocorr
      have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun t => packet a ω t * packet a ω (t + u)) (-u)
      rw [← this]
      congr 1
      funext t
      rw [show t + -u + u = t by ring, mul_comm]
    rw [hneg]
    exact packet_autocorr_of_le ha hu

/-- `‖g‖² = a + sin(2ωa)/(2ω)`. -/
theorem packet_normSq {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    normSq (packet a ω) = a + Real.sin (2 * ω * a) / (2 * ω) := by
  rw [← autocorr_zero, packet_autocorr ha hω le_rfl (by linarith)]
  rw [mul_zero, Real.cos_zero, mul_one, sub_zero, show ω * (2 * a) = 2 * ω * a by ring]
  ring

/-! ## The packet is a probe -/

theorem packet_supp {a ω : ℝ} (u : ℝ) (hu : a < |u|) : packet a ω u = 0 :=
  packet_of_lt hu

theorem packet_memLp (a ω : ℝ) : MemLp (packet a ω) 2 volume := by
  unfold packet
  exact memLp_indicator_of_continuous (f := fun u => Real.cos (ω * u)) (by fun_prop)
    measurableSet_Icc measure_Icc_lt_top.ne (C := 1) fun x _ => Real.abs_cos_le_one _

theorem packet_measurable (a ω : ℝ) : Measurable (packet a ω) := by
  unfold packet
  exact (by fun_prop : Measurable fun u => Real.cos (ω * u)).indicator measurableSet_Icc

theorem packet_intervalIntegrable (a ω : ℝ) : IntervalIntegrable (packet a ω) volume (-a) a :=
  memLp_intervalIntegrable (packet_memLp a ω) _ _

/-- `f(0) − f(u) ≤ (aω² u + 1) u` for `u ≥ 0`: the shifted packet differs by at most `ωu` inside and by at most
`1` on two edge intervals of length `u`. -/
theorem packet_autocorr_diff_le {a ω : ℝ} (ha : 0 < a) (hω : 0 ≤ ω) {u : ℝ} (hu : 0 ≤ u) :
    autocorr (packet a ω) 0 - autocorr (packet a ω) u ≤ (a * ω ^ 2 * u + 1) * u := by
  have hb := packet_memLp a ω
  rw [show autocorr (packet a ω) 0 - autocorr (packet a ω) u
      = normSq (fun t => packet a ω t - packet a ω (t + u)) / 2 by
    rw [normSq_sub_shift hb u]; ring]
  set B : ℝ → ℝ := fun t => ω ^ 2 * u ^ 2 * (Icc (-a) a).indicator 1 t
    + ((Icc (a - u) a).indicator 1 t + (Icc (-a - u) (-a)).indicator 1 t) with hB
  have hI : ∀ x y : ℝ, Integrable ((Icc x y).indicator (1 : ℝ → ℝ)) := fun x y =>
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)
  have hBint : Integrable B := ((hI _ _).const_mul _).add ((hI _ _).add (hI _ _))
  have hnn : ∀ (s : Set ℝ) (t : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) t :=
    fun s t => Set.indicator_nonneg (fun _ _ => zero_le_one) t
  have hone : ∀ {s : Set ℝ} {t : ℝ}, t ∈ s → s.indicator (1 : ℝ → ℝ) t = 1 :=
    fun ht => by rw [Set.indicator_of_mem ht]; rfl
  have hpt : ∀ t, (packet a ω t - packet a ω (t + u)) ^ 2 ≤ B t := by
    intro t
    have i1 := hnn (Icc (-a) a) t
    have i2 := hnn (Icc (a - u) a) t
    have i3 := hnn (Icc (-a - u) (-a)) t
    have hwu : 0 ≤ ω ^ 2 * u ^ 2 := by positivity
    simp only [hB]
    rw [packet_apply, packet_apply]
    by_cases h1 : |t| ≤ a <;> by_cases h2 : |t + u| ≤ a
    · simp only [h1, h2, ite_true]
      have hc := Real.abs_cos_sub_cos_le (ω * t) (ω * (t + u))
      have e : |ω * t - ω * (t + u)| = ω * u := by
        rw [show ω * t - ω * (t + u) = -(ω * u) by ring, abs_neg,
          abs_of_nonneg (mul_nonneg hω hu)]
      rw [e] at hc
      have hsq : (Real.cos (ω * t) - Real.cos (ω * (t + u))) ^ 2 ≤ ω ^ 2 * u ^ 2 := by
        rw [← sq_abs]
        calc |Real.cos (ω * t) - Real.cos (ω * (t + u))| ^ 2 ≤ (ω * u) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) hc 2
          _ = ω ^ 2 * u ^ 2 := by ring
      rw [hone (show t ∈ Icc (-a) a by rw [mem_Icc, ← abs_le]; exact h1)]
      linarith
    · simp only [h1, h2, ite_true, ite_false, sub_zero]
      have ht : t ∈ Icc (a - u) a := by
        rw [abs_le] at h1; rw [not_le, lt_abs] at h2
        constructor
        · rcases h2 with h2 | h2 <;> linarith
        · exact h1.2
      rw [hone ht]
      have := Real.cos_sq_le_one (ω * t)
      nlinarith
    · simp only [h1, h2, ite_true, ite_false, zero_sub, neg_sq]
      have ht : t ∈ Icc (-a - u) (-a) := by
        rw [abs_le] at h2; rw [not_le, lt_abs] at h1
        constructor
        · linarith [h2.1]
        · rcases h1 with h1 | h1
          · linarith [h2.2]
          · linarith
      rw [hone ht]
      have := Real.cos_sq_le_one (ω * (t + u))
      nlinarith
    · simp only [h1, h2, ite_false, sub_self]
      nlinarith
  have hle : normSq (fun t => packet a ω t - packet a ω (t + u)) ≤ ∫ t, B t :=
    integral_mono ((hb.sub (memLp_shift hb u)).integrable_sq) hBint hpt
  have hBv : ∫ t, B t = 2 * ((a * ω ^ 2 * u + 1) * u) := by
    have hI1 : Integrable (fun t => ω ^ 2 * u ^ 2 * (Icc (-a) a).indicator (1 : ℝ → ℝ) t) :=
      (hI _ _).const_mul _
    have hI2 : Integrable (fun t => (Icc (a - u) a).indicator (1 : ℝ → ℝ) t
        + (Icc (-a - u) (-a)).indicator 1 t) := (hI _ _).add (hI _ _)
    simp only [hB]
    rw [integral_add hI1 hI2, integral_const_mul, integral_add (hI _ _) (hI _ _),
      integral_indicator_one measurableSet_Icc, integral_indicator_one measurableSet_Icc,
      integral_indicator_one measurableSet_Icc,
      Measure.real, Measure.real, Measure.real, Real.volume_Icc, Real.volume_Icc, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hBv] at hle
  linarith

theorem packet_arch {a ω : ℝ} (ha : 0 < a) (hω : 0 ≤ ω) :
    IntegrableOn (archIntegrand (packet a ω)) (Set.Ioi 0) := by
  have hm : AEStronglyMeasurable (archIntegrand (packet a ω)) (volume.restrict (Ioi 0)) := by
    have h1 := (autocorr_stronglyMeasurable (packet_measurable a ω)).measurable
    have : Measurable (archIntegrand (packet a ω)) := by
      unfold archIntegrand
      exact ((measurable_const.sub h1).mul
        ((Real.measurable_exp.comp (measurable_id.div_const 2)).div Real.measurable_sinh))
    exact this.aestronglyMeasurable
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 8)).const_mul
    (16 * (8 * (a * ω ^ 2) + 1))) hm
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
  have hu0 : 0 < u := hu
  have hK : 0 < Real.exp (u / 2) / Real.sinh u :=
    div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu0)
  rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg (packet_memLp a ω) hu0)]
  unfold archIntegrand
  have hA : 0 ≤ a * ω ^ 2 := by positivity
  have hpoly : a * ω ^ 2 * u + 1 ≤ (8 * (a * ω ^ 2) + 1) * Real.exp (1 / 8 * u) := by
    have e1 := Real.add_one_le_exp (1 / 8 * u)
    have e2 : 1 ≤ Real.exp (1 / 8 * u) := Real.one_le_exp (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left e1 hA]
  have hexp : Real.exp (1 / 8 * u) * Real.exp (-(1 / 4) * u) = Real.exp (-(1 / 8) * u) := by
    rw [← Real.exp_add]; ring_nf
  calc (autocorr (packet a ω) 0 - autocorr (packet a ω) u) * (Real.exp (u / 2) / Real.sinh u)
      ≤ ((a * ω ^ 2 * u + 1) * u) * (Real.exp (u / 2) / Real.sinh u) :=
        mul_le_mul_of_nonneg_right (packet_autocorr_diff_le ha hω hu0.le) hK.le
    _ = (a * ω ^ 2 * u + 1) * (u * (Real.exp (u / 2) / Real.sinh u)) := by ring
    _ ≤ (a * ω ^ 2 * u + 1) * (16 * Real.exp (-(1 / 4) * u)) :=
        mul_le_mul_of_nonneg_left (u_archK_le hu0) (by positivity)
    _ ≤ ((8 * (a * ω ^ 2) + 1) * Real.exp (1 / 8 * u)) * (16 * Real.exp (-(1 / 4) * u)) :=
        mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = 16 * (8 * (a * ω ^ 2) + 1) * Real.exp (-(1 / 8) * u) := by rw [← hexp]; ring

theorem packet_probe {a ω : ℝ} (ha : 0 < a) (hω : 0 ≤ ω) : Probe a (packet a ω) :=
  ⟨packet_even a ω, fun u hu => packet_supp u hu, packet_memLp a ω, packet_arch ha hω⟩

/-! ## The transform and the width-3 strip test -/

/-- `∫_{−a}^{a} e^{iwu} du = 2 sin(wa)/w` for `w ≠ 0`. -/
theorem integral_cexp_I_mul {w : ℂ} (hw : w ≠ 0) (a : ℝ) :
    ∫ u in (-a)..a, Complex.exp (Complex.I * w * u) = 2 * Complex.sin (w * a) / w := by
  have hc : Complex.I * w ≠ 0 := mul_ne_zero Complex.I_ne_zero hw
  rw [integral_exp_mul_complex hc]
  have e1 : Complex.exp (Complex.I * w * (a : ℂ)) = Complex.exp (w * a * Complex.I) := by
    congr 1; ring
  have e2 : Complex.exp (Complex.I * w * ((-a : ℝ) : ℂ)) = Complex.exp (-(w * a) * Complex.I) := by
    congr 1; push_cast; ring
  rw [e1, e2, Complex.sin]
  generalize Complex.exp (w * a * Complex.I) = E1
  generalize Complex.exp (-(w * a) * Complex.I) = E2
  rw [div_eq_iff hc]
  field_simp
  linear_combination (E1 - E2) * Complex.I_sq

/-- The packet is integrable. -/
theorem packet_integrable (a ω : ℝ) : Integrable (packet a ω) := by
  unfold packet
  exact (Continuous.integrableOn_Icc (by fun_prop)).integrable_indicator measurableSet_Icc

/-- `ĝ(z) = sin((z + ω)a)/(z + ω) + sin((z − ω)a)/(z − ω)`. -/
theorem packet_ghatC {a ω : ℝ} (ha : 0 ≤ a) (z : ℂ) (h1 : z + ω ≠ 0) (h2 : z - ω ≠ 0) :
    ghatC (packet a ω) a z
      = Complex.sin ((z + ω) * a) / (z + ω) + Complex.sin ((z - ω) * a) / (z - ω) := by
  unfold ghatC
  have hcongr : EqOn (fun u : ℝ => ((packet a ω u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u))
      (fun u : ℝ => (Complex.exp (Complex.I * (z + ω) * u) + Complex.exp (Complex.I * (z - ω) * u)) / 2)
      (Set.uIcc (-a) a) := by
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    have hu' : |u| ≤ a := abs_le.2 hu
    simp only
    rw [packet_of_le hu', Complex.ofReal_cos, Complex.cos]
    have e1 : Complex.exp (Complex.I * (z + ω) * u)
        = Complex.exp ((ω * u : ℂ) * Complex.I) * Complex.exp (Complex.I * z * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    have e2 : Complex.exp (Complex.I * (z - ω) * u)
        = Complex.exp (-(ω * u : ℂ) * Complex.I) * Complex.exp (Complex.I * z * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [e1, e2]
    push_cast
    ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_div,
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cexp_I_mul h1, integral_cexp_I_mul h2]
  ring

/-- `‖sin w‖ ≤ e^{|Im w|}`. -/
theorem norm_csin_le_exp (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have h := norm_sub_le (Complex.exp (-w * Complex.I)) (Complex.exp (w * Complex.I))
  rw [Complex.norm_exp, Complex.norm_exp] at h
  have r1 : (-w * Complex.I).re = w.im := by simp
  have r2 : (w * Complex.I).re = -w.im := by simp
  rw [r1, r2] at h
  have b1 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.2 (le_abs_self _)
  have b2 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.2 (neg_le_abs _)
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- **`ĝ(3z)²` is a strip test function.** -/
theorem packet_striptest {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    ∃ K, StripTest (fun z => ghatC (packet a ω) a (3 * z) ^ 2) K := by
  have hint : IntervalIntegrable (packet a ω) volume (-a) a :=
    (packet_integrable a ω).intervalIntegrable
  set τ0 := Real.exp (3 * a) * ∫ u in (-a)..a, |packet a ω u| with hτ0
  have hI : 0 ≤ ∫ u in (-a)..a, |packet a ω u| :=
    intervalIntegral.integral_nonneg (by linarith) fun u _ => abs_nonneg _
  have hτ0nn : 0 ≤ τ0 := mul_nonneg (Real.exp_pos _).le hI
  refine ⟨τ0 ^ 2 + ((1 + ω) / 3 * (2 * Real.exp (3 * a) + τ0)) ^ 2,
    striptest_sq ((ghatC_differentiable hint).comp (differentiable_id.const_mul 3))
      fun t ht => ?_⟩
  have h3im : (3 * t).im = 3 * t.im := by simp
  have htim : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  have h3 : |(3 * t).im| ≤ 3 := by
    rw [h3im, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith
  have hG0 : ‖ghatC (packet a ω) a (3 * t)‖ ≤ τ0 := by
    refine (norm_ghatC_le_exp_im ha.le hint _).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hI
    linarith [mul_le_mul_of_nonneg_left h3 ha.le]
  refine sq_strip_bound hG0 ?_
  show ‖t‖ * ‖ghatC (packet a ω) a (3 * t)‖ ≤ _
  have hn3 : ‖(3 : ℂ) * t‖ = 3 * ‖t‖ := by rw [norm_mul]; norm_num
  have hnω : ‖(ω : ℂ)‖ = ω := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
  have hGn := norm_nonneg (ghatC (packet a ω) a (3 * t))
  have htn := norm_nonneg t
  by_cases hbig : 1 ≤ ‖3 * t + ω‖ ∧ 1 ≤ ‖3 * t - ω‖
  · obtain ⟨hp, hm⟩ := hbig
    have hp0 : (3 * t + ω : ℂ) ≠ 0 := norm_pos_iff.1 (by linarith)
    have hm0 : (3 * t - ω : ℂ) ≠ 0 := norm_pos_iff.1 (by linarith)
    -- the sine bounds
    have hs : ∀ w : ℂ, w.im = (3 * t).im → ‖Complex.sin (w * a)‖ ≤ Real.exp (3 * a) := by
      intro w hw
      refine (norm_csin_le_exp _).trans (Real.exp_le_exp.2 ?_)
      have e : (w * a).im = w.im * a := by simp
      rw [e, abs_mul, abs_of_pos ha, hw]
      nlinarith
    have hsp := hs (3 * t + ω) (by simp)
    have hsm := hs (3 * t - ω) (by simp)
    -- `‖t‖ ≤ (1 + ω)/3 · ‖3t ± ω‖`
    have htp : ‖t‖ ≤ (1 + ω) / 3 * ‖3 * t + ω‖ := by
      have := norm_sub_le (3 * t + ω) (ω : ℂ)
      rw [add_sub_cancel_right, hn3, hnω] at this
      nlinarith
    have htm : ‖t‖ ≤ (1 + ω) / 3 * ‖3 * t - ω‖ := by
      have := norm_add_le (3 * t - ω) (ω : ℂ)
      rw [sub_add_cancel, hn3, hnω] at this
      nlinarith
    rw [packet_ghatC ha.le _ hp0 hm0]
    have hpn : 0 < ‖3 * t + ω‖ := by linarith
    have hmn : 0 < ‖3 * t - ω‖ := by linarith
    have hq1 : ‖t‖ * ‖Complex.sin ((3 * t + ω) * a) / (3 * t + ω)‖
        ≤ (1 + ω) / 3 * Real.exp (3 * a) := by
      rw [norm_div, mul_div_assoc', div_le_iff₀ hpn]
      calc ‖t‖ * ‖Complex.sin ((3 * t + ω) * a)‖ ≤ ‖t‖ * Real.exp (3 * a) :=
            mul_le_mul_of_nonneg_left hsp htn
        _ ≤ (1 + ω) / 3 * ‖3 * t + ω‖ * Real.exp (3 * a) :=
            mul_le_mul_of_nonneg_right htp (Real.exp_pos _).le
        _ = _ := by ring
    have hq2 : ‖t‖ * ‖Complex.sin ((3 * t - ω) * a) / (3 * t - ω)‖
        ≤ (1 + ω) / 3 * Real.exp (3 * a) := by
      rw [norm_div, mul_div_assoc', div_le_iff₀ hmn]
      calc ‖t‖ * ‖Complex.sin ((3 * t - ω) * a)‖ ≤ ‖t‖ * Real.exp (3 * a) :=
            mul_le_mul_of_nonneg_left hsm htn
        _ ≤ (1 + ω) / 3 * ‖3 * t - ω‖ * Real.exp (3 * a) :=
            mul_le_mul_of_nonneg_right htm (Real.exp_pos _).le
        _ = _ := by ring
    calc ‖t‖ * ‖Complex.sin ((3 * t + ω) * a) / (3 * t + ω)
          + Complex.sin ((3 * t - ω) * a) / (3 * t - ω)‖
        ≤ ‖t‖ * (‖Complex.sin ((3 * t + ω) * a) / (3 * t + ω)‖
          + ‖Complex.sin ((3 * t - ω) * a) / (3 * t - ω)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) htn
      _ ≤ (1 + ω) / 3 * Real.exp (3 * a) + (1 + ω) / 3 * Real.exp (3 * a) := by
          rw [mul_add]; exact add_le_add hq1 hq2
      _ ≤ (1 + ω) / 3 * (2 * Real.exp (3 * a) + τ0) := by nlinarith
  · -- near `±ω/3`: `‖t‖ ≤ (1 + ω)/3`
    have htsmall : ‖t‖ ≤ (1 + ω) / 3 := by
      rcases not_and_or.1 hbig with hp | hm
      · have := norm_sub_le (3 * t + ω) (ω : ℂ)
        rw [add_sub_cancel_right, hn3, hnω] at this
        linarith [not_le.1 hp]
      · have := norm_add_le (3 * t - ω) (ω : ℂ)
        rw [sub_add_cancel, hn3, hnω] at this
        linarith [not_le.1 hm]
    calc ‖t‖ * ‖ghatC (packet a ω) a (3 * t)‖ ≤ (1 + ω) / 3 * τ0 :=
          mul_le_mul htsmall hG0 hGn (by linarith)
      _ ≤ (1 + ω) / 3 * (2 * Real.exp (3 * a) + τ0) := by
          have := Real.exp_pos (3 * a)
          nlinarith

/-! ## The κ-structure of the coefficients -/

/-! ## The two sines -/

theorem sin_sq_pi_div_five : Real.sin (π / 5) ^ 2 = (5 - Real.sqrt 5) / 8 := by
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h := Real.sin_sq_add_cos_sq (π / 5)
  rw [Real.cos_pi_div_five] at h
  linear_combination h - (1 / 16 : ℝ) * s5

theorem sin_sq_two_pi_div_five : Real.sin (2 * π / 5) ^ 2 = (5 + Real.sqrt 5) / 8 := by
  have h := sin_sq_pi_div_five_add
  rw [sin_sq_pi_div_five] at h
  linear_combination h

theorem sin_pi_div_five_pos : 0 < Real.sin (π / 5) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

theorem sin_two_pi_div_five_pos : 0 < Real.sin (2 * π / 5) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

theorem sin_pi_div_five_eq : Real.sin (π / 5) = Real.sqrt ((5 - Real.sqrt 5) / 8) := by
  rw [← sin_sq_pi_div_five, Real.sqrt_sq sin_pi_div_five_pos.le]

theorem sin_two_pi_div_five_eq : Real.sin (2 * π / 5) = Real.sqrt ((5 + Real.sqrt 5) / 8) := by
  rw [← sin_sq_two_pi_div_five, Real.sqrt_sq sin_two_pi_div_five_pos.le]

/-! ## Bounds on `κ` -/

theorem kappa_den_pos : 0 < Real.sqrt 5 + 2 * Real.sin (2 * π / 5) := by
  have := sin_two_pi_div_five_pos
  positivity

theorem kappa_pos : 0 < kappa :=
  div_pos (by linarith [sin_pi_div_five_pos]) kappa_den_pos

theorem sqrt_five_gt : (22360679 : ℝ) / 10000000 < Real.sqrt 5 :=
  (Real.lt_sqrt (by norm_num)).2 (by norm_num)

theorem sqrt_five_lt : Real.sqrt 5 < (2236068 : ℝ) / 1000000 :=
  (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

theorem sin_pi_div_five_gt : (5877852 : ℝ) / 10000000 < Real.sin (π / 5) :=
  lt_of_pow_lt_pow_left₀ 2 sin_pi_div_five_pos.le (by
    rw [sin_sq_pi_div_five]; nlinarith [sqrt_five_lt])

theorem sin_pi_div_five_lt : Real.sin (π / 5) < (5877853 : ℝ) / 10000000 :=
  lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by
    rw [sin_sq_pi_div_five]; nlinarith [sqrt_five_gt])

theorem sin_two_pi_div_five_gt : (9510565 : ℝ) / 10000000 < Real.sin (2 * π / 5) :=
  lt_of_pow_lt_pow_left₀ 2 sin_two_pi_div_five_pos.le (by
    rw [sin_sq_two_pi_div_five]; nlinarith [sqrt_five_gt])

theorem sin_two_pi_div_five_lt : Real.sin (2 * π / 5) < (9510566 : ℝ) / 10000000 :=
  lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by
    rw [sin_sq_two_pi_div_five]; nlinarith [sqrt_five_lt])

theorem kappa_gt : (28407 : ℝ) / 100000 < kappa := by
  unfold kappa
  rw [lt_div_iff₀ kappa_den_pos]
  linarith [sqrt_five_lt, sin_two_pi_div_five_lt, sin_pi_div_five_gt]

theorem kappa_lt : kappa < (28408 : ℝ) / 100000 := by
  unfold kappa
  rw [div_lt_iff₀ kappa_den_pos]
  linarith [sqrt_five_gt, sin_two_pi_div_five_gt, sin_pi_div_five_lt]

/-! ## The normalised coefficients `u(n)` -/

/-- `a(n) = 2((1 + Re ε) Re χ₅(n) + Im ε · Im χ₅(n))`, real. -/
theorem aDH_chi5_eq (n : ℕ) : aDH chi5 n =
    ((2 * ((1 + 2 * Real.sin (2 * π / 5) / Real.sqrt 5) * (chi5 n).re
      + 2 * Real.sin (π / 5) / Real.sqrt 5 * (chi5 n).im) : ℝ) : ℂ) := by
  simp only [aDH, chi5_inv_apply, rootNumber_chi5_inv_eq_conj, rootNumber_chi5_eq]
  apply Complex.ext <;>
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
    Complex.one_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, map_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I] <;> ring

/-- `κ (1 + Re ε) = Im ε`. -/
theorem kappa_mul_one_add :
    kappa * (1 + 2 * Real.sin (2 * π / 5) / Real.sqrt 5) = 2 * Real.sin (π / 5) / Real.sqrt 5 := by
  have h5 : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hd := kappa_den_pos.ne'
  unfold kappa
  field_simp

theorem uDH_chi5_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    uDH chi5 n = (((chi5 n).re + kappa * (chi5 n).im : ℝ) : ℂ) := by
  simp only [uDH, hn, ↓reduceIte]
  rw [aDH_chi5_eq, aDH_chi5_eq, ← Complex.ofReal_div]
  congr 1
  simp only [Nat.cast_one, chi5_apply_one, Complex.one_re, Complex.one_im]
  have hA : 0 < 1 + 2 * Real.sin (2 * π / 5) / Real.sqrt 5 :=
    add_pos one_pos (div_pos (by linarith [sin_two_pi_div_five_pos]) (Real.sqrt_pos.2 (by norm_num)))
  rw [div_eq_iff (by nlinarith)]
  linear_combination (-2 * (chi5 n).im) * kappa_mul_one_add

theorem chi5_re_add_kappa_im (n : ℕ) :
    (chi5 n).re + kappa * (chi5 n).im = uval (n % 5) := by
  rw [← ZMod.natCast_mod n 5]
  have h : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize n % 5 = r at h ⊢
  interval_cases r <;> simp [uval]

/-- `u(n) = a(n)/a(1)` takes the values `0, 1, κ, −κ, −1` by `n mod 5` (and `0` for `n < 2`). -/
theorem uDH_chi5_eq (n : ℕ) : uDH chi5 n = if n < 2 then 0 else ((uval (n % 5) : ℝ) : ℂ) := by
  split_ifs with h
  · simp [uDH, show ¬ 2 ≤ n by omega]
  · rw [uDH_chi5_of_two_le (by omega), chi5_re_add_kappa_im]

theorem uR_eq (n : ℕ) : uR n = if n < 2 then 0 else uval (n % 5) := by
  show (uDH chi5 n).re = _
  rw [uDH_chi5_eq]
  split_ifs <;> simp

theorem uDH_chi5_eq_ofReal (n : ℕ) : uDH chi5 n = (uR n : ℂ) :=
  (Complex.conj_eq_iff_re.1 (conjFixed_uDH_chi5 n)).symm

theorem dinv_uDH_chi5_eq_ofReal (n : ℕ) : DInv.dinv (uDH chi5) n = (dinvR n : ℂ) :=
  (Complex.conj_eq_iff_re.1 (conjFixed_uDH_chi5.dinv n)).symm

theorem dinvR_zero : dinvR 0 = 0 := by
  show (DInv.dinv (uDH chi5) 0).re = 0
  rw [DInv.dinv_zero, Complex.zero_re]

theorem dinvR_one : dinvR 1 = 1 := by
  show (DInv.dinv (uDH chi5) 1).re = 1
  rw [DInv.dinv_one, Complex.one_re]

theorem dinvR_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    dinvR n = -∑ p ∈ n.divisorsAntidiagonal with p.1 ≠ 1, uR p.1 * dinvR p.2 := by
  show (DInv.dinv (uDH chi5) n).re = _
  rw [DInv.dinv_of_two_le _ hn, Complex.neg_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [uDH_chi5_eq_ofReal, dinv_uDH_chi5_eq_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- `c(n) = Σ_{de = n} log d · (δ(d) + u(d)) · dinv(e)`, real form. -/
theorem fDH_eq (n : ℕ) : fDH n = ∑ p ∈ n.divisorsAntidiagonal,
    Real.log p.1 * ((if p.1 = 1 then 1 else 0) + uR p.1) * dinvR p.2 := by
  show (cDH chi5 n).re = _
  simp only [cDH, LSeries.convolution_def, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [LSeries.logMul, Pi.add_apply, LSeries.delta]
  rw [← Complex.natCast_log, uDH_chi5_eq_ofReal, dinv_uDH_chi5_eq_ofReal]
  split_ifs
  · rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  · rw [← Complex.ofReal_zero, ← Complex.ofReal_add, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.ofReal_re]

/-! ## The prime sum is finite -/

theorem cDH_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : cDH χ 1 = 0 := by
  unfold cDH
  rw [LSeries.convolution_def]
  simp [Nat.divisorsAntidiagonal_one, LSeries.logMul]

theorem cDH_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : cDH χ 0 = 0 := by
  unfold cDH
  exact LSeries.convolution_map_zero _ _

theorem fDH_zero : fDH 0 = 0 := by
  simp [fDH, cDH_zero]

theorem fDH_one : fDH 1 = 0 := by
  simp [fDH, cDH_one]

/-- The prime sum of `QDHu` is finite when the autocorrelation vanishes beyond `log N`. -/
theorem tsum_fDH_eq_sum {g : ℝ → ℝ} {N : ℕ} (hsupp : ∀ n : ℕ, N < n → autocorr g (Real.log n) = 0) :
    ∑' n : ℕ, fDH n / Real.sqrt n * autocorr g (Real.log n)
      = ∑ n ∈ Finset.Icc 2 N, fDH n / Real.sqrt n * autocorr g (Real.log n) := by
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  rcases hn with hn | hn
  · interval_cases n
    · simp
    · simp [fDH_one]
  · simp [hsupp n hn]

theorem QDHu_eq_sum {g : ℝ → ℝ} {N : ℕ} (hsupp : ∀ n : ℕ, N < n → autocorr g (Real.log n) = 0) :
    QDHu g = ((Complex.digamma (3 / 4 : ℂ)).re + Real.log 5 - Real.log π) * normSq g + archEQ (3 / 4) g
      - 2 * ∑ n ∈ Finset.Icc 2 N, fDH n / Real.sqrt n * autocorr g (Real.log n) := by
  unfold QDHu
  rw [tsum_fDH_eq_sum hsupp]

/-- Beyond `⌊e^{2a}⌋` the logarithm is at least `2a`. -/
theorem two_mul_le_log_of_floor_exp_lt {a : ℝ} {n : ℕ} (h : ⌊Real.exp (2 * a)⌋₊ < n) :
    2 * a ≤ Real.log n := by
  have he : Real.exp (2 * a) < n := (Nat.floor_lt (Real.exp_pos _).le).1 h
  have hn : (0 : ℝ) < n := (Real.exp_pos _).trans he
  exact (Real.le_log_iff_exp_le hn).2 he.le


/-! ## The assembled closed form -/

/-- **Weil's form of `dh` on the packet, in closed form.** -/
theorem QDHu_packet_eq {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    QDHu (packet a ω) = ((Complex.digamma (3 / 4 : ℂ)).re + Real.log 5 - Real.log π)
        * (a + Real.sin (2 * ω * a) / (2 * ω)) + archEQ (3 / 4) (packet a ω)
      - 2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, fDH n / Real.sqrt n
          * ((2 * a - Real.log n) / 2 * Real.cos (ω * Real.log n)
            + Real.sin (ω * (2 * a - Real.log n)) / (2 * ω)) := by
  have hsupp : ∀ n : ℕ, ⌊Real.exp (2 * a)⌋₊ < n → autocorr (packet a ω) (Real.log n) = 0 :=
    fun n hn => packet_autocorr_of_le ha (two_mul_le_log_of_floor_exp_lt hn)
  rw [QDHu_eq_sum hsupp, packet_normSq ha hω]
  have e : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, fDH n / Real.sqrt n * autocorr (packet a ω) (Real.log n)
      = ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, fDH n / Real.sqrt n
          * ((2 * a - Real.log n) / 2 * Real.cos (ω * Real.log n)
            + Real.sin (ω * (2 * a - Real.log n)) / (2 * ω)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have h2 : 2 ≤ n := (Finset.mem_Icc.1 hn).1
    have hN : n ≤ ⌊Real.exp (2 * a)⌋₊ := (Finset.mem_Icc.1 hn).2
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hlog : Real.log n ≤ 2 * a := by
      have hle : (n : ℝ) ≤ Real.exp (2 * a) :=
        (Nat.cast_le.2 hN).trans (Nat.floor_le (Real.exp_pos _).le)
      calc Real.log n ≤ Real.log (Real.exp (2 * a)) :=
            Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) hle
        _ = 2 * a := Real.log_exp _
    rw [packet_autocorr ha hω hlog0 hlog]
  rw [e]

/-- **The explicit formula on the packet**: `Q_dh(g) = Σ_u 2ĝ(3τ_u)²`. -/
theorem packet_QDHu_hasSum {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    HasSum (fun i : ZeroIdx (sqF XiDH3) => 2 * ghatC (packet a ω) a (3 * tau3 i) ^ 2)
      (QDHu (packet a ω) : ℂ) := by
  obtain ⟨K, hK⟩ := packet_striptest ha hω
  exact QDHu_hasSum (packet_probe ha hω.le) ha hK

/-- **A negative Weil form on a packet certifies an off-line zero of `dh`.** -/
theorem exists_offline_dh_of_neg_packet {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω)
    (hneg : QDHu (packet a ω) < 0) : ∃ s : ℂ, dh s = 0 ∧ 0 < s.re ∧ s.re ≠ 1 / 2 := by
  obtain ⟨K, hK⟩ := packet_striptest ha hω
  exact exists_offline_dh_of_neg_u (packet_probe ha hω.le) ha hK hneg

end PsiOmega

#print axioms PsiOmega.packet_probe
#print axioms PsiOmega.packet_autocorr
#print axioms PsiOmega.packet_normSq
#print axioms PsiOmega.packet_ghatC
#print axioms PsiOmega.packet_striptest
#print axioms PsiOmega.kappa_gt
#print axioms PsiOmega.kappa_lt
#print axioms PsiOmega.uDH_chi5_eq
#print axioms PsiOmega.dinvR_of_two_le
#print axioms PsiOmega.fDH_eq
#print axioms PsiOmega.tsum_fDH_eq_sum
#print axioms PsiOmega.QDHu_eq_sum
#print axioms PsiOmega.QDHu_packet_eq
#print axioms PsiOmega.packet_QDHu_hasSum
#print axioms PsiOmega.exists_offline_dh_of_neg_packet
