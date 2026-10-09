import Mathlib
import DHPacket
import DHArch
import DHConstants
import DHCertificate
import DHForm
import DHOddTerms
import ParitySplit

/-! # The sine packet: Weil's form of `dh` is negative on an odd probe (round 269)

The cosine packet `packet a ω = 1_{[−a,a]}·cos(ω·)` certifies `Q_dh < 0` on an even probe
(`QDHu_packet_neg`, DHCertificate.lean). This file is the same certificate for the **odd** packet
`sinPacket a ω = 1_{[−a,a]}·sin(ω·)` at the same `(a, ω) = (12/5, 169/2)`.

**Closed forms** (every `0 < a`, `0 < ω`): `‖g‖² = a − sin(2ωa)/(2ω)` (`sinPacket_normSq`),
`f(u) = ½(2a − u) cos(ωu) − sin(ω(2a − u))/(2ω)` on `0 ≤ u ≤ 2a` and `0` beyond (`sinPacket_autocorr`,
`sinPacket_autocorr_of_le`: the cosine packet's autocorrelation with the sidelobe sign flipped),
`ĝ(z) = i[sin((z − ω)a)/(z − ω) − sin((z + ω)a)/(z + ω)]` (`sinPacket_ghatC`), the width-3 strip test
(`sinPacket_striptest`), and the odd probe (`sinPacket_oprobe : OProbe a (sinPacket a ω)`).
**The form** (`QDHu_sinPacket_eq`): `QDHu` has no pole term (`dh` is entire), so on an odd `g` it is the
same expression as on an even one,
`Q_dh(g) = (Re ψ(¾) + log(5/π))(a − sin(2ωa)/(2ω)) + E_{3/4}(g) − 2 Σ_{2 ≤ n ≤ ⌊e^{2a}⌋} c(n) n^{−1/2} f(log n)`.
**The archimedean bound** (`sinPacket_archEQ_le`, `sinPacket_arch_total_le`): on `(0, 2a]`,
`f(0) − f(u) = f(0)(1 − cos ωu) + (u/2) cos ωu + β′ sin ωu` with `β′ = −cos(2ωa)/(2ω)` (the even
packet has `β = +cos(2ωa)/(2ω)`), and DHArch's kernel lemmas bound every piece exactly as for the cosine
packet, since only `|β′| = |β| ≤ 1/(2ω)` enters.
**The certificate** (`QDHu_sinPacket_le`): `Q_dh(sinPacket 12/5 169/2) ≤ −111/100`, from the generated
`oddPartial_121` (DHOddTerms.lean, `gen_oddterms.py`) and DHConstants' bounds; numerically
`Q_dh = −1.24351…` (`−0.51771‖g‖²`, `‖g‖² = 2.4019428…`).
**The `dh` column of `rh_of_lamO_lower`** (`not_odd_lower_dh`, `not_lamODH_lower`): `QDHu` sees the probe,
not the window, so the normalised sine packet is a negative odd unit probe at every `b ≥ 12/5`
(`exists_oprobe_QDHu_neg`), the odd ground energy `λ_dh^odd(b)` (`lamODH`) is negative there (`lamODH_neg`),
and no positive lower bound `c·e^{(9+δ)b − 4πe^{2b}}` on the odd sector of `dh` holds eventually.
-/

open Real Complex MeasureTheory Set Filter Topology

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-! ## The sine packet -/

/-- The odd box wave packet `sin(ωu)·1_{[−a,a]}`. -/
def sinPacket (a ω : ℝ) : ℝ → ℝ := Set.indicator (Icc (-a) a) fun u => Real.sin (ω * u)

theorem sinPacket_apply (a ω u : ℝ) :
    sinPacket a ω u = if |u| ≤ a then Real.sin (ω * u) else 0 := by
  unfold sinPacket
  rw [Set.indicator_apply]
  congr 1
  simp [abs_le]

theorem sinPacket_of_le {a ω u : ℝ} (hu : |u| ≤ a) : sinPacket a ω u = Real.sin (ω * u) := by
  simp [sinPacket_apply, hu]

theorem sinPacket_of_lt {a ω u : ℝ} (hu : a < |u|) : sinPacket a ω u = 0 := by
  simp [sinPacket_apply, not_le.2 hu]

theorem sinPacket_odd (a ω u : ℝ) : sinPacket a ω (-u) = -sinPacket a ω u := by
  rw [sinPacket_apply, sinPacket_apply, abs_neg, mul_neg, Real.sin_neg]
  split_ifs <;> simp

/-! ## Closed forms of the autocorrelation and the norm -/

/-- For `0 ≤ u`, `g(t) g(t + u) = 1_{[−a, a−u]}(t) sin(ωt) sin(ω(t+u))`. -/
theorem sinPacket_mul_shift (a ω : ℝ) {u : ℝ} (hu0 : 0 ≤ u) (t : ℝ) :
    sinPacket a ω t * sinPacket a ω (t + u) =
      (Icc (-a) (a - u)).indicator (fun t => Real.sin (ω * t) * Real.sin (ω * (t + u))) t := by
  rw [sinPacket_apply, sinPacket_apply, Set.indicator_apply]
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

/-- For `0 ≤ u`, the autocorrelation is the integral of `sin(ωt) sin(ω(t+u))` over `[−a, a−u]`. -/
theorem sinPacket_autocorr_Icc (a ω : ℝ) {u : ℝ} (hu0 : 0 ≤ u) :
    autocorr (sinPacket a ω) u =
      ∫ t in Icc (-a) (a - u), Real.sin (ω * t) * Real.sin (ω * (t + u)) := by
  unfold autocorr
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  funext t
  exact sinPacket_mul_shift a ω hu0 t

/-- `sin(ωt) sin(ω(t+u)) = ½ cos(ωu) − ½ cos(ω(2t+u))`. -/
theorem sin_mul_sin_shift (ω t u : ℝ) :
    Real.sin (ω * t) * Real.sin (ω * (t + u)) =
      Real.cos (ω * u) / 2 - Real.cos (ω * (2 * t + u)) / 2 := by
  have h1 : ω * u = ω * (t + u) - ω * t := by ring
  have h2 : ω * (2 * t + u) = ω * (t + u) + ω * t := by ring
  rw [h1, h2, Real.cos_sub, Real.cos_add]
  ring

/-- `f(u) = ½(2a − u) cos(ωu) − sin(ω(2a − u))/(2ω)` on `0 ≤ u ≤ 2a`. -/
theorem sinPacket_autocorr {a ω : ℝ} (hω : 0 < ω) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 2 * a) :
    autocorr (sinPacket a ω) u
      = (2 * a - u) / 2 * Real.cos (ω * u) - Real.sin (ω * (2 * a - u)) / (2 * ω) := by
  have hle : -a ≤ a - u := by linarith
  rw [sinPacket_autocorr_Icc a ω hu0, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hω0 : ω ≠ 0 := hω.ne'
  have hderiv : ∀ t ∈ uIcc (-a) (a - u),
      HasDerivAt (fun t => Real.cos (ω * u) * t / 2 - Real.sin (ω * (2 * t + u)) / (4 * ω))
        (Real.sin (ω * t) * Real.sin (ω * (t + u))) t := by
    intro t _
    rw [sin_mul_sin_shift]
    have hlin : HasDerivAt (fun t : ℝ => ω * (2 * t + u)) (ω * 2) t := by
      have := ((hasDerivAt_id t).const_mul 2).add_const u
      simpa using this.const_mul ω
    have h1 : HasDerivAt (fun x : ℝ => Real.cos (ω * u) * x / 2) (Real.cos (ω * u) / 2) t := by
      simpa using ((hasDerivAt_id t).const_mul (Real.cos (ω * u))).div_const 2
    have h2 : HasDerivAt (fun x : ℝ => Real.sin (ω * (2 * x + u)) / (4 * ω))
        (Real.cos (ω * (2 * t + u)) / 2) t := by
      have := ((Real.hasDerivAt_sin (ω * (2 * t + u))).comp t hlin).div_const (4 * ω)
      exact this.congr_deriv (by field_simp; ring)
    exact h1.sub h2
  have hcont : Continuous fun t : ℝ => Real.sin (ω * t) * Real.sin (ω * (t + u)) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  have e1 : ω * (2 * (a - u) + u) = ω * (2 * a - u) := by ring
  have e2 : ω * (2 * -a + u) = -(ω * (2 * a - u)) := by ring
  rw [e1, e2, Real.sin_neg]
  field_simp
  ring

/-- For `u ≥ 2a` the autocorrelation vanishes (the overlap `[−a, a−u]` is null). -/
theorem sinPacket_autocorr_of_le {a ω : ℝ} (ha : 0 < a) {u : ℝ} (hu : 2 * a ≤ u) :
    autocorr (sinPacket a ω) u = 0 := by
  rw [sinPacket_autocorr_Icc a ω (by linarith)]
  apply setIntegral_measure_zero
  rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
  linarith

/-- `‖g‖² = a − sin(2ωa)/(2ω)`. -/
theorem sinPacket_normSq {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    normSq (sinPacket a ω) = a - Real.sin (2 * ω * a) / (2 * ω) := by
  rw [← autocorr_zero, sinPacket_autocorr hω le_rfl (by linarith)]
  rw [mul_zero, Real.cos_zero, mul_one, sub_zero, show ω * (2 * a) = 2 * ω * a by ring]
  ring

/-! ## The sine packet is an odd probe -/

theorem sinPacket_memLp (a ω : ℝ) : MemLp (sinPacket a ω) 2 volume := by
  unfold sinPacket
  exact memLp_indicator_of_continuous (f := fun u => Real.sin (ω * u)) (by fun_prop)
    measurableSet_Icc measure_Icc_lt_top.ne (C := 1) fun x _ => Real.abs_sin_le_one _

theorem sinPacket_measurable (a ω : ℝ) : Measurable (sinPacket a ω) := by
  unfold sinPacket
  exact (by fun_prop : Measurable fun u => Real.sin (ω * u)).indicator measurableSet_Icc

theorem sinPacket_integrable (a ω : ℝ) : Integrable (sinPacket a ω) := by
  unfold sinPacket
  exact (Continuous.integrableOn_Icc (by fun_prop)).integrable_indicator measurableSet_Icc

/-- `f(0) − f(u) ≤ (aω² u + 1) u` for `u ≥ 0`: the shifted packet differs by at most `ωu` inside and by at
most `1` on two edge intervals of length `u`. -/
theorem sinPacket_autocorr_diff_le {a ω : ℝ} (ha : 0 < a) (hω : 0 ≤ ω) {u : ℝ} (hu : 0 ≤ u) :
    autocorr (sinPacket a ω) 0 - autocorr (sinPacket a ω) u ≤ (a * ω ^ 2 * u + 1) * u := by
  have hb := sinPacket_memLp a ω
  rw [show autocorr (sinPacket a ω) 0 - autocorr (sinPacket a ω) u
      = normSq (fun t => sinPacket a ω t - sinPacket a ω (t + u)) / 2 by
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
  have hpt : ∀ t, (sinPacket a ω t - sinPacket a ω (t + u)) ^ 2 ≤ B t := by
    intro t
    have i1 := hnn (Icc (-a) a) t
    have i2 := hnn (Icc (a - u) a) t
    have i3 := hnn (Icc (-a - u) (-a)) t
    have hwu : 0 ≤ ω ^ 2 * u ^ 2 := by positivity
    simp only [hB]
    rw [sinPacket_apply, sinPacket_apply]
    by_cases h1 : |t| ≤ a <;> by_cases h2 : |t + u| ≤ a
    · simp only [h1, h2, ite_true]
      have hc := Real.abs_sin_sub_sin_le (ω * t) (ω * (t + u))
      have e : |ω * t - ω * (t + u)| = ω * u := by
        rw [show ω * t - ω * (t + u) = -(ω * u) by ring, abs_neg,
          abs_of_nonneg (mul_nonneg hω hu)]
      rw [e] at hc
      have hsq : (Real.sin (ω * t) - Real.sin (ω * (t + u))) ^ 2 ≤ ω ^ 2 * u ^ 2 := by
        rw [← sq_abs]
        calc |Real.sin (ω * t) - Real.sin (ω * (t + u))| ^ 2 ≤ (ω * u) ^ 2 :=
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
      have := Real.sin_sq_le_one (ω * t)
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
      have := Real.sin_sq_le_one (ω * (t + u))
      nlinarith
    · simp only [h1, h2, ite_false, sub_self]
      nlinarith
  have hle : normSq (fun t => sinPacket a ω t - sinPacket a ω (t + u)) ≤ ∫ t, B t :=
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

theorem sinPacket_arch {a ω : ℝ} (ha : 0 < a) (hω : 0 ≤ ω) :
    IntegrableOn (archIntegrand (sinPacket a ω)) (Set.Ioi 0) := by
  have hm : AEStronglyMeasurable (archIntegrand (sinPacket a ω)) (volume.restrict (Ioi 0)) := by
    have h1 := (autocorr_stronglyMeasurable (sinPacket_measurable a ω)).measurable
    have : Measurable (archIntegrand (sinPacket a ω)) := by
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
  rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg (sinPacket_memLp a ω) hu0)]
  unfold archIntegrand
  have hA : 0 ≤ a * ω ^ 2 := by positivity
  have hpoly : a * ω ^ 2 * u + 1 ≤ (8 * (a * ω ^ 2) + 1) * Real.exp (1 / 8 * u) := by
    have e1 := Real.add_one_le_exp (1 / 8 * u)
    have e2 : 1 ≤ Real.exp (1 / 8 * u) := Real.one_le_exp (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left e1 hA]
  have hexp : Real.exp (1 / 8 * u) * Real.exp (-(1 / 4) * u) = Real.exp (-(1 / 8) * u) := by
    rw [← Real.exp_add]; ring_nf
  calc (autocorr (sinPacket a ω) 0 - autocorr (sinPacket a ω) u) * (Real.exp (u / 2) / Real.sinh u)
      ≤ ((a * ω ^ 2 * u + 1) * u) * (Real.exp (u / 2) / Real.sinh u) :=
        mul_le_mul_of_nonneg_right (sinPacket_autocorr_diff_le ha hω hu0.le) hK.le
    _ = (a * ω ^ 2 * u + 1) * (u * (Real.exp (u / 2) / Real.sinh u)) := by ring
    _ ≤ (a * ω ^ 2 * u + 1) * (16 * Real.exp (-(1 / 4) * u)) :=
        mul_le_mul_of_nonneg_left (u_archK_le hu0) (by positivity)
    _ ≤ ((8 * (a * ω ^ 2) + 1) * Real.exp (1 / 8 * u)) * (16 * Real.exp (-(1 / 4) * u)) :=
        mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = 16 * (8 * (a * ω ^ 2) + 1) * Real.exp (-(1 / 8) * u) := by rw [← hexp]; ring

/-- **The sine packet is an odd probe.** -/
theorem sinPacket_oprobe {a ω : ℝ} (ha : 0 < a) (hω : 0 ≤ ω) : OProbe a (sinPacket a ω) :=
  ⟨sinPacket_odd a ω, fun _ hu => sinPacket_of_lt hu, sinPacket_memLp a ω, sinPacket_arch ha hω⟩

/-! ## The transform and the width-3 strip test -/

/-- `ĝ(z) = i[sin((z − ω)a)/(z − ω) − sin((z + ω)a)/(z + ω)]`. -/
theorem sinPacket_ghatC {a ω : ℝ} (ha : 0 ≤ a) (z : ℂ) (h1 : z + ω ≠ 0) (h2 : z - ω ≠ 0) :
    ghatC (sinPacket a ω) a z
      = Complex.I * (Complex.sin ((z - ω) * a) / (z - ω) - Complex.sin ((z + ω) * a) / (z + ω)) := by
  unfold ghatC
  have hcongr : EqOn (fun u : ℝ => ((sinPacket a ω u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u))
      (fun u : ℝ => (Complex.exp (Complex.I * (z - ω) * u) - Complex.exp (Complex.I * (z + ω) * u))
        * Complex.I / 2)
      (Set.uIcc (-a) a) := by
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    have hu' : |u| ≤ a := abs_le.2 hu
    simp only
    rw [sinPacket_of_le hu', Complex.ofReal_sin, Complex.sin]
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
    intervalIntegral.integral_mul_const,
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cexp_I_mul h2, integral_cexp_I_mul h1]
  ring

/-- **`ĝ(3z)²` is a strip test function** for the sine packet. -/
theorem sinPacket_striptest {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    ∃ K, StripTest (fun z => ghatC (sinPacket a ω) a (3 * z) ^ 2) K := by
  have hint : IntervalIntegrable (sinPacket a ω) volume (-a) a :=
    (sinPacket_integrable a ω).intervalIntegrable
  set τ0 := Real.exp (3 * a) * ∫ u in (-a)..a, |sinPacket a ω u| with hτ0
  have hI : 0 ≤ ∫ u in (-a)..a, |sinPacket a ω u| :=
    intervalIntegral.integral_nonneg (by linarith) fun u _ => abs_nonneg _
  have hτ0nn : 0 ≤ τ0 := mul_nonneg (Real.exp_pos _).le hI
  refine ⟨τ0 ^ 2 + ((1 + ω) / 3 * (2 * Real.exp (3 * a) + τ0)) ^ 2,
    striptest_sq ((ghatC_differentiable hint).comp (differentiable_id.const_mul 3))
      fun t ht => ?_⟩
  have h3im : (3 * t).im = 3 * t.im := by simp
  have htim : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  have h3 : |(3 * t).im| ≤ 3 := by
    rw [h3im, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith
  have hG0 : ‖ghatC (sinPacket a ω) a (3 * t)‖ ≤ τ0 := by
    refine (norm_ghatC_le_exp_im ha.le hint _).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hI
    linarith [mul_le_mul_of_nonneg_left h3 ha.le]
  refine sq_strip_bound hG0 ?_
  show ‖t‖ * ‖ghatC (sinPacket a ω) a (3 * t)‖ ≤ _
  have hn3 : ‖(3 : ℂ) * t‖ = 3 * ‖t‖ := by rw [norm_mul]; norm_num
  have hnω : ‖(ω : ℂ)‖ = ω := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
  have hGn := norm_nonneg (ghatC (sinPacket a ω) a (3 * t))
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
    rw [sinPacket_ghatC ha.le _ hp0 hm0]
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
    calc ‖t‖ * ‖Complex.I * (Complex.sin ((3 * t - ω) * a) / (3 * t - ω)
          - Complex.sin ((3 * t + ω) * a) / (3 * t + ω))‖
        = ‖t‖ * ‖Complex.sin ((3 * t - ω) * a) / (3 * t - ω)
          - Complex.sin ((3 * t + ω) * a) / (3 * t + ω)‖ := by
          rw [norm_mul Complex.I, Complex.norm_I, one_mul]
      _ ≤ ‖t‖ * (‖Complex.sin ((3 * t - ω) * a) / (3 * t - ω)‖
          + ‖Complex.sin ((3 * t + ω) * a) / (3 * t + ω)‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) htn
      _ ≤ (1 + ω) / 3 * Real.exp (3 * a) + (1 + ω) / 3 * Real.exp (3 * a) := by
          rw [mul_add]; exact add_le_add hq2 hq1
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
    calc ‖t‖ * ‖ghatC (sinPacket a ω) a (3 * t)‖ ≤ (1 + ω) / 3 * τ0 :=
          mul_le_mul htsmall hG0 hGn (by linarith)
      _ ≤ (1 + ω) / 3 * (2 * Real.exp (3 * a) + τ0) := by
          have := Real.exp_pos (3 * a)
          nlinarith

/-! ## The assembled closed form -/

/-- **Weil's form of `dh` on the sine packet, in closed form.** -/
theorem QDHu_sinPacket_eq {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    QDHu (sinPacket a ω) = ((Complex.digamma (3 / 4 : ℂ)).re + Real.log 5 - Real.log π)
        * (a - Real.sin (2 * ω * a) / (2 * ω)) + archEQ (3 / 4) (sinPacket a ω)
      - 2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, fDH n / Real.sqrt n
          * ((2 * a - Real.log n) / 2 * Real.cos (ω * Real.log n)
            - Real.sin (ω * (2 * a - Real.log n)) / (2 * ω)) := by
  have hsupp : ∀ n : ℕ, ⌊Real.exp (2 * a)⌋₊ < n → autocorr (sinPacket a ω) (Real.log n) = 0 :=
    fun n hn => sinPacket_autocorr_of_le ha (two_mul_le_log_of_floor_exp_lt hn)
  rw [QDHu_eq_sum hsupp, sinPacket_normSq ha hω]
  have e : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, fDH n / Real.sqrt n
        * autocorr (sinPacket a ω) (Real.log n)
      = ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, fDH n / Real.sqrt n
          * ((2 * a - Real.log n) / 2 * Real.cos (ω * Real.log n)
            - Real.sin (ω * (2 * a - Real.log n)) / (2 * ω)) := by
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
    rw [sinPacket_autocorr hω hlog0 hlog]
  rw [e]

/-! ## The archimedean term of the sine packet -/

/-- **Integrability for `q ≥ ¼`** on an odd probe (`archIntegrandQ_integrable` uses only the
archimedean condition). -/
theorem oprobe_archIntegrandQ_integrable {a q : ℝ} {g : ℝ → ℝ} (hp : OProbe a g) (hq : 1 / 4 ≤ q) :
    IntegrableOn (archIntegrandQ q g) (Ioi 0) := by
  have hb : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), ‖Real.exp ((1 / 2 - 2 * q) * u)‖ ≤ 1 := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hu)
  refine (hp.arch.mul_bdd (Continuous.aestronglyMeasurable (by fun_prop)) hb).congr
    (Eventually.of_forall fun u => ?_)
  simp only [archIntegrand, archIntegrandQ, archKer]
  rw [mul_assoc, div_mul_eq_mul_div, ← Real.exp_add]
  congr 3; ring

/-- `‖g‖² = a − sin(2ωa)/(2ω) ≥ 0` once `2aω ≥ 1`. -/
theorem sinPacket_f0_nonneg {a ω : ℝ} (hω : 0 < ω) (h1 : 1 ≤ 2 * a * ω) :
    0 ≤ a - Real.sin (2 * ω * a) / (2 * ω) := by
  have h2ω : 0 < 2 * ω := by positivity
  have hs : Real.sin (2 * ω * a) / (2 * ω) ≤ 1 / (2 * ω) :=
    div_le_div_of_nonneg_right (Real.sin_le_one _) h2ω.le
  have ha : 1 / (2 * ω) ≤ a := by
    rw [div_le_iff₀ h2ω]; linarith
  linarith

/-- **The archimedean term of the sine packet**: with `f₀ = a − sin(2ωa)/(2ω)`,
`E_{3/4}(g) ≤ f₀·[Re ψ(¾ + iω/2) − ψ(¾)] + f₀·(4/3)e^{−3a}/(1 − e^{−4a}) + 1/(2ω) + (1 + log(2aω))/(2ω)`.
On `(0, 2a]`, `f(0) − f(u) = f₀(1 − cos ωu) + (u/2) cos ωu + β′ sin ωu` with `β′ = −cos(2ωa)/(2ω)`. -/
theorem sinPacket_archEQ_le {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) (h1 : 1 ≤ 2 * a * ω) :
    archEQ (3 / 4) (sinPacket a ω)
      ≤ (a - Real.sin (2 * ω * a) / (2 * ω)) * (psiReQ (3 / 4) ω - psiReQ (3 / 4) 0)
        + (a - Real.sin (2 * ω * a) / (2 * ω)) * (4 / 3 * Real.exp (-(3 * a)) / (1 - Real.exp (-(4 * a))))
        + 1 / (2 * ω) + (1 + Real.log (2 * a * ω)) / (2 * ω) := by
  have hf0nn := sinPacket_f0_nonneg hω h1
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : ℝ, a - Real.sin (2 * ω * a) / (2 * ω) = f₀ := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, -(Real.cos (2 * ω * a) / (2 * ω)) = β := ⟨_, rfl⟩
  rw [hf₀] at hf0nn ⊢
  have h2a : (0 : ℝ) ≤ 2 * a := by linarith
  have h2ω : 0 < 2 * ω := by positivity
  have hF := oprobe_archIntegrandQ_integrable (q := 3 / 4) (sinPacket_oprobe ha hω.le) (by norm_num)
  have hA := integrableOn_K_one_sub_cos ω
  have hB := integrableOn_uK_cos (ω := ω) ha
  have hC := integrableOn_K_sin ha hω
  have hKc := integrableOn_K_cos_Ioi ha ω
  have hf0 : autocorr (sinPacket a ω) 0 = f₀ := by rw [autocorr_zero, sinPacket_normSq ha hω, hf₀]
  -- the piece on `(0, 2a]`
  have eIoc : ∫ u in Ioc (0 : ℝ) (2 * a), archIntegrandQ (3 / 4) (sinPacket a ω) u
      = f₀ * (∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * (1 - Real.cos (ω * u)))
        + ((∫ u in Ioc (0 : ℝ) (2 * a), u / 2 * archKer (3 / 4) u * Real.cos (ω * u))
          + β * ∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * Real.sin (ω * u)) := by
    have e : EqOn (archIntegrandQ (3 / 4) (sinPacket a ω))
        (fun u => f₀ * (archKer (3 / 4) u * (1 - Real.cos (ω * u)))
          + (u / 2 * archKer (3 / 4) u * Real.cos (ω * u)
            + β * (archKer (3 / 4) u * Real.sin (ω * u)))) (Ioc 0 (2 * a)) := by
      intro u hu
      simp only [archIntegrandQ]
      rw [hf0, sinPacket_autocorr hω hu.1.le hu.2,
        show ω * (2 * a - u) = 2 * ω * a - ω * u by ring, Real.sin_sub, ← hf₀, ← hβ]
      ring
    have hBC : IntegrableOn (fun u => u / 2 * archKer (3 / 4) u * Real.cos (ω * u)
        + β * (archKer (3 / 4) u * Real.sin (ω * u))) (Ioc 0 (2 * a)) := hB.add (hC.const_mul β)
    rw [setIntegral_congr_fun measurableSet_Ioc e,
      integral_add ((hA.mono_set Ioc_subset_Ioi_self).const_mul f₀) hBC,
      integral_add hB (hC.const_mul β), integral_const_mul, integral_const_mul]
  -- the piece on `(2a, ∞)`
  have eIoi : ∫ u in Ioi (2 * a), archIntegrandQ (3 / 4) (sinPacket a ω) u
      = f₀ * (∫ u in Ioi (2 * a), archKer (3 / 4) u * (1 - Real.cos (ω * u)))
        + f₀ * ∫ u in Ioi (2 * a), archKer (3 / 4) u * Real.cos (ω * u) := by
    have e : EqOn (archIntegrandQ (3 / 4) (sinPacket a ω))
        (fun u => f₀ * (archKer (3 / 4) u * (1 - Real.cos (ω * u)))
          + f₀ * (archKer (3 / 4) u * Real.cos (ω * u))) (Ioi (2 * a)) := by
      intro u hu
      simp only [archIntegrandQ]
      rw [hf0, sinPacket_autocorr_of_le ha (le_of_lt (mem_Ioi.1 hu))]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi e,
      integral_add ((hA.mono_set (Ioi_subset_Ioi h2a)).const_mul f₀) (hKc.const_mul f₀),
      integral_const_mul, integral_const_mul]
  -- recombination
  have hD := psiReQ_three_quarters_sub_u ω
  rw [integral_Ioi_split h2a hA] at hD
  have hsplit : archEQ (3 / 4) (sinPacket a ω)
      = (∫ u in Ioc (0 : ℝ) (2 * a), archIntegrandQ (3 / 4) (sinPacket a ω) u)
        + ∫ u in Ioi (2 * a), archIntegrandQ (3 / 4) (sinPacket a ω) u := by
    unfold archEQ
    exact integral_Ioi_split h2a hF
  -- the three remainders
  have hB' : (∫ u in Ioc (0 : ℝ) (2 * a), u / 2 * archKer (3 / 4) u * Real.cos (ω * u))
      ≤ 1 / (2 * ω) := (le_abs_self _).trans (abs_integral_uK_cos_le ha hω)
  have hβabs : |β| ≤ 1 / (2 * ω) := by
    rw [← hβ, abs_neg, abs_div, abs_of_pos h2ω]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) h2ω.le
  have hlog : 0 ≤ 1 + Real.log (2 * a * ω) := by
    have := Real.log_nonneg h1; linarith
  have hC' : β * (∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * Real.sin (ω * u))
      ≤ (1 + Real.log (2 * a * ω)) / (2 * ω) :=
    calc β * (∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * Real.sin (ω * u))
        ≤ |β * (∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * Real.sin (ω * u))| := le_abs_self _
      _ = |β| * |∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * Real.sin (ω * u)| := abs_mul _ _
      _ ≤ 1 / (2 * ω) * (1 + Real.log (2 * a * ω)) :=
          mul_le_mul hβabs (abs_integral_K_sin_le ha hω h1) (abs_nonneg _) (by positivity)
      _ = (1 + Real.log (2 * a * ω)) / (2 * ω) := by ring
  have hKc' : (∫ u in Ioi (2 * a), archKer (3 / 4) u * Real.cos (ω * u))
      ≤ 4 / 3 * Real.exp (-(3 * a)) / (1 - Real.exp (-(4 * a))) := by
    refine le_trans (setIntegral_mono_on hKc (integrableOn_K_Ioi ha) measurableSet_Ioi
      (fun u hu => ?_)) (integral_K_tail_le ha)
    have hu0 : 0 < u := lt_trans (by linarith) (mem_Ioi.1 hu)
    exact mul_le_of_le_one_right (K_pos hu0).le (Real.cos_le_one _)
  have hKc'' := mul_le_mul_of_nonneg_left hKc' hf0nn
  rw [hsplit, eIoc, eIoi, hD]
  nlinarith [hB', hC', hKc'']

/-- **The archimedean total of the sine packet**: `ψ(¾)‖g‖² + E_{3/4}(g)` against the explicit majorant. -/
theorem sinPacket_arch_total_le {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) (h1 : 1 ≤ 2 * a * ω) :
    (Complex.digamma (3 / 4 : ℂ)).re * (a - Real.sin (2 * ω * a) / (2 * ω)) + archEQ (3 / 4) (sinPacket a ω)
      ≤ (a - Real.sin (2 * ω * a) / (2 * ω)) * (Real.log (Real.sqrt (9 / 16 + ω ^ 2 / 4)) + 3 / ω)
        + (a - Real.sin (2 * ω * a) / (2 * ω)) * (4 / 3 * Real.exp (-(3 * a)) / (1 - Real.exp (-(4 * a))))
        + 1 / (2 * ω) + (1 + Real.log (2 * a * ω)) / (2 * ω) := by
  have hE := sinPacket_archEQ_le ha hω h1
  have hf0nn := sinPacket_f0_nonneg hω h1
  have hψ := mul_le_mul_of_nonneg_left (psiReQ_three_quarters_le hω) hf0nn
  rw [psiReQ_zero, show ((3 / 4 : ℝ) : ℂ) = (3 / 4 : ℂ) by norm_num] at hE
  nlinarith [hE, hψ]

/-! ## The constant `‖g‖² = 12/5 − sin(2028/5)/169` -/

theorem Num.normSq_sinPacket_bounds :
    (2401942 : ℝ) / 10 ^ 6 < 12 / 5 - Real.sin (2028 / 5) / (2 * (169 / 2 : ℝ)) ∧
      12 / 5 - Real.sin (2028 / 5) / (2 * (169 / 2 : ℝ)) < (2401944 : ℝ) / 10 ^ 6 := by
  have h := PsiOmega.Num.twoOmegaA_sin
  constructor <;> nlinarith [h.1, h.2]

/-! ## The certificate -/

/-- **`Q_dh(sinPacket 12/5 169/2) ≤ −111/100`** (numerically `−1.24351`; the bound evaluates to `−1.1149`). -/
theorem QDHu_sinPacket_le : QDHu (sinPacket (12 / 5) (169 / 2)) ≤ -(111 / 100) := by
  rw [QDHu_sinPacket_eq (by norm_num) (by norm_num), floor_exp_twoA]
  have hsum : ∑ n ∈ Finset.Icc 2 121, fDH n / Real.sqrt n
      * ((2 * (12 / 5) - Real.log n) / 2 * Real.cos (169 / 2 * Real.log n)
        - Real.sin (169 / 2 * (2 * (12 / 5) - Real.log n)) / (2 * (169 / 2)))
      = ∑ n ∈ Finset.Icc 2 121, oddTerm n := rfl
  rw [hsum]
  have hS := oddPartial_121
  have hA := sinPacket_arch_total_le (a := 12 / 5) (ω := 169 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  have hf0 := PsiOmega.Num.normSq_sinPacket_bounds
  have hL := PsiOmega.Num.log_sqrt_z_bounds
  have hlog5 := PsiOmega.Num.log_bound_5
  have hpi := PsiOmega.Num.log_pi_bounds
  have h2aw := PsiOmega.Num.log_two_a_omega_bounds
  have hexp := PsiOmega.Num.exp_neg_three_a_le
  have hexp4 := PsiOmega.Num.one_sub_exp_neg_four_a_ge
  -- normalise the numerals appearing in `hA`
  have e1 : (2 * (169 / 2 : ℝ) * (12 / 5)) = 2028 / 5 := by norm_num
  have e2 : (2 * (12 / 5 : ℝ) * (169 / 2)) = 2028 / 5 := by norm_num
  rw [e1] at hA ⊢
  rw [e2] at hA
  set f0 : ℝ := 12 / 5 - Real.sin (2028 / 5) / (2 * (169 / 2)) with hf0def
  set L : ℝ := Real.log (Real.sqrt (9 / 16 + (169 / 2 : ℝ) ^ 2 / 4)) with hLdef
  set T : ℝ := 4 / 3 * Real.exp (-(3 * (12 / 5 : ℝ))) / (1 - Real.exp (-(4 * (12 / 5 : ℝ)))) with hTdef
  have hT : T ≤ 13 / 10000 := by
    rw [hTdef, div_le_iff₀ (by linarith)]
    nlinarith [hexp, hexp4, Real.exp_pos (-(3 * (12 / 5 : ℝ)))]
  have hTpos : 0 ≤ T := by rw [hTdef]; positivity
  have hA' : (Complex.digamma (3 / 4 : ℂ)).re * f0 + archEQ (3 / 4) (sinPacket (12 / 5) (169 / 2))
      ≤ f0 * (L + 3 / (169 / 2)) + f0 * T + 1 / (2 * (169 / 2))
        + (1 + Real.log (2028 / 5)) / (2 * (169 / 2)) := hA
  have hprod1 : f0 * (L + 3 / (169 / 2)) ≤ 2401944 / 10 ^ 6 * (37437620 / 10 ^ 7 + 3 / (169 / 2)) :=
    mul_le_mul hf0.2.le (by linarith [hL.2]) (by linarith [hL.1]) (by norm_num)
  have hprod2 : f0 * T ≤ 2401944 / 10 ^ 6 * (13 / 10000) :=
    mul_le_mul hf0.2.le hT hTpos (by norm_num)
  have hprod3 : (Real.log 5 - Real.log π) * f0
      ≤ (16094380 / 10 ^ 7 - 11447296 / 10 ^ 7) * (2401944 / 10 ^ 6) :=
    mul_le_mul (by linarith [hlog5.2, hpi.1]) hf0.2.le (by linarith [hf0.1]) (by norm_num)
  have hexp' : ((Complex.digamma (3 / 4 : ℂ)).re + Real.log 5 - Real.log π) * f0
      = (Complex.digamma (3 / 4 : ℂ)).re * f0 + (Real.log 5 - Real.log π) * f0 := by ring
  rw [hexp']
  linarith [hS, hA', hprod1, hprod2, hprod3, h2aw.2]

/-- **`Q_dh(sinPacket 12/5 169/2) < 0`**: Weil's form of `dh` is negative on an odd probe. -/
theorem QDHu_sinPacket_neg : QDHu (sinPacket (12 / 5) (169 / 2)) < 0 := by
  have := QDHu_sinPacket_le
  linarith

/-! ## The `dh` column of `rh_of_lamO_lower` -/

/-- **A negative normalised odd probe at every support `b ≥ 12/5`**: the normalised sine packet
(`QDHu` sees the probe, not the window). -/
theorem exists_oprobe_QDHu_neg {b : ℝ} (hb : 12 / 5 ≤ b) :
    ∃ o, OProbe b o ∧ normSq o = 1 ∧ QDHu o < 0 := by
  set g := sinPacket (12 / 5) (169 / 2) with hg
  have hpos : 0 < normSq g := by
    rw [hg, sinPacket_normSq (by norm_num) (by norm_num)]
    have := Real.sin_le_one (2 * (169 / 2 : ℝ) * (12 / 5))
    linarith
  set c := 1 / Real.sqrt (normSq g) with hc
  have hc0 : 0 < c := by rw [hc]; exact one_div_pos.2 (Real.sqrt_pos.2 hpos)
  have hc2 : c ^ 2 * normSq g = 1 := by
    rw [hc, div_pow, Real.sq_sqrt hpos.le]; field_simp
  refine ⟨fun t => c * g t, ((sinPacket_oprobe (a := 12 / 5) (ω := 169 / 2) (by norm_num)
    (by norm_num)).smul c).mono hb, ?_, ?_⟩
  · rw [normSq_smul]; exact hc2
  · rw [QDHu_smul]; exact mul_neg_of_pos_of_neg (pow_pos hc0 2) QDHu_sinPacket_neg

/-- **The `dh` column of `rh_of_lamO_lower`'s hypothesis, refuted**: for no `c > 0` (and any `δ`) is
Weil's form of `dh` eventually `≥ c·e^{(9+δ)b − 4πe^{2b}}` on every normalised odd probe at support `b`. -/
theorem not_odd_lower_dh {δ c : ℝ} (hc : 0 < c) :
    ¬ ∀ᶠ b in atTop, ∀ o, OProbe b o → normSq o = 1 →
      c * Real.exp ((9 + δ) * b - 4 * π * Real.exp (2 * b)) ≤ QDHu o := by
  intro h
  obtain ⟨b, hb, hb'⟩ := (h.and (eventually_ge_atTop (12 / 5 : ℝ))).exists
  obtain ⟨o, hp, hn, hneg⟩ := exists_oprobe_QDHu_neg hb'
  have h1 := hb o hp hn
  have h2 : 0 < c * Real.exp ((9 + δ) * b - 4 * π * Real.exp (2 * b)) := mul_pos hc (Real.exp_pos _)
  linarith

/-! ## The odd ground energy of `dh` -/

/-- **`Q_dh(o) ≥ −M_dh(a)‖o‖²`** on odd probes at support `a`. -/
theorem QDHu_ge_odd {a : ℝ} {o : ℝ → ℝ} (hp : OProbe a o) : -(MDH a * normSq o) ≤ QDHu o :=
  QDHu_ge_of_supp hp.supp hp.memL2

/-- **The odd `dh` ground energy** `λ_dh^odd(a) = inf {Q_dh(o) : o an odd probe at support a, ‖o‖ = 1}`. -/
def lamODH (a : ℝ) : ℝ := sInf {q | ∃ o, OProbe a o ∧ normSq o = 1 ∧ QDHu o = q}

theorem lamODH_bdd (a : ℝ) : BddBelow {q | ∃ o, OProbe a o ∧ normSq o = 1 ∧ QDHu o = q} :=
  ⟨-MDH a, by
    rintro q ⟨o, hp, hn, rfl⟩
    have := QDHu_ge_odd hp
    rwa [hn, mul_one] at this⟩

theorem lamODH_le {a : ℝ} {o : ℝ → ℝ} (hp : OProbe a o) (hn : normSq o = 1) : lamODH a ≤ QDHu o :=
  csInf_le (lamODH_bdd a) ⟨o, hp, hn, rfl⟩

/-- **`λ_dh^odd(b) < 0` for every `b ≥ 12/5`.** -/
theorem lamODH_neg {b : ℝ} (hb : 12 / 5 ≤ b) : lamODH b < 0 := by
  obtain ⟨o, hp, hn, hneg⟩ := exists_oprobe_QDHu_neg hb
  exact (lamODH_le hp hn).trans_lt hneg

/-- **`rh_of_lamO_lower`'s hypothesis with `λ_dh^odd` in place of `λ_odd`, refuted.** -/
theorem not_lamODH_lower {δ c : ℝ} (hc : 0 < c) :
    ¬ ∀ᶠ b in atTop, c * Real.exp ((9 + δ) * b - 4 * π * Real.exp (2 * b)) ≤ lamODH b := by
  intro h
  obtain ⟨b, hb, hb'⟩ := (h.and (eventually_ge_atTop (12 / 5 : ℝ))).exists
  have h1 := lamODH_neg hb'
  have h2 : 0 < c * Real.exp ((9 + δ) * b - 4 * π * Real.exp (2 * b)) := mul_pos hc (Real.exp_pos _)
  linarith

end PsiOmega

#print axioms PsiOmega.sinPacket_oprobe
#print axioms PsiOmega.sinPacket_autocorr
#print axioms PsiOmega.sinPacket_normSq
#print axioms PsiOmega.sinPacket_ghatC
#print axioms PsiOmega.sinPacket_striptest
#print axioms PsiOmega.QDHu_sinPacket_eq
#print axioms PsiOmega.sinPacket_archEQ_le
#print axioms PsiOmega.sinPacket_arch_total_le
#print axioms PsiOmega.Num.normSq_sinPacket_bounds
#print axioms PsiOmega.QDHu_sinPacket_le
#print axioms PsiOmega.QDHu_sinPacket_neg
#print axioms PsiOmega.exists_oprobe_QDHu_neg
#print axioms PsiOmega.not_odd_lower_dh
#print axioms PsiOmega.lamODH_neg
#print axioms PsiOmega.not_lamODH_lower
