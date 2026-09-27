import Mathlib
import KaiserTail

/-! # Integration by parts on the tail (round 163, part 8)

`φ(v) = e^{v/2} Σ_{n≥1} H(n eᵛ)`, which is `E H (eᵛ)`. For `eᵃ = L ≥ 1`, `|Im t| ≤ ½`, `t ≠ 0`:

  `‖∫_a^∞ φ(v) e^{itv} dv‖ ≤ 6P(1 + D₀)/‖t‖`   and   `≤ 2P`,

with `P = (πη)^{−8}`, `D₀ = 6 + 2β² + 32πη` — polynomial in `L`.
-/

open Complex Filter Topology MeasureTheory Real Set

noncomputable section

namespace Kaiser

variable {L η α : ℝ}

/-- `φ(v) = e^{v/2} Σ H(n eᵛ)`. -/
def phi (L η α : ℝ) (v : ℝ) : ℂ := (Real.exp (v / 2) : ℂ) * Sf (Hr L η α) (Real.exp v)

/-- `φ′`. -/
def phid (L η α : ℝ) (v : ℝ) : ℂ :=
  (Real.exp (v / 2) : ℂ) * ((1 / 2 : ℂ) * Sf (Hr L η α) (Real.exp v)
    + (Real.exp v : ℂ) * SHd L η α (Real.exp v))

theorem phi_eq_E (v : ℝ) : phi L η α v = E (Hr L η α) (Real.exp v) := by
  unfold phi E Sf
  congr 2
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf

theorem hasDerivAt_phi (hp : Par L η) (v : ℝ) : HasDerivAt (phi L η α) (phid L η α v) v := by
  have h1 : HasDerivAt (fun v : ℝ => ((Real.exp (v / 2) : ℝ) : ℂ)) ((Real.exp (v / 2) * (1 / 2) : ℝ)) v := by
    have := ((Real.hasDerivAt_exp (v / 2)).comp v ((hasDerivAt_id v).div_const 2))
    simpa using this.ofReal_comp
  have h2 : HasDerivAt (fun v : ℝ => Sf (Hr L η α) (Real.exp v))
      (Real.exp v • SHd L η α (Real.exp v)) v :=
    (hasDerivAt_SH hp (Real.exp_pos v) (α := α)).scomp v (Real.hasDerivAt_exp v)
  have := h1.mul h2
  unfold phi phid
  convert this using 1
  rw [Complex.real_smul]; push_cast; ring

theorem continuous_phi (hp : Par L η) : Continuous (phi L η α) :=
  continuous_iff_continuousAt.2 fun v => (hasDerivAt_phi hp v).continuousAt

theorem continuousOn_phid (hp : Par L η) : ContinuousOn (phid L η α) univ := by
  have hS : Continuous fun v : ℝ => Sf (Hr L η α) (Real.exp v) :=
    continuous_iff_continuousAt.2 fun v =>
      ((hasDerivAt_SH hp (Real.exp_pos v) (α := α)).continuousAt).comp Real.continuous_exp.continuousAt
  have hD : Continuous fun v : ℝ => SHd L η α (Real.exp v) :=
    (continuousOn_SHd hp (α := α)).comp_continuous Real.continuous_exp fun v => Real.exp_pos v
  unfold phid
  exact (by fun_prop : Continuous _).continuousOn

theorem norm_phi_tail (ht : Tail L η α) {v : ℝ} (hv : L ≤ Real.exp v) :
    ‖phi L η α v‖ ≤ 4 * kP η * Real.exp (-(7 / 2) * v) := by
  unfold phi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := norm_SH_tail ht hv
  have e4 : (Real.exp v)⁻¹ ^ 4 = Real.exp (-4 * v) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; push_cast; ring_nf
  have e : Real.exp (v / 2) * (4 * kP η * (Real.exp v)⁻¹ ^ 4) = 4 * kP η * Real.exp (-(7 / 2) * v) := by
    rw [e4, mul_left_comm, ← Real.exp_add]; congr 2; ring
  calc Real.exp (v / 2) * ‖Sf (Hr L η α) (Real.exp v)‖ ≤ Real.exp (v / 2) * (4 * kP η * (Real.exp v)⁻¹ ^ 4) := by
        gcongr
    _ = _ := e

theorem norm_phid_tail (ht : Tail L η α) {v : ℝ} (hv : L < Real.exp v) :
    ‖phid L η α v‖ ≤ 2 * kP η * (1 + kD0 L η) * Real.exp (-(3 / 2) * v) := by
  have hv0 : 0 ≤ v := by
    by_contra h; push Not at h
    have := Real.exp_le_one_iff.2 h.le; linarith [ht.one]
  have hP := (kP_pos ht.par.pos).le
  have hD := kD0_nonneg (L := L) ht.par.pos
  have h1 := norm_SH_tail ht hv.le (α := α)
  have h2 := norm_SHd_tail ht hv (α := α)
  unfold phid
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hsum : ‖(1 / 2 : ℂ) * Sf (Hr L η α) (Real.exp v) + (Real.exp v : ℂ) * SHd L η α (Real.exp v)‖
      ≤ 1 / 2 * (4 * kP η * (Real.exp v)⁻¹ ^ 4) + Real.exp v * (2 * kP η * kD0 L η * (Real.exp v)⁻¹ ^ 3) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]; gcongr
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; gcongr
  have e4 : (Real.exp v)⁻¹ ^ 4 = Real.exp (-4 * v) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; push_cast; ring_nf
  have e3 : (Real.exp v)⁻¹ ^ 3 = Real.exp (-3 * v) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; push_cast; ring_nf
  have ea : Real.exp (v / 2) * (Real.exp v)⁻¹ ^ 4 = Real.exp (-(7 / 2) * v) := by
    rw [e4, ← Real.exp_add]; congr 1; ring
  have eb : Real.exp (v / 2) * (Real.exp v * (Real.exp v)⁻¹ ^ 3) = Real.exp (-(3 / 2) * v) := by
    rw [e3, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hle : Real.exp (-(7 / 2) * v) ≤ Real.exp (-(3 / 2) * v) := Real.exp_le_exp.2 (by nlinarith)
  calc Real.exp (v / 2) * ‖(1 / 2 : ℂ) * Sf (Hr L η α) (Real.exp v) + (Real.exp v : ℂ) * SHd L η α (Real.exp v)‖
      ≤ Real.exp (v / 2) * (1 / 2 * (4 * kP η * (Real.exp v)⁻¹ ^ 4)
          + Real.exp v * (2 * kP η * kD0 L η * (Real.exp v)⁻¹ ^ 3)) := by gcongr
    _ = 2 * kP η * (Real.exp (v / 2) * (Real.exp v)⁻¹ ^ 4)
          + 2 * kP η * kD0 L η * (Real.exp (v / 2) * (Real.exp v * (Real.exp v)⁻¹ ^ 3)) := by ring
    _ = 2 * kP η * Real.exp (-(7 / 2) * v) + 2 * kP η * kD0 L η * Real.exp (-(3 / 2) * v) := by rw [ea, eb]
    _ ≤ 2 * kP η * Real.exp (-(3 / 2) * v) + 2 * kP η * kD0 L η * Real.exp (-(3 / 2) * v) := by gcongr
    _ = 2 * kP η * (1 + kD0 L η) * Real.exp (-(3 / 2) * v) := by ring


theorem norm_cexp_It {t : ℂ} (hti : |t.im| ≤ 1 / 2) {v : ℝ} (hv : 0 ≤ v) :
    ‖Complex.exp (I * t * v)‖ ≤ Real.exp (v / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (I * t * (v : ℂ)).re = -(t.im * v) := by simp [mul_re, mul_im]
  rw [this]
  have := abs_le.1 hti
  nlinarith

/-- **Trivial tail bound.** -/
theorem tail_le0 (ht : Tail L η α) {a : ℝ} (hLa : Real.exp a = L) {t : ℂ} (hti : |t.im| ≤ 1 / 2) :
    ‖∫ v in Ioi a, phi L η α v * Complex.exp (I * t * v)‖ ≤ 2 * kP η := by
  have ha0 : 0 ≤ a := by rw [← Real.exp_le_exp, Real.exp_zero, hLa]; exact ht.one
  have hP := (kP_pos ht.par.pos).le
  have hb : ∀ v ∈ Ioi a, ‖phi L η α v * Complex.exp (I * t * v)‖ ≤ 4 * kP η * Real.exp (-3 * v) := by
    intro v hv
    have hv' : a < v := hv
    have hL : L ≤ Real.exp v := hLa ▸ (Real.exp_le_exp.2 hv'.le)
    rw [norm_mul]
    calc ‖phi L η α v‖ * ‖Complex.exp (I * t * v)‖ ≤ 4 * kP η * Real.exp (-(7 / 2) * v) * Real.exp (v / 2) := by
          gcongr
          · exact norm_phi_tail ht hL
          · exact norm_cexp_It hti (by linarith)
      _ = 4 * kP η * Real.exp (-3 * v) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hint : IntegrableOn (fun v : ℝ => 4 * kP η * Real.exp (-3 * v)) (Ioi a) :=
    (integrableOn_exp_mul_Ioi (by norm_num) a).const_mul _
  calc ‖∫ v in Ioi a, phi L η α v * Complex.exp (I * t * v)‖
      ≤ ∫ v in Ioi a, 4 * kP η * Real.exp (-3 * v) := norm_integral_le_of_norm_le hint
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb))
    _ = 4 * kP η * (Real.exp (-3 * a) / 3) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num)]; ring
    _ ≤ 2 * kP η := by
        have : Real.exp (-3 * a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
        nlinarith

/-- **Integration by parts on the tail**: `‖∫_a^∞ φ e^{itv}‖ ≤ 6P(1 + D₀)/‖t‖`. -/
theorem tail_ibp (ht : Tail L η α) {a : ℝ} (hLa : Real.exp a = L) {t : ℂ} (hti : |t.im| ≤ 1 / 2)
    (ht0 : t ≠ 0) :
    ‖∫ v in Ioi a, phi L η α v * Complex.exp (I * t * v)‖ ≤ 6 * kP η * (1 + kD0 L η) / ‖t‖ := by
  have hp := ht.par
  have ha0 : 0 ≤ a := by rw [← Real.exp_le_exp, Real.exp_zero, hLa]; exact ht.one
  have hP := (kP_pos hp.pos).le
  have hD := kD0_nonneg (L := L) hp.pos
  have hIt : I * t ≠ 0 := mul_ne_zero I_ne_zero ht0
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht0
  have hItn : ‖I * t‖ = ‖t‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  set w : ℝ → ℂ := fun v => Complex.exp (I * t * v) / (I * t)
  have hw : ∀ v : ℝ, HasDerivAt w (Complex.exp (I * t * v)) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => I * t * (v : ℂ)) (I * t) v := by
      simpa using ((hasDerivAt_id v).ofReal_comp).const_mul (I * t)
    have := (h1.cexp).div_const (I * t)
    convert this using 1; field_simp
  have hwn : ∀ v : ℝ, 0 ≤ v → ‖w v‖ ≤ Real.exp (v / 2) / ‖t‖ := by
    intro v hv
    simp only [w, norm_div, hItn]
    gcongr; exact norm_cexp_It hti hv
  -- bounds on `Ioi a`
  have hL : ∀ v ∈ Ioi a, L < Real.exp v := fun v hv => hLa ▸ Real.exp_lt_exp.2 hv
  have hb1 : ∀ v ∈ Ioi a, ‖phi L η α v * Complex.exp (I * t * v)‖ ≤ 4 * kP η * Real.exp (-3 * v) := by
    intro v hv
    have hv' : a < v := hv
    rw [norm_mul]
    calc ‖phi L η α v‖ * ‖Complex.exp (I * t * v)‖ ≤ 4 * kP η * Real.exp (-(7 / 2) * v) * Real.exp (v / 2) := by
          gcongr
          · exact norm_phi_tail ht (hL v hv).le
          · exact norm_cexp_It hti (by linarith)
      _ = 4 * kP η * Real.exp (-3 * v) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hb2 : ∀ v ∈ Ioi a, ‖phid L η α v * w v‖ ≤ 2 * kP η * (1 + kD0 L η) / ‖t‖ * Real.exp (-v) := by
    intro v hv
    have hv' : a < v := hv
    rw [norm_mul]
    calc ‖phid L η α v‖ * ‖w v‖ ≤ 2 * kP η * (1 + kD0 L η) * Real.exp (-(3 / 2) * v) * (Real.exp (v / 2) / ‖t‖) := by
          gcongr
          · exact norm_phid_tail ht (hL v hv)
          · exact hwn v (by linarith)
      _ = 2 * kP η * (1 + kD0 L η) / ‖t‖ * (Real.exp (-(3 / 2) * v) * Real.exp (v / 2)) := by ring
      _ = 2 * kP η * (1 + kD0 L η) / ‖t‖ * Real.exp (-v) := by rw [← Real.exp_add]; congr 2; ring
  -- measurability
  have hcw : Continuous w := by simp only [w]; fun_prop
  have hphi := continuous_phi hp (α := α)
  have hphid : ContinuousOn (phid L η α) (Ioi a) := (continuousOn_phid hp).mono (subset_univ _)
  have hI1 : IntegrableOn (fun v : ℝ => phi L η α v * Complex.exp (I * t * v)) (Ioi a) := by
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0) a).const_mul (4 * kP η))
      ((hphi.mul (by fun_prop)).aestronglyMeasurable.restrict)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb1))
  have hI2 : IntegrableOn (fun v : ℝ => phid L η α v * w v) (Ioi a) := by
    refine Integrable.mono' ((integrableOn_exp_neg_Ioi a).const_mul _)
      ((hphid.mul hcw.continuousOn).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb2))
  have h_zero : Tendsto (phi L η α * w) (𝓝[>] a) (𝓝 (phi L η α a * w a)) :=
    ((hphi.mul hcw).tendsto a).mono_left nhdsWithin_le_nhds
  have hexp3 : Tendsto (fun v : ℝ => 4 * kP η / ‖t‖ * Real.exp (-3 * v)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-3 : ℝ) < 0))
    simpa using this.const_mul (4 * kP η / ‖t‖)
  have h_infty : Tendsto (phi L η α * w) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hexp3
    filter_upwards [eventually_gt_atTop a] with v hv
    simp only [Pi.mul_apply, norm_mul]
    calc ‖phi L η α v‖ * ‖w v‖ ≤ 4 * kP η * Real.exp (-(7 / 2) * v) * (Real.exp (v / 2) / ‖t‖) := by
          gcongr
          · exact norm_phi_tail ht (hL v hv).le
          · exact hwn v (by linarith)
      _ = 4 * kP η / ‖t‖ * (Real.exp (-(7 / 2) * v) * Real.exp (v / 2)) := by ring
      _ = 4 * kP η / ‖t‖ * Real.exp (-3 * v) := by rw [← Real.exp_add]; congr 2; ring
  have hIBP := integral_Ioi_mul_deriv_eq_deriv_mul (u := phi L η α) (u' := phid L η α) (v := w)
    (v' := fun v : ℝ => Complex.exp (I * t * v)) (a := a) (fun x _ => hasDerivAt_phi hp x)
    (fun x _ => hw x) hI1 hI2 h_zero h_infty
  rw [hIBP, zero_sub]
  have hphia : ‖phi L η α a‖ ≤ 4 * kP η * Real.exp (-(7 / 2) * a) := norm_phi_tail ht (le_of_eq hLa.symm)
  have hwa := hwn a ha0
  have hint2 : ‖∫ v in Ioi a, phid L η α v * w v‖ ≤ 2 * kP η * (1 + kD0 L η) / ‖t‖ * Real.exp (-a) := by
    calc ‖∫ v in Ioi a, phid L η α v * w v‖
        ≤ ∫ v in Ioi a, 2 * kP η * (1 + kD0 L η) / ‖t‖ * Real.exp (-v) :=
          norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi a).const_mul _)
            ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb2))
      _ = _ := by rw [integral_const_mul, integral_exp_neg_Ioi]
  have hea : Real.exp (-(7 / 2) * a) * Real.exp (a / 2) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]; linarith
  have hea2 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  calc ‖-(phi L η α a * w a) - ∫ v in Ioi a, phid L η α v * w v‖
      ≤ ‖phi L η α a‖ * ‖w a‖ + ‖∫ v in Ioi a, phid L η α v * w v‖ := by
        rw [sub_eq_add_neg, ← neg_add]; rw [norm_neg]
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ 4 * kP η * Real.exp (-(7 / 2) * a) * (Real.exp (a / 2) / ‖t‖)
          + 2 * kP η * (1 + kD0 L η) / ‖t‖ * Real.exp (-a) := by gcongr
    _ = (4 * kP η * (Real.exp (-(7 / 2) * a) * Real.exp (a / 2)) + 2 * kP η * (1 + kD0 L η) * Real.exp (-a)) / ‖t‖ := by
        ring
    _ ≤ (4 * kP η * 1 + 2 * kP η * (1 + kD0 L η) * 1) / ‖t‖ := by gcongr
    _ ≤ 6 * kP η * (1 + kD0 L η) / ‖t‖ := by
        gcongr; nlinarith

end Kaiser

#print axioms Kaiser.tail_le0
#print axioms Kaiser.tail_ibp

#print axioms Kaiser.hasDerivAt_phi
#print axioms Kaiser.norm_phi_tail
#print axioms Kaiser.norm_phid_tail
