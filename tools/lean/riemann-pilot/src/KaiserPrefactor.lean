import Mathlib
import KaiserBulk
import KaiserPlanch

/-! # The prefactor: the zero side at the density level (round 164, part 4)

The tail `T(t) = ∫_a^∞ φ(v) e^{itv} dv` is `e^{ita} F(t)` with `F(t) = ∫_0^∞ φ(a + w) e^{itw} dw`.
Poisson (`Fl_sq_le`) and the zero weight (`tsum_Vz_le`) give
`Σ_ρ ‖F(t_ρ)‖² ≤ ∫ W(x) ‖F(x − i)‖² dx` with `W(x) = (5 + kLam + ½log(|x| + 2))/π`, and the regularised
Plancherel inequality with the tail integration by parts bound this by `C(1 + a) L⁹`.
-/

open Complex Filter Topology MeasureTheory Real Set

noncomputable section

namespace Kaiser

open Pilot1ca Pilot1bt

variable {L η α : ℝ}

theorem norm_cexp_It_line {t : ℂ} (hti : -1 ≤ t.im) {v : ℝ} (hv : 0 ≤ v) :
    ‖Complex.exp (I * t * v)‖ ≤ Real.exp v := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (I * t * (v : ℂ)).re = -(t.im * v) := by simp [mul_re, mul_im]
  rw [this]; nlinarith

/-- **Integration by parts on the tail, down to the line `Im t = −1`.** -/
theorem tail_ibp_line (ht : Tail L η α) {a : ℝ} (hLa : Real.exp a = L) {t : ℂ} (hti : -1 ≤ t.im)
    (ht0 : t ≠ 0) :
    ‖∫ v in Ioi a, phi L η α v * Complex.exp (I * t * v)‖ ≤ 8 * kP η * (1 + kD0 L η) / ‖t‖ := by
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
  have hwn : ∀ v : ℝ, 0 ≤ v → ‖w v‖ ≤ Real.exp v / ‖t‖ := by
    intro v hv
    simp only [w, norm_div, hItn]
    gcongr; exact norm_cexp_It_line hti hv
  have hL : ∀ v ∈ Ioi a, L < Real.exp v := fun v hv => hLa ▸ Real.exp_lt_exp.2 hv
  have hb1 : ∀ v ∈ Ioi a, ‖phi L η α v * Complex.exp (I * t * v)‖ ≤ 4 * kP η * Real.exp (-(5 / 2) * v) := by
    intro v hv
    have hv' : a < v := hv
    rw [norm_mul]
    calc ‖phi L η α v‖ * ‖Complex.exp (I * t * v)‖ ≤ 4 * kP η * Real.exp (-(7 / 2) * v) * Real.exp v := by
          gcongr
          · exact norm_phi_tail ht (hL v hv).le
          · exact norm_cexp_It_line hti (by linarith)
      _ = 4 * kP η * Real.exp (-(5 / 2) * v) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hb2 : ∀ v ∈ Ioi a, ‖phid L η α v * w v‖ ≤ 2 * kP η * (1 + kD0 L η) / ‖t‖ * Real.exp (-(1 / 2) * v) := by
    intro v hv
    have hv' : a < v := hv
    rw [norm_mul]
    calc ‖phid L η α v‖ * ‖w v‖ ≤ 2 * kP η * (1 + kD0 L η) * Real.exp (-(3 / 2) * v) * (Real.exp v / ‖t‖) := by
          gcongr
          · exact norm_phid_tail ht (hL v hv)
          · exact hwn v (by linarith)
      _ = 2 * kP η * (1 + kD0 L η) / ‖t‖ * (Real.exp (-(3 / 2) * v) * Real.exp v) := by ring
      _ = 2 * kP η * (1 + kD0 L η) / ‖t‖ * Real.exp (-(1 / 2) * v) := by rw [← Real.exp_add]; congr 2; ring
  have hcw : Continuous w := by simp only [w]; fun_prop
  have hphi := continuous_phi hp (α := α)
  have hphid : ContinuousOn (phid L η α) (Ioi a) := (continuousOn_phid hp).mono (subset_univ _)
  have hI1 : IntegrableOn (fun v : ℝ => phi L η α v * Complex.exp (I * t * v)) (Ioi a) := by
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by norm_num : (-(5 / 2) : ℝ) < 0) a).const_mul (4 * kP η))
      ((hphi.mul (by fun_prop)).aestronglyMeasurable.restrict)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb1))
  have hI2 : IntegrableOn (fun v : ℝ => phid L η α v * w v) (Ioi a) := by
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 2) : ℝ) < 0) a).const_mul _)
      ((hphid.mul hcw.continuousOn).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb2))
  have h_zero : Tendsto (phi L η α * w) (𝓝[>] a) (𝓝 (phi L η α a * w a)) :=
    ((hphi.mul hcw).tendsto a).mono_left nhdsWithin_le_nhds
  have hexp : Tendsto (fun v : ℝ => 4 * kP η / ‖t‖ * Real.exp (-(5 / 2) * v)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-(5 / 2) : ℝ) < 0))
    simpa using this.const_mul (4 * kP η / ‖t‖)
  have h_infty : Tendsto (phi L η α * w) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hexp
    filter_upwards [eventually_gt_atTop a] with v hv
    simp only [Pi.mul_apply, norm_mul]
    calc ‖phi L η α v‖ * ‖w v‖ ≤ 4 * kP η * Real.exp (-(7 / 2) * v) * (Real.exp v / ‖t‖) := by
          gcongr
          · exact norm_phi_tail ht (hL v hv).le
          · exact hwn v (by linarith)
      _ = 4 * kP η / ‖t‖ * (Real.exp (-(7 / 2) * v) * Real.exp v) := by ring
      _ = 4 * kP η / ‖t‖ * Real.exp (-(5 / 2) * v) := by rw [← Real.exp_add]; congr 2; ring
  have hIBP := integral_Ioi_mul_deriv_eq_deriv_mul (u := phi L η α) (u' := phid L η α) (v := w)
    (v' := fun v : ℝ => Complex.exp (I * t * v)) (a := a) (fun x _ => hasDerivAt_phi hp x)
    (fun x _ => hw x) hI1 hI2 h_zero h_infty
  rw [hIBP, zero_sub]
  have hphia : ‖phi L η α a‖ ≤ 4 * kP η * Real.exp (-(7 / 2) * a) := norm_phi_tail ht (le_of_eq hLa.symm)
  have hwa := hwn a ha0
  have hint2 : ‖∫ v in Ioi a, phid L η α v * w v‖ ≤ 2 * kP η * (1 + kD0 L η) / ‖t‖ * (2 * Real.exp (-(1 / 2) * a)) := by
    calc ‖∫ v in Ioi a, phid L η α v * w v‖
        ≤ ∫ v in Ioi a, 2 * kP η * (1 + kD0 L η) / ‖t‖ * Real.exp (-(1 / 2) * v) :=
          norm_integral_le_of_norm_le ((integrableOn_exp_mul_Ioi (by norm_num) a).const_mul _)
            ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb2))
      _ = _ := by rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num)]; ring
  have hea : Real.exp (-(7 / 2) * a) * Real.exp a ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]; linarith
  have hea2 : Real.exp (-(1 / 2) * a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  calc ‖-(phi L η α a * w a) - ∫ v in Ioi a, phid L η α v * w v‖
      ≤ ‖phi L η α a‖ * ‖w a‖ + ‖∫ v in Ioi a, phid L η α v * w v‖ := by
        rw [sub_eq_add_neg, ← neg_add]; rw [norm_neg]
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ 4 * kP η * Real.exp (-(7 / 2) * a) * (Real.exp a / ‖t‖)
          + 2 * kP η * (1 + kD0 L η) / ‖t‖ * (2 * Real.exp (-(1 / 2) * a)) := by gcongr
    _ = (4 * kP η * (Real.exp (-(7 / 2) * a) * Real.exp a)
          + 4 * kP η * (1 + kD0 L η) * Real.exp (-(1 / 2) * a)) / ‖t‖ := by ring
    _ ≤ (4 * kP η * 1 + 4 * kP η * (1 + kD0 L η) * 1) / ‖t‖ := by gcongr
    _ ≤ 8 * kP η * (1 + kD0 L η) / ‖t‖ := by
        gcongr; nlinarith

/-! ## The shifted tail `F` and its transform -/

/-- `ψ(w) = φ(a + w)`. -/
def psiK (L η α a : ℝ) (w : ℝ) : ℂ := phi L η α (a + w)

/-- `Ψ(w) = 1_{w>0} ψ(w) e^w`, so that `F(x − i) = ∫ Ψ(w) e^{ixw} dw`. -/
def PsiK (L η α a : ℝ) : ℝ → ℂ := (Ioi 0).indicator fun w => psiK L η α a w * (Real.exp w : ℂ)

theorem Tt_eq (a : ℝ) (t : ℂ) :
    Tt L η α a t = Complex.exp (I * t * a) * Fl (psiK L η α a) t := by
  unfold Tt Fl psiK
  rw [← integral_const_mul, ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  rw [← integral_add_left_eq_self _ a]
  congr 1; funext w
  by_cases hw : 0 < w
  · have h1 : a + w ∈ Ioi a := by simp; linarith
    have h2 : w ∈ Ioi (0 : ℝ) := hw
    rw [indicator_of_mem h1, indicator_of_mem h2]
    rw [show I * t * ((a + w : ℝ) : ℂ) = I * t * a + I * t * w by push_cast; ring, Complex.exp_add]
    ring
  · have h1 : a + w ∉ Ioi a := by simp; linarith
    have h2 : w ∉ Ioi (0 : ℝ) := by simpa using hw
    rw [indicator_of_notMem h1, indicator_of_notMem h2]

theorem Fl_line_eq (a x : ℝ) : Fl (psiK L η α a) ((x : ℂ) - I) = FT (PsiK L η α a) x := by
  unfold Fl FT PsiK
  rw [← integral_indicator measurableSet_Ioi]
  congr 1; funext w
  by_cases hw : w ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hw, indicator_of_mem hw, Complex.ofReal_exp, mul_assoc, mul_assoc, ← Complex.exp_add]
    congr 2; ring_nf; rw [I_sq]; ring
  · rw [indicator_of_notMem hw, indicator_of_notMem hw, zero_mul]

theorem norm_psiK_le (ht : Tail L η α) {a : ℝ} (hLa : Real.exp a = L) {w : ℝ} (hw : 0 < w) :
    ‖psiK L η α a w‖ ≤ 4 * kP η * Real.exp (-(7 / 2) * a) * Real.exp (-(7 / 2) * w) := by
  have hL : L ≤ Real.exp (a + w) := hLa ▸ Real.exp_le_exp.2 (by linarith)
  refine (norm_phi_tail ht hL).trans (le_of_eq ?_)
  rw [show -(7 / 2) * (a + w) = -(7 / 2) * a + -(7 / 2) * w by ring, Real.exp_add]; ring

theorem norm_PsiK_le (ht : Tail L η α) {a : ℝ} (hLa : Real.exp a = L) (w : ℝ) :
    ‖PsiK L η α a w‖ ≤ (Ioi 0).indicator (fun w => 4 * kP η * Real.exp (-(7 / 2) * a) * Real.exp (-(5 / 2) * w)) w := by
  unfold PsiK
  by_cases hw : w ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hw, indicator_of_mem hw, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc ‖psiK L η α a w‖ * Real.exp w ≤ 4 * kP η * Real.exp (-(7 / 2) * a) * Real.exp (-(7 / 2) * w) * Real.exp w :=
          mul_le_mul_of_nonneg_right (norm_psiK_le ht hLa hw) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  · rw [indicator_of_notMem hw, indicator_of_notMem hw, norm_zero]

theorem measurable_PsiK (hp : Par L η) (a : ℝ) : AEStronglyMeasurable (PsiK L η α a) volume := by
  unfold PsiK psiK
  exact (((continuous_phi hp).comp (continuous_const.add continuous_id)).mul (by fun_prop)
    |>.aestronglyMeasurable).indicator measurableSet_Ioi

theorem integrable_PsiK (ht : Tail L η α) {a : ℝ} (hLa : Real.exp a = L) : Integrable (PsiK L η α a) := by
  have hi : Integrable ((Ioi 0).indicator
      (fun w : ℝ => 4 * kP η * Real.exp (-(7 / 2) * a) * Real.exp (-(5 / 2) * w))) :=
    IntegrableOn.integrable_indicator ((integrableOn_exp_mul_Ioi (by norm_num : (-(5 / 2) : ℝ) < 0) 0).const_mul
      (4 * kP η * Real.exp (-(7 / 2) * a))) measurableSet_Ioi
  exact hi.mono' (measurable_PsiK ht.par a) (ae_of_all _ (norm_PsiK_le ht hLa))

/-- **`∫ ‖Ψ‖² ≤ (16/5) P² e^{−7a}`.** -/
theorem integral_PsiK_sq (ht : Tail L η α) {a : ℝ} (hLa : Real.exp a = L) :
    ∫ w, ‖PsiK L η α a w‖ ^ 2 ≤ 16 / 5 * kP η ^ 2 * Real.exp (-(7 * a)) := by
  set c := 4 * kP η * Real.exp (-(7 / 2) * a)
  have hc : 0 ≤ c := by have := (kP_pos ht.par.pos).le; positivity
  have hb : ∀ w, ‖PsiK L η α a w‖ ^ 2 ≤ (Ioi 0).indicator (fun w => c ^ 2 * Real.exp (-5 * w)) w := by
    intro w
    have h := norm_PsiK_le ht hLa w
    by_cases hw : w ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hw] at h ⊢
      calc ‖PsiK L η α a w‖ ^ 2 ≤ (c * Real.exp (-(5 / 2) * w)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = c ^ 2 * Real.exp (-5 * w) := by rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    · rw [indicator_of_notMem hw] at h ⊢
      have := norm_nonneg (PsiK L η α a w); nlinarith
  have hi : Integrable ((Ioi 0).indicator fun w : ℝ => c ^ 2 * Real.exp (-5 * w)) :=
    IntegrableOn.integrable_indicator ((integrableOn_exp_mul_Ioi (by norm_num : (-5 : ℝ) < 0) 0).const_mul _)
      measurableSet_Ioi
  have h0 : ∀ w, 0 ≤ ‖PsiK L η α a w‖ ^ 2 := fun w => by positivity
  calc ∫ w, ‖PsiK L η α a w‖ ^ 2 ≤ ∫ w, (Ioi 0).indicator (fun w => c ^ 2 * Real.exp (-5 * w)) w := by
        refine integral_mono_of_nonneg (ae_of_all _ h0) hi (ae_of_all _ hb)
    _ = c ^ 2 / 5 := by
        rw [integral_indicator measurableSet_Ioi, integral_const_mul, integral_exp_mul_Ioi (by norm_num)]
        simp; ring
    _ = _ := by
        simp only [c]; rw [mul_pow, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf

/-! ## The log-weighted integral -/

/-- The zero weight bound `W(x) = (5 + kLam + ½ log(|x| + 2))/π`. -/
def Wf (x : ℝ) : ℝ := (5 + kLam + Real.log (|x| + 2) / 2) / π

theorem kLam_nonneg : 0 ≤ kLam := tsum_nonneg fun _ => norm_nonneg _

theorem Wf_nonneg (x : ℝ) : 0 ≤ Wf x := by
  unfold Wf
  have := kLam_nonneg
  have : 0 ≤ Real.log (|x| + 2) := Real.log_nonneg (by linarith [abs_nonneg x])
  positivity

theorem Wf_mono {x M : ℝ} (hx : |x| ≤ M) : Wf x ≤ Wf |M| := by
  unfold Wf
  refine div_le_div_of_nonneg_right ?_ pi_pos.le
  have : Real.log (|x| + 2) ≤ Real.log (|M| + 2) :=
    Real.log_le_log (by positivity) (by linarith [le_abs_self M])
  rw [abs_abs]; linarith

/-- `ρ(x) = (1 + x²)^{−5/8}`, integrable. -/
def rho58 (x : ℝ) : ℝ := (1 + ‖x‖ ^ 2) ^ (-(5 / 4 : ℝ) / 2)

theorem integrable_rho58 : Integrable rho58 := by
  have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 5 / 4) (by simp; norm_num)
  exact this

theorem Wf_tail_le {x M : ℝ} (hM : 1 ≤ M) (hx : M ≤ |x|) :
    Wf x / x ^ 2 ≤ 2 * ((8 + kLam) / π) * (1 + M ^ 2) ^ (-(1 / 8 : ℝ)) * rho58 x := by
  have hx1 : 1 ≤ |x| := hM.trans hx
  have hx2 : 1 ≤ x ^ 2 := by rw [← sq_abs]; nlinarith
  set y := 1 + x ^ 2
  have hy : 1 ≤ y := by simp only [y]; nlinarith
  have hy0 : 0 < y := by linarith
  have hq := Real.one_le_rpow hy (by norm_num : (0 : ℝ) ≤ 1 / 4)
  -- `log(|x| + 2) ≤ 1 + 4 y^{1/4}`
  have hlog : Real.log (|x| + 2) ≤ 1 + 4 * y ^ (1 / 4 : ℝ) := by
    have h2y : |x| + 2 ≤ 2 * y := by simp only [y]; rw [← sq_abs]; nlinarith
    have h1 : Real.log (|x| + 2) ≤ Real.log 2 + Real.log y := by
      rw [← Real.log_mul (by norm_num) hy0.ne']
      exact Real.log_le_log (by linarith [abs_nonneg x]) h2y
    have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have h3 : Real.log y ≤ 4 * y ^ (1 / 4 : ℝ) := by
      have e : Real.log y = 4 * Real.log (y ^ (1 / 4 : ℝ)) := by
        rw [Real.log_rpow hy0]; ring
      rw [e]
      have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy0 (1 / 4 : ℝ))
      linarith
    linarith
  have hk := kLam_nonneg
  have hW : Wf x ≤ (8 + kLam) / π * y ^ (1 / 4 : ℝ) := by
    unfold Wf
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ pi_pos.le
    nlinarith
  have hinv : 1 / x ^ 2 ≤ 2 / y := by
    rw [div_le_div_iff₀ (by positivity) hy0]; simp only [y]; linarith
  have hrho : rho58 x = y ^ (-(5 / 8 : ℝ)) := by
    unfold rho58; rw [Real.norm_eq_abs, sq_abs]; congr 1; norm_num
  have hsplit : y ^ (1 / 4 : ℝ) * (2 / y) = 2 * (y ^ (-(1 / 8 : ℝ)) * y ^ (-(5 / 8 : ℝ))) := by
    have e1 : 2 / y = 2 * y ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; ring
    rw [e1, show y ^ (1 / 4 : ℝ) * (2 * y ^ (-1 : ℝ)) = 2 * (y ^ (1 / 4 : ℝ) * y ^ (-1 : ℝ)) by ring,
      ← Real.rpow_add hy0, ← Real.rpow_add hy0]
    norm_num
  have hmono : y ^ (-(1 / 8 : ℝ)) ≤ (1 + M ^ 2) ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by simp only [y]; rw [← sq_abs x]; nlinarith) (by norm_num)
  have hc : 0 ≤ (8 + kLam) / π := by positivity
  calc Wf x / x ^ 2 = Wf x * (1 / x ^ 2) := by ring
    _ ≤ (8 + kLam) / π * y ^ (1 / 4 : ℝ) * (2 / y) :=
        mul_le_mul hW hinv (by positivity) (by positivity)
    _ = (8 + kLam) / π * (2 * (y ^ (-(1 / 8 : ℝ)) * y ^ (-(5 / 8 : ℝ)))) := by rw [mul_assoc, hsplit]
    _ ≤ (8 + kLam) / π * (2 * ((1 + M ^ 2) ^ (-(1 / 8 : ℝ)) * y ^ (-(5 / 8 : ℝ)))) := by
        gcongr
    _ = _ := by rw [hrho]; ring

theorem continuous_FT {Ψ : ℝ → ℂ} (h1 : Integrable Ψ) : Continuous (FT Ψ) :=
  continuous_of_dominated (bound := fun w => ‖Ψ w‖)
    (fun x => h1.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop)))
    (fun x => ae_of_all _ fun w => by
      rw [norm_mul, Complex.norm_exp]
      have : (I * (x : ℂ) * (w : ℂ)).re = 0 := by simp
      rw [this, Real.exp_zero, mul_one])
    h1.norm (ae_of_all _ fun w => by fun_prop)

theorem norm_FT_le {Ψ : ℝ → ℂ} (x : ℝ) : ‖FT Ψ x‖ ≤ ∫ w, ‖Ψ w‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext w
  rw [norm_mul, Complex.norm_exp]
  have : (I * (x : ℂ) * (w : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero, mul_one]

/-- **The log-weighted `L²` bound** (and the integrability of `W‖F‖²`). -/
theorem weighted_FT_le {Ψ : ℝ → ℂ} (h1 : Integrable Ψ) (h2 : Integrable fun w => ‖Ψ w‖ ^ 2)
    {B M : ℝ} (hM : 1 ≤ M) (hB : ∀ x : ℝ, x ≠ 0 → ‖FT Ψ x‖ ≤ B / |x|) :
    Integrable (fun x => Wf x * ‖FT Ψ x‖ ^ 2) ∧
    ∫ x, Wf x * ‖FT Ψ x‖ ^ 2 ≤ Wf M * Real.exp 1 * (2 * π * ∫ w, ‖Ψ w‖ ^ 2)
      + 2 * ((8 + kLam) / π) * B ^ 2 * (1 + M ^ 2) ^ (-(1 / 8 : ℝ)) * ∫ x, rho58 x := by
  set b := 1 / M ^ 2
  have hb : 0 < b := by positivity
  set K2 := 2 * ((8 + kLam) / π) * B ^ 2 * (1 + M ^ 2) ^ (-(1 / 8 : ℝ))
  have hK2 : 0 ≤ K2 := by have := kLam_nonneg; positivity
  have hWM : Wf |M| = Wf M := by rw [abs_of_pos (by linarith)]
  have hpt : ∀ x : ℝ, Wf x * ‖FT Ψ x‖ ^ 2 ≤
      Wf M * Real.exp 1 * (‖FT Ψ x‖ ^ 2 * Real.exp (-(b * x ^ 2))) + K2 * rho58 x := by
    intro x
    have hr : 0 ≤ rho58 x := by unfold rho58; positivity
    have hF := sq_nonneg ‖FT Ψ x‖
    rcases le_or_gt |x| M with hx | hx
    · have hW := Wf_mono hx; rw [hWM] at hW
      have he : 1 ≤ Real.exp 1 * Real.exp (-(b * x ^ 2)) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        have : b * x ^ 2 ≤ 1 := by
          simp only [b]; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity), ← sq_abs x]
          nlinarith [abs_nonneg x]
        linarith
      have := Wf_nonneg x
      have := Wf_nonneg M
      calc Wf x * ‖FT Ψ x‖ ^ 2 ≤ Wf M * ‖FT Ψ x‖ ^ 2 := mul_le_mul_of_nonneg_right hW hF
        _ ≤ Wf M * (‖FT Ψ x‖ ^ 2 * (Real.exp 1 * Real.exp (-(b * x ^ 2)))) := by
            gcongr; nlinarith
        _ ≤ _ := by nlinarith [mul_nonneg hK2 hr]
    · have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
      have hxa : 0 < |x| := abs_pos.2 hx0
      have hFB : ‖FT Ψ x‖ ^ 2 ≤ B ^ 2 / x ^ 2 := by
        rw [← sq_abs x, ← div_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hB x hx0) 2
      have hWt := Wf_tail_le hM hx.le
      have hWx := Wf_nonneg x
      have h3 : Wf x * ‖FT Ψ x‖ ^ 2 ≤ K2 * rho58 x := by
        calc Wf x * ‖FT Ψ x‖ ^ 2 ≤ Wf x * (B ^ 2 / x ^ 2) := mul_le_mul_of_nonneg_left hFB hWx
          _ = B ^ 2 * (Wf x / x ^ 2) := by ring
          _ ≤ B ^ 2 * (2 * ((8 + kLam) / π) * (1 + M ^ 2) ^ (-(1 / 8 : ℝ)) * rho58 x) :=
              mul_le_mul_of_nonneg_left hWt (sq_nonneg B)
          _ = K2 * rho58 x := by simp only [K2]; ring
      have : 0 ≤ Wf M * Real.exp 1 * (‖FT Ψ x‖ ^ 2 * Real.exp (-(b * x ^ 2))) := by
        have := Wf_nonneg M; positivity
      linarith
  -- integrability
  have hc := continuous_FT h1
  have hG : Integrable fun x : ℝ => ‖FT Ψ x‖ ^ 2 * Real.exp (-(b * x ^ 2)) := by
    have hg0 : Integrable fun x : ℝ => Real.exp (-(b * x ^ 2)) := by
      simpa only [neg_mul] using integrable_exp_neg_mul_sq hb
    have hg := hg0.const_mul ((∫ w, ‖Ψ w‖) ^ 2)
    refine hg.mono' ((hc.norm.pow 2).mul (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_FT_le x) 2) (Real.exp_pos _).le
  have hR : Integrable fun x => Wf M * Real.exp 1 * (‖FT Ψ x‖ ^ 2 * Real.exp (-(b * x ^ 2))) + K2 * rho58 x :=
    (hG.const_mul _).add (integrable_rho58.const_mul _)
  have hWc : Continuous Wf := by
    unfold Wf
    exact (continuous_const.add ((Continuous.log (by fun_prop) fun x => by positivity).div_const _)).div_const _
  have hL : Integrable fun x => Wf x * ‖FT Ψ x‖ ^ 2 :=
    hR.mono' (hWc.mul (hc.norm.pow 2)).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (Wf_nonneg x) (sq_nonneg _))]; exact hpt x)
  refine ⟨hL, ?_⟩
  calc ∫ x, Wf x * ‖FT Ψ x‖ ^ 2
      ≤ ∫ x, (Wf M * Real.exp 1 * (‖FT Ψ x‖ ^ 2 * Real.exp (-(b * x ^ 2))) + K2 * rho58 x) :=
        integral_mono hL hR hpt
    _ = Wf M * Real.exp 1 * (∫ x, ‖FT Ψ x‖ ^ 2 * Real.exp (-(b * x ^ 2))) + K2 * ∫ x, rho58 x := by
        rw [integral_add (hG.const_mul _) (integrable_rho58.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ Wf M * Real.exp 1 * (2 * π * ∫ w, ‖Ψ w‖ ^ 2) + K2 * ∫ x, rho58 x := by
        have := Wf_nonneg M
        gcongr
        exact FT_gauss_le h1 h2 hb

/-! ## The zero side, zero by zero -/

section Zero

variable (ht : Tail L η α) {a : ℝ} (hLa : Real.exp a = L)
include ht hLa

omit hLa in
theorem psiK_meas : AEStronglyMeasurable (psiK L η α a) (volume.restrict (Ioi 0)) :=
  ((continuous_phi ht.par).comp (continuous_const.add continuous_id)).aestronglyMeasurable

theorem psiK_int : IntegrableOn (fun w => ‖psiK L η α a w‖ * Real.exp w) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by norm_num : (-(5 / 2) : ℝ) < 0) 0).const_mul
    (4 * kP η * Real.exp (-(7 / 2) * a))) ((psiK_meas ht (a := a)).norm.mul (by fun_prop : Continuous
      fun w : ℝ => Real.exp w).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖psiK L η α a w‖ * Real.exp w ≤ 4 * kP η * Real.exp (-(7 / 2) * a) * Real.exp (-(7 / 2) * w) * Real.exp w :=
        mul_le_mul_of_nonneg_right (norm_psiK_le ht hLa hw) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

omit ht hLa in
theorem norm_Tt_eq (t : ℂ) :
    ‖Tt L η α a t‖ = Real.exp (-(a * t.im)) * ‖Fl (psiK L η α a) t‖ := by
  rw [Tt_eq, norm_mul, Complex.norm_exp]
  congr 2; simp [mul_re, mul_im]; ring

theorem integrable_pk_FT {y : ℝ} (hy : 0 < y) (c : ℝ) :
    Integrable fun x => pk y (x - c) * ‖FT (PsiK L η α a) x‖ ^ 2 := by
  have hc := continuous_FT (integrable_PsiK ht hLa)
  set B := ∫ w, ‖PsiK L η α a w‖
  refine (((integrable_pk hy).comp_sub_right c).mul_const (B ^ 2)).mono'
    ((((continuous_pk hy).comp (continuous_id.sub continuous_const)).mul (hc.norm.pow 2)).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (pk_nonneg hy.le _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_FT_le x) 2) (pk_nonneg hy.le _)

omit ht hLa in
theorem Vz_neg (τ : ℂ) (x : ℝ) : Vz (-τ) x = Vz τ x := by
  unfold Vz; simp only [neg_im, neg_re]
  rw [add_comm]; congr 1 <;> congr 1 <;> ring

/-- **One zero**: `‖ĝ(τ)‖² ≤ 2e^{2a|Im τ|} ∫ V_τ(x) ‖F(x − i)‖² dx`. -/
theorem ghat_sq_le_pair (hint : ∫ x, Hr L η α x = 0) (ha : 0 < a) {τ : ℂ} (hτ : |τ.im| < 1 / 2)
    (hX : Xi τ = 0) :
    ‖ghatC (gK L η α a) a τ‖ ^ 2 ≤
      2 * Real.exp (2 * a * |τ.im|) * ∫ x, Vz τ x * ‖FT (PsiK L η α a) x‖ ^ 2 := by
  have hp := ht.par
  have hs := abs_lt.1 hτ
  set σ := τ.re; set s := τ.im
  have hτe : τ = σ + s * I := (Complex.re_add_im τ).symm
  have hτn : -τ = ((-σ : ℝ) : ℂ) + ((-s : ℝ) : ℂ) * I := by rw [hτe]; push_cast; ring
  have hm := psiK_meas ht (α := α) (a := a)
  have hi := psiK_int ht hLa (α := α) (a := a)
  -- the two Poisson majorants
  have h1 := Fl_sq_le hm hi (σ := σ) (s := s) (by linarith)
  have h2 := Fl_sq_le hm hi (σ := -σ) (s := -s) (by linarith)
  rw [← hτe] at h1; rw [← hτn] at h2
  simp_rw [Fl_line_eq] at h1 h2
  have e2 : ∀ x : ℝ, pk (1 + -s) (x - -σ) = pk (1 - s) (x + σ) := fun x => by rw [sub_neg_eq_add, ← sub_eq_add_neg]
  simp_rw [e2] at h2
  have hsum : ‖Fl (psiK L η α a) τ‖ ^ 2 + ‖Fl (psiK L η α a) (-τ)‖ ^ 2 ≤
      ∫ x, Vz τ x * ‖FT (PsiK L η α a) x‖ ^ 2 := by
    have i1 := integrable_pk_FT ht hLa (by linarith : 0 < 1 + s) σ
    have i2 := integrable_pk_FT ht hLa (by linarith : 0 < 1 - s) (-σ)
    simp only [sub_neg_eq_add] at i2
    calc _ ≤ (∫ x, pk (1 + s) (x - σ) * ‖FT (PsiK L η α a) x‖ ^ 2)
          + ∫ x, pk (1 - s) (x + σ) * ‖FT (PsiK L η α a) x‖ ^ 2 := add_le_add h1 h2
      _ = _ := by
          rw [← integral_add i1 i2]; congr 1; funext x; simp only [Vz]; ring
  -- `ĝ = −(T(τ) + T(−τ))` and `‖T(±τ)‖ ≤ e^{a|s|}‖F(±τ)‖`
  have hdec := ghat_zero_decomp hp hint ha.le hLa hτ hX
  have hT1 : ‖Tt L η α a τ‖ ^ 2 ≤ Real.exp (2 * a * |s|) * ‖Fl (psiK L η α a) τ‖ ^ 2 := by
    rw [norm_Tt_eq, mul_pow, ← Real.exp_nat_mul]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
    push_cast; nlinarith [neg_abs_le s, le_abs_self s]
  have hT2 : ‖Tt L η α a (-τ)‖ ^ 2 ≤ Real.exp (2 * a * |s|) * ‖Fl (psiK L η α a) (-τ)‖ ^ 2 := by
    rw [norm_Tt_eq, mul_pow, ← Real.exp_nat_mul, neg_im]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
    push_cast; nlinarith [neg_abs_le s, le_abs_self s]
  have hE := (Real.exp_pos (2 * a * |s|)).le
  calc ‖ghatC (gK L η α a) a τ‖ ^ 2 ≤ (‖Tt L η α a τ‖ + ‖Tt L η α a (-τ)‖) ^ 2 := by
        rw [hdec, norm_neg]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    _ ≤ 2 * (‖Tt L η α a τ‖ ^ 2 + ‖Tt L η α a (-τ)‖ ^ 2) := by
        nlinarith [sq_nonneg (‖Tt L η α a τ‖ - ‖Tt L η α a (-τ)‖)]
    _ ≤ 2 * (Real.exp (2 * a * |s|) * (‖Fl (psiK L η α a) τ‖ ^ 2 + ‖Fl (psiK L η α a) (-τ)‖ ^ 2)) := by
        nlinarith
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hsum hE
        nlinarith

/-- **The zero side at the density level**: if `e^{2a|Im τ|} ≤ κ` at every zero, then
`Q(g) ≤ 4κ ∫ W(x) ‖F(x − i)‖² dx`. -/
theorem weilQ_le_W (hint : ∫ x, Hr L η α x = 0) (ha : 0 < a) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ i : ZeroIdx (sqF Xi), Real.exp (2 * a * |(tau i).im|) ≤ κ)
    (hW : Integrable fun x => Wf x * ‖FT (PsiK L η α a) x‖ ^ 2) :
    weilQ a (gK L η α a) ≤ 4 * κ * ∫ x, Wf x * ‖FT (PsiK L η α a) x‖ ^ 2 := by
  have hp := ht.par
  set F := FT (PsiK L η α a)
  have H := weilQ_eq_zero_sum (probe_gK hp hint ha.le) ha (weilExplicit_gK hp hint ha)
  have Hre := Complex.hasSum_re H
  simp only [Complex.ofReal_re] at Hre
  set c : ZeroIdx (sqF Xi) → ℝ := fun i => 2 * κ * ∫ x, Vz (tau i) x * ‖F x‖ ^ 2
  have hV0 : ∀ i x, 0 ≤ Vz (tau i) x * ‖F x‖ ^ 2 := fun i x =>
    mul_nonneg (Vz_nonneg (tau_im i) x) (sq_nonneg _)
  have hc0 : ∀ i, 0 ≤ c i := fun i => mul_nonneg (by positivity) (integral_nonneg fun x => hV0 i x)
  -- each term
  have hterm : ∀ p : Bool × ZeroIdx (sqF Xi),
      (ghatC (gK L η α a) a ((rhoXi p - 1 / 2) / I) ^ 2).re ≤ c p.2 := by
    intro p
    set t := (rhoXi p - 1 / 2) / I
    have hpair := ghat_sq_le_pair ht hLa hint ha (im_rhoXi p) (Xi_rhoXi p)
    have hV : (fun x => Vz t x * ‖F x‖ ^ 2) = fun x => Vz (tau p.2) x * ‖F x‖ ^ 2 := by
      funext x; simp only [t, ordinate_rhoXi]; split_ifs
      · rfl
      · rw [Vz_neg]
    have hI : |t.im| = |(tau p.2).im| := by
      simp only [t, ordinate_rhoXi]; split_ifs
      · rfl
      · rw [neg_im, abs_neg]
    rw [hV, hI] at hpair
    have hint0 : 0 ≤ ∫ x, Vz (tau p.2) x * ‖F x‖ ^ 2 := integral_nonneg fun x => hV0 p.2 x
    calc (ghatC (gK L η α a) a t ^ 2).re ≤ ‖ghatC (gK L η α a) a t ^ 2‖ := Complex.re_le_norm _
      _ = ‖ghatC (gK L η α a) a t‖ ^ 2 := norm_pow _ _
      _ ≤ 2 * Real.exp (2 * a * |(tau p.2).im|) * ∫ x, Vz (tau p.2) x * ‖F x‖ ^ 2 := hpair
      _ ≤ c p.2 := by
          simp only [c]; gcongr; exact hκ p.2
  -- finite sums
  have hfin : ∀ T : Finset (ZeroIdx (sqF Xi)), ∑ i ∈ T, c i ≤ 2 * κ * ∫ x, Wf x * ‖F x‖ ^ 2 := by
    intro T
    have hint : ∀ i ∈ T, Integrable fun x => Vz (tau i) x * ‖F x‖ ^ 2 := by
      intro i _
      have hs := abs_lt.1 (tau_im i)
      have i1 := integrable_pk_FT ht hLa (by linarith : 0 < 1 + (tau i).im) (tau i).re
      have i2 := integrable_pk_FT ht hLa (by linarith : 0 < 1 - (tau i).im) (-(tau i).re)
      simp only [sub_neg_eq_add] at i2
      refine (i1.add i2).congr (ae_of_all _ fun x => ?_)
      simp only [Pi.add_apply, Vz, add_mul, F]
    have e : ∑ i ∈ T, c i = 2 * κ * ∫ x, (∑ i ∈ T, Vz (tau i) x) * ‖F x‖ ^ 2 := by
      simp only [c]; rw [← Finset.mul_sum, ← integral_finsetSum _ hint]
      congr 1; congr 1; funext x; rw [Finset.sum_mul]
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine integral_mono_of_nonneg (ae_of_all _ fun x => ?_) hW (ae_of_all _ fun x => ?_)
    · exact mul_nonneg (Finset.sum_nonneg fun i _ => Vz_nonneg (tau_im i) x) (sq_nonneg _)
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      refine le_trans ?_ (tsum_Vz_le x)
      exact (hasSum_Vz x).summable.sum_le_tsum T (fun i _ => Vz_nonneg (tau_im i) x)
  rw [← Hre.tsum_eq]
  refine Hre.summable.tsum_le_of_sum_le fun S => ?_
  set T := S.image Prod.snd
  calc ∑ p ∈ S, (ghatC (gK L η α a) a ((rhoXi p - 1 / 2) / I) ^ 2).re ≤ ∑ p ∈ S, c p.2 :=
        Finset.sum_le_sum fun p _ => hterm p
    _ ≤ ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ T, c p.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => by
          simp only [Finset.mem_product, Finset.mem_univ, true_and, T]
          exact Finset.mem_image_of_mem _ hp) (fun p _ _ => hc0 p.2)
    _ = 2 * ∑ i ∈ T, c i := by
        rw [Finset.sum_product]; simp [Finset.sum_const]
    _ ≤ 2 * (2 * κ * ∫ x, Wf x * ‖F x‖ ^ 2) := by gcongr; exact hfin T
    _ = _ := by ring

end Zero

/-! ## Numbers -/

theorem integrable_PsiK_sq (ht : Tail L η α) {a : ℝ} (hLa : Real.exp a = L) :
    Integrable fun w => ‖PsiK L η α a w‖ ^ 2 := by
  set c := 4 * kP η * Real.exp (-(7 / 2) * a)
  have hi : Integrable ((Ioi 0).indicator fun w : ℝ => c ^ 2 * Real.exp (-5 * w)) :=
    IntegrableOn.integrable_indicator ((integrableOn_exp_mul_Ioi (by norm_num : (-5 : ℝ) < 0) 0).const_mul _)
      measurableSet_Ioi
  refine hi.mono' ((measurable_PsiK ht.par a).norm.pow 2) (ae_of_all _ fun w => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := norm_PsiK_le ht hLa w
  by_cases hw : w ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hw] at h ⊢
    calc ‖PsiK L η α a w‖ ^ 2 ≤ (c * Real.exp (-(5 / 2) * w)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = c ^ 2 * Real.exp (-5 * w) := by rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  · rw [indicator_of_notMem hw] at h ⊢
    have := norm_nonneg (PsiK L η α a w); nlinarith

/-- `‖F(x − i)‖ ≤ 8P(1 + D₀)e^{−a}/|x|`. -/
theorem norm_FT_PsiK_le (ht : Tail L η α) {a : ℝ} (hLa : Real.exp a = L) {x : ℝ} (hx : x ≠ 0) :
    ‖FT (PsiK L η α a) x‖ ≤ 8 * kP η * (1 + kD0 L η) * Real.exp (-a) / |x| := by
  rw [← Fl_line_eq]
  have h1 := norm_Tt_eq (L := L) (η := η) (α := α) (a := a) ((x : ℂ) - I)
  have him : ((x : ℂ) - I).im = -1 := by simp
  rw [him] at h1
  have hne : (x : ℂ) - I ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this
  have h2 := tail_ibp_line ht hLa (t := (x : ℂ) - I) (by rw [him]) hne
  have hxn : |x| ≤ ‖(x : ℂ) - I‖ := by
    have := Complex.abs_re_le_norm ((x : ℂ) - I); simpa using this
  have hxa : 0 < |x| := abs_pos.2 hx
  have hP := (kP_pos ht.par.pos).le
  have hD := kD0_nonneg (L := L) ht.par.pos
  have h3 : ‖Tt L η α a ((x : ℂ) - I)‖ ≤ 8 * kP η * (1 + kD0 L η) / |x| :=
    h2.trans (div_le_div_of_nonneg_left (by positivity) hxa hxn)
  rw [h1, mul_neg_one, neg_neg] at h3
  have he := Real.exp_pos a
  calc ‖Fl (psiK L η α a) ((x : ℂ) - I)‖ = Real.exp (-a) * (Real.exp a * ‖Fl (psiK L η α a) ((x : ℂ) - I)‖) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-a) * (8 * kP η * (1 + kD0 L η) / |x|) := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = _ := by ring

/-- `∫ (1 + x²)^{−5/8}`. -/
def I58 : ℝ := ∫ x, rho58 x

theorem I58_nonneg : 0 ≤ I58 := integral_nonneg fun x => by unfold rho58; positivity

/-- The constant of the zero side. -/
def Kz : ℝ := (24 + kLam) * (2 * Real.exp 1 * (16 / 5)) + 2 * ((8 + kLam) / π) * 409600 * I58

theorem Kz_nonneg : 0 ≤ Kz := by
  unfold Kz; have := kLam_nonneg; have := I58_nonneg; positivity

/-- **The zero side at `η = 1/L`**: `Q(g) ≤ 16 κ Kz (a + 1) e^{9a}`. -/
theorem weilQ_prefactor {a : ℝ} (ha : 4 ≤ a) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ i : ZeroIdx (sqF Xi), Real.exp (2 * a * |(tau i).im|) ≤ κ) :
    weilQ a (gK (Real.exp a) (1 / Real.exp a) (kα (Real.exp a)) a) ≤ 16 * κ * Kz * (a + 1) * Real.exp (9 * a) := by
  set L := Real.exp a with hLdef
  have hL : 50 ≤ L := exp_four_ge.trans (Real.exp_le_exp.2 ha)
  have ha0 : 0 < a := by linarith
  have hp := par_inv hL
  obtain ⟨hint, -, hα⟩ := alpha_ok hL
  have ht : Tail L (1 / L) (kα L) := ⟨hp, hα, by linarith⟩
  have hLa : Real.exp a = L := rfl
  set Ψ := PsiK L (1 / L) (kα L) a
  set P := kP (1 / L)
  set D := kD0 L (1 / L)
  have hP := (kP_pos hp.pos).le
  have hD0 : 0 ≤ 1 + D := by linarith [kD0_nonneg (L := L) hp.pos]
  set M := Real.exp (36 * a)
  have hM1 : 1 ≤ M := Real.one_le_exp (by linarith)
  obtain ⟨hW, hWb⟩ := weighted_FT_le (integrable_PsiK ht hLa) (integrable_PsiK_sq ht hLa) hM1
    (fun x hx => norm_FT_PsiK_le ht hLa hx)
  have hQ := weilQ_le_W ht hLa hint ha0 hκ0 hκ hW
  -- the pieces
  have hN2 := integral_PsiK_sq ht hLa
  have hk := kLam_nonneg
  have hWM : Wf M ≤ (24 + kLam) * (a + 1) / π := by
    unfold Wf
    rw [abs_of_pos (Real.exp_pos _)]
    have hlog : Real.log (M + 2) ≤ 36 * a + 2 := by
      have h3 : M + 2 ≤ Real.exp 2 * M := by
        have : 3 ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
        nlinarith
      calc Real.log (M + 2) ≤ Real.log (Real.exp 2 * M) := Real.log_le_log (by positivity) h3
        _ = 36 * a + 2 := by rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_exp]; ring
    apply div_le_div_of_nonneg_right _ pi_pos.le
    nlinarith
  have hrpow : (1 + M ^ 2) ^ (-(1 / 8 : ℝ)) ≤ Real.exp (-(9 * a)) := by
    have h1 : (1 + M ^ 2) ^ (-(1 / 8 : ℝ)) ≤ (M ^ 2) ^ (-(1 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have h2 : (M ^ 2) ^ (-(1 / 8 : ℝ)) = Real.exp (-(9 * a)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_mul]; congr 1; push_cast; ring
    rw [← h2]; exact h1
  have hD : (1 + D) ^ 2 ≤ 6400 * Real.exp (4 * a) := by
    have := pow_le_pow_left₀ hD0 (kD0_inv_le hL) 2
    have e : (80 * L ^ 2) ^ 2 = 6400 * Real.exp (4 * a) := by
      rw [mul_pow, ← pow_mul, hLdef, ← Real.exp_nat_mul]; norm_num
    linarith
  have hB2 : (8 * P * (1 + D) * Real.exp (-a)) ^ 2 * (1 + M ^ 2) ^ (-(1 / 8 : ℝ))
      ≤ 409600 * (P ^ 2 * Real.exp (-(7 * a))) := by
    have hr0 : 0 ≤ (1 + M ^ 2) ^ (-(1 / 8 : ℝ)) := by positivity
    calc (8 * P * (1 + D) * Real.exp (-a)) ^ 2 * (1 + M ^ 2) ^ (-(1 / 8 : ℝ))
        = 64 * P ^ 2 * (1 + D) ^ 2 * Real.exp (-(2 * a)) * (1 + M ^ 2) ^ (-(1 / 8 : ℝ)) := by
          rw [show -(2 * a) = -a + -a by ring, Real.exp_add]; ring
      _ ≤ 64 * P ^ 2 * (6400 * Real.exp (4 * a)) * Real.exp (-(2 * a)) * Real.exp (-(9 * a)) := by
          gcongr
      _ = 409600 * (P ^ 2 * Real.exp (-(7 * a))) := by
          rw [mul_assoc (64 * P ^ 2 * (6400 * Real.exp (4 * a))), ← Real.exp_add,
            show 64 * P ^ 2 * (6400 * Real.exp (4 * a)) * Real.exp (-(2 * a) + -(9 * a))
              = 409600 * (P ^ 2 * (Real.exp (4 * a) * Real.exp (-(2 * a) + -(9 * a)))) by ring,
            ← Real.exp_add]
          congr 3; ring
  have hint2 : ∫ x, Wf x * ‖FT Ψ x‖ ^ 2 ≤ Kz * (a + 1) * (P ^ 2 * Real.exp (-(7 * a))) := by
    refine hWb.trans ?_
    have hc4 : 0 ≤ 2 * ((8 + kLam) / π) := by positivity
    have hI := I58_nonneg
    have hPe : 0 ≤ P ^ 2 * Real.exp (-(7 * a)) := by positivity
    have t1 : Wf M * Real.exp 1 * (2 * π * ∫ w, ‖Ψ w‖ ^ 2) ≤
        (24 + kLam) * (2 * Real.exp 1 * (16 / 5)) * (a + 1) * (P ^ 2 * Real.exp (-(7 * a))) := by
      have hWM0 := Wf_nonneg M
      have hN2' : ∫ w, ‖Ψ w‖ ^ 2 ≤ 16 / 5 * (P ^ 2 * Real.exp (-(7 * a))) := by linarith [hN2]
      calc Wf M * Real.exp 1 * (2 * π * ∫ w, ‖Ψ w‖ ^ 2)
          ≤ (24 + kLam) * (a + 1) / π * Real.exp 1 * (2 * π * (16 / 5 * (P ^ 2 * Real.exp (-(7 * a))))) := by
            gcongr
        _ = _ := by field_simp
    have t2 : 2 * ((8 + kLam) / π) * (8 * P * (1 + D) * Real.exp (-a)) ^ 2 * (1 + M ^ 2) ^ (-(1 / 8 : ℝ)) * I58
        ≤ 2 * ((8 + kLam) / π) * 409600 * I58 * (a + 1) * (P ^ 2 * Real.exp (-(7 * a))) := by
      have := mul_le_mul_of_nonneg_left hB2 hc4
      have h' := mul_le_mul_of_nonneg_right this hI
      have ha1 : 1 ≤ a + 1 := by linarith
      calc _ = 2 * ((8 + kLam) / π) * ((8 * P * (1 + D) * Real.exp (-a)) ^ 2 * (1 + M ^ 2) ^ (-(1 / 8 : ℝ))) * I58 := by ring
        _ ≤ 2 * ((8 + kLam) / π) * (409600 * (P ^ 2 * Real.exp (-(7 * a)))) * I58 := h'
        _ ≤ _ := by
            have : 0 ≤ 2 * ((8 + kLam) / π) * 409600 * I58 * (P ^ 2 * Real.exp (-(7 * a))) := by positivity
            nlinarith
    calc _ ≤ (24 + kLam) * (2 * Real.exp 1 * (16 / 5)) * (a + 1) * (P ^ 2 * Real.exp (-(7 * a)))
          + 2 * ((8 + kLam) / π) * 409600 * I58 * (a + 1) * (P ^ 2 * Real.exp (-(7 * a))) := add_le_add t1 t2
      _ = _ := by unfold Kz; ring
  -- `P² ≤ 4 e^{16a}`
  have hP2 : P ^ 2 ≤ 4 * Real.exp (16 * a) := by
    have h := pow_le_pow_left₀ hP ((kV_ge hp).trans (kV_inv_le hL)) 2
    have e : (2 * L ^ 8) ^ 2 = 4 * Real.exp (16 * a) := by
      rw [mul_pow, ← pow_mul, hLdef, ← Real.exp_nat_mul]; norm_num
    linarith
  have hKz := Kz_nonneg
  calc weilQ a (gK L (1 / L) (kα L) a) ≤ 4 * κ * ∫ x, Wf x * ‖FT Ψ x‖ ^ 2 := hQ
    _ ≤ 4 * κ * (Kz * (a + 1) * (P ^ 2 * Real.exp (-(7 * a)))) := by gcongr
    _ ≤ 4 * κ * (Kz * (a + 1) * (4 * Real.exp (16 * a) * Real.exp (-(7 * a)))) := by gcongr
    _ = 16 * κ * Kz * (a + 1) * Real.exp (9 * a) := by
        rw [mul_assoc 4 (Real.exp (16 * a)), ← Real.exp_add]; ring_nf

/-! ## The ground energy -/

/-- `λ₁(a) ≤ K (a + 1) κ e^{9a − 4πe^{2a}}` whenever `e^{2a|Im τ|} ≤ κ` at every zero. -/
theorem lam_le_kappa : ∃ K, 0 ≤ K ∧ ∀ a, 4 ≤ a → ∀ κ, 0 ≤ κ →
    (∀ i : ZeroIdx (sqF Xi), Real.exp (2 * a * |(tau i).im|) ≤ κ) →
    lam a ≤ K * (a + 1) * κ * Real.exp (9 * a - 4 * π * Real.exp (2 * a)) := by
  have hKz := Kz_nonneg
  set C := 16 * Kz * 5 * 51200 ^ 2 * Real.exp (16 * π + 16)
  refine ⟨C, by positivity, fun a ha κ hκ0 hκ => ?_⟩
  set L := Real.exp a with hLdef
  have hL : 50 ≤ L := exp_four_ge.trans (Real.exp_le_exp.2 ha)
  have ha0 : 0 < a := by linarith
  have hp := par_inv hL
  obtain ⟨hint, -, -⟩ := alpha_ok hL
  have hQ := weilQ_prefactor ha hκ0 hκ
  have hN := normSq_gK_ge hL (a := a) (by linarith)
  have hlam := lam_mul_le (probe_gK hp hint ha0.le (α := kα L))
  have hM : 0 < kM L := Real.exp_pos _
  have hNb : 0 < (kM L / 51200) ^ 2 / 5 := by positivity
  have hE : 0 ≤ Real.exp (9 * a - 4 * π * Real.exp (2 * a)) := (Real.exp_pos _).le
  rcases le_or_gt (lam a) 0 with hl | hl
  · exact hl.trans (by positivity)
  have hNpos : 0 < Pilot1ca.normSq (gK L (1 / L) (kα L) a) := hNb.trans_le hN
  have h1 : lam a ≤ weilQ a (gK L (1 / L) (kα L) a) / Pilot1ca.normSq (gK L (1 / L) (kα L) a) := by
    rw [le_div_iff₀ hNpos]; exact hlam
  have hQ0 : 0 ≤ weilQ a (gK L (1 / L) (kα L) a) := (mul_pos hl hNpos).le.trans hlam
  have h2 := div_le_div₀ (by positivity) hQ hNb hN
  have e1 : kM L ^ 2 = Real.exp (4 * π * L ^ 2) / Real.exp (16 * π + 16) := by
    rw [kM, ← Real.exp_nat_mul, bt_inv_mul hL, ← Real.exp_sub]; congr 1; push_cast; ring
  have e2 : Real.exp (9 * a - 4 * π * Real.exp (2 * a)) = Real.exp (9 * a) / Real.exp (4 * π * L ^ 2) := by
    have f2 : Real.exp (2 * a) = L ^ 2 := by rw [hLdef, ← Real.exp_nat_mul]; norm_num
    rw [Real.exp_sub, f2]
  have e3 : 16 * κ * Kz * (a + 1) * Real.exp (9 * a) / ((kM L / 51200) ^ 2 / 5) =
      C * (a + 1) * κ * Real.exp (9 * a - 4 * π * Real.exp (2 * a)) := by
    rw [div_pow, e1, e2]
    have := Real.exp_pos (4 * π * L ^ 2); have := Real.exp_pos (16 * π + 16)
    simp only [C]; field_simp
  linarith

/-- **Rung 0 at the density level**: `λ₁(a) ≤ K (a + 1) e^{10a − 4πe^{2a}}` for `a ≥ 4`, no RH input.
The factor `e^a` over Connes' `e^{9a}` is `κ = e^a`: a zero with `|Im t| = δ` enters with `e^{2aδ}`. -/
theorem lam_prefactor :
    ∃ K, 0 ≤ K ∧ ∀ a, 4 ≤ a → lam a ≤ K * (a + 1) * Real.exp (10 * a - 4 * π * Real.exp (2 * a)) := by
  obtain ⟨K, hK, h⟩ := lam_le_kappa
  refine ⟨K, hK, fun a ha => ?_⟩
  have ha0 : 0 < a := by linarith
  have hk : ∀ i : ZeroIdx (sqF Xi), Real.exp (2 * a * |(tau i).im|) ≤ Real.exp a := fun i =>
    Real.exp_le_exp.2 (by nlinarith [tau_im i, abs_nonneg (tau i).im])
  refine (h a ha _ (Real.exp_pos a).le hk).trans (le_of_eq ?_)
  rw [mul_assoc (K * (a + 1)), ← Real.exp_add]; ring_nf

end Kaiser

#print axioms Kaiser.tail_ibp_line
#print axioms Kaiser.integral_PsiK_sq
#print axioms Kaiser.Tt_eq
#print axioms Kaiser.weighted_FT_le
#print axioms Kaiser.ghat_sq_le_pair
#print axioms Kaiser.weilQ_le_W
#print axioms Kaiser.weilQ_prefactor
#print axioms Kaiser.lam_prefactor
