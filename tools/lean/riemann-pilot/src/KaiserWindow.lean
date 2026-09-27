import Mathlib
import KaiserIBP
import WeilCriterion

/-! # The Kaiser probe on the window (round 163, part 9)

* `KF_real`: `KF` is real on `(0, ∞)`; the probe is `g = 1_{[−a,a]}·Re KF(eᵘ)`.
* `KF_exp`: `KF(eᵘ) = φ(u) + φ(−u)`, and `KF(eᵘ) = φ(u)` for `u > a` (`eᵃ = L`).
* `ghat_zero_decomp`: at every zero `t` of `Ξ`, `ĝ(t) = −(T(t) + T(−t))`, `T(t) = ∫_a^∞ φ(v)e^{itv}dv`.
-/

open Complex Filter Topology MeasureTheory Real Set

noncomputable section

namespace Kaiser

open Pilot1ca Pilot1bt

variable {L η α : ℝ}

theorem kK_real_ex (β L y : ℝ) : ∃ r : ℝ, kK β L y = r := by
  rcases le_total (L ^ 2) (y ^ 2) with h | h
  · exact ⟨_, kK_real_ge h⟩
  · exact ⟨_, kK_real_le h⟩

theorem sincE_real_ex (x : ℝ) : ∃ r : ℝ, sincE x = r := by
  rcases eq_or_ne x 0 with rfl | h
  · exact ⟨1, by simp [sincE_zero]⟩
  · exact ⟨_, sincE_real x h⟩

theorem Hr_real_ex (y : ℝ) : ∃ r : ℝ, Hr L η α y = r := by
  obtain ⟨r₁, h₁⟩ := kK_real_ex (2 * π * (L - 4 * η)) L y
  obtain ⟨r₂, h₂⟩ := sincE_real_ex (π * η * y)
  refine ⟨y ^ 2 * (y ^ 2 - α) * r₁ * r₂ ^ 8, ?_⟩
  simp only [Hr, kH, h₁, cast_pey, h₂]; push_cast; ring_nf

theorem Hr_im (y : ℝ) : (Hr L η α y).im = 0 := by
  obtain ⟨r, h⟩ := Hr_real_ex y (L := L) (η := η) (α := α); rw [h, ofReal_im]

theorem tsum_im_zero {f : ℕ → ℂ} (hs : Summable f) (h : ∀ n, (f n).im = 0) : (∑' n, f n).im = 0 := by
  rw [Complex.im_tsum hs]; simp [h]

theorem EHr_im (hp : Par L η) {x : ℝ} (hx : 0 < x) : (E (Hr L η α) x).im = 0 := by
  unfold E
  rw [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, tsum_im_zero (summable_Hr_nat' hp hx)
    (fun n => Hr_im _), mul_zero]

theorem KF_im (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {x : ℝ} (hx : 0 < x) :
    (KF L η α x).im = 0 := by
  rw [KF_eq hp hint hx, add_im, EHr_im hp hx, EHr_im hp (one_div_pos.2 hx), add_zero]

theorem KF_real (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {x : ℝ} (hx : 0 < x) :
    ((KF L η α x).re : ℂ) = KF L η α x :=
  Complex.ext (by simp) (by simp [KF_im hp hint hx])

/-- `KF(eᵘ) = φ(u) + φ(−u)`. -/
theorem KF_exp (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) (u : ℝ) :
    KF L η α (Real.exp u) = phi L η α u + phi L η α (-u) := by
  rw [KF_eq hp hint (Real.exp_pos u), phi_eq_E, phi_eq_E, one_div, ← Real.exp_neg]

/-- Beyond the window, `KF(eᵘ) = φ(u)`. -/
theorem KF_exp_tail (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {a u : ℝ} (hLa : Real.exp a = L)
    (hu : a < u) : KF L η α (Real.exp u) = phi L η α u := by
  rw [KF_exp hp hint, phi_eq_E (v := -u), EHr_zero hp hint (Real.exp_pos _), add_zero]
  rw [← hLa, ← Real.exp_add]
  exact Real.exp_lt_one_iff.2 (by linarith)

/-- The Kaiser probe. -/
def gK (L η α a : ℝ) : ℝ → ℝ := (Icc (-a) a).indicator fun u => (KF L η α (Real.exp u)).re

/-- The tail integral. -/
def Tt (L η α a : ℝ) (t : ℂ) : ℂ := ∫ v in Ioi a, phi L η α v * Complex.exp (I * t * v)

theorem integrable_KF_line (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {t : ℂ} (ht : |t.im| < 3 / 2) :
    Integrable fun u : ℝ => KF L η α (Real.exp u) * Complex.exp (I * t * u) := by
  have hm : MellinConvergent (KF L η α) (I * t) :=
    mellinConvergent_of_isBigO_rpow ((continuousOn_KF hp hint).locallyIntegrableOn measurableSet_Ioi)
      (KF_top hp hint) (by simp [mul_re]; linarith [(abs_lt.1 ht).1])
      (KF_bot hp hint) (by simp [mul_re]; linarith [(abs_lt.1 ht).2])
  have h := (integrable_comp_exp (fun y : ℝ => (y : ℂ) ^ (I * t - 1) • KF L η α y)).2 hm
  refine h.congr (Eventually.of_forall fun u => ?_)
  have hpow : (Complex.exp (u : ℂ)) ^ (I * t - 1) = Complex.exp ((I * t - 1) * u) := by
    rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
    ring_nf
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_exp, hpow]
  rw [← mul_assoc, ← Complex.exp_add, mul_comm]; congr 1; ring_nf

/-- **Decomposition at a zero.** -/
theorem ghat_zero_decomp (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {a : ℝ} (ha : 0 ≤ a)
    (hLa : Real.exp a = L) {t : ℂ} (ht : |t.im| < 1 / 2) (hX : Xi t = 0) :
    ghatC (gK L η α a) a t = -(Tt L η α a t + Tt L η α a (-t)) := by
  set F : ℝ → ℂ := fun u => KF L η α (Real.exp u) * Complex.exp (I * t * u)
  have hF := integrable_KF_line hp hint (t := t) (by linarith)
  have h0 : ∫ u, F u = 0 := integral_KF_zero hp hint ht hX
  -- split `ℝ = Iic(−a) ∪ (−a, a] ∪ Ioi a`
  have hsplit : ∫ u, F u = (∫ u in Iic (-a), F u) + (∫ u in (-a)..a, F u) + ∫ u in Ioi a, F u := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hF.integrableOn hF.integrableOn (b := a),
      ← intervalIntegral.integral_Iic_sub_Iic hF.integrableOn hF.integrableOn (a := -a) (b := a)]
    simp only [F]; ring
  -- the window part is `ĝ`
  have hwin : ∫ u in (-a)..a, F u = ghatC (gK L η α a) a t := by
    unfold ghatC
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith)] at hu
    simp only [F, gK, indicator_of_mem hu]
    rw [KF_real hp hint (Real.exp_pos u)]
  -- the right tail
  have hright : ∫ u in Ioi a, F u = Tt L η α a t := by
    unfold Tt
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    simp only [F]; rw [KF_exp_tail hp hint hLa hu]
  -- the left tail, by `u ↦ −u`
  have hleft : ∫ u in Iic (-a), F u = Tt L η α a (-t) := by
    rw [← integral_comp_neg_Ioi]
    unfold Tt
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    simp only [F]
    rw [KF_exp hp hint, neg_neg, phi_eq_E (v := -v), EHr_zero hp hint (Real.exp_pos _), zero_add]
    · congr 1; push_cast; ring_nf
    · rw [← hLa, ← Real.exp_add]; exact Real.exp_lt_one_iff.2 (by have : a < v := hv; linarith)
  rw [hsplit, hwin, hright, hleft] at h0
  linear_combination h0


/-! ## The probe, the strip test, and the zero-side bound -/

/-- `Gc(u) = φ(u) + φ(−u)`. -/
def Gc (L η α : ℝ) (u : ℝ) : ℂ := phi L η α u + phi L η α (-u)
def Gcd (L η α : ℝ) (u : ℝ) : ℂ := phid L η α u - phid L η α (-u)

theorem hasDerivAt_Gc (hp : Par L η) (u : ℝ) : HasDerivAt (Gc L η α) (Gcd L η α u) u := by
  have h2 : HasDerivAt (fun u => phi L η α (-u)) (phid L η α (-u) * (-1)) u := by
    have := (hasDerivAt_phi hp (-u) (α := α)).scomp u (hasDerivAt_neg u)
    convert this using 1
    · rfl
    · rw [Complex.real_smul]; push_cast; ring
  have := (hasDerivAt_phi hp u (α := α)).add h2
  unfold Gc Gcd; convert this using 1; ring

theorem continuous_Gc (hp : Par L η) : Continuous (Gc L η α) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_Gc hp u).continuousAt

theorem continuous_Gcd (hp : Par L η) : Continuous (Gcd L η α) := by
  have h := (continuousOn_phid hp (α := α))
  rw [continuousOn_univ] at h
  unfold Gcd; fun_prop

theorem gK_eq_Gc (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {a u : ℝ} (hu : u ∈ Icc (-a) a) :
    ((gK L η α a u : ℝ) : ℂ) = Gc L η α u := by
  simp only [gK, indicator_of_mem hu]
  rw [KF_real hp hint (Real.exp_pos u), KF_exp hp hint]; rfl

theorem gK_re (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) (u : ℝ) :
    (KF L η α (Real.exp u)).re = (Gc L η α u).re := by
  rw [KF_exp hp hint]; rfl

theorem probe_gK (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {a : ℝ} (ha : 0 ≤ a) :
    Probe a (gK L η α a) := by
  set φ : ℝ → ℝ := fun u => (KF L η α (Real.exp u)).re
  have hφ : φ = fun u => (Gc L η α u).re := funext (gK_re hp hint)
  have hc : Continuous φ := by rw [hφ]; exact Complex.continuous_re.comp (continuous_Gc hp)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.continuousOn (s := Icc (-a) a))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_Gcd hp (α := α)).continuousOn (s := Icc (-a) a))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC a ⟨by linarith, le_rfl⟩)
  have hMb : ∀ t ∈ Icc (-a) a, φ t ^ 2 ≤ M ^ 2 := fun t ht => by
    have := hM t ht; rw [Real.norm_eq_abs] at this
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hLip : ∀ t ∈ Icc (-a) a, ∀ s ∈ Icc (-a) a, ‖Gc L η α t - Gc L η α s‖ ≤ C * ‖t - s‖ :=
    fun t ht s hs => (convex_Icc (-a) a).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (hasDerivAt_Gc hp x).hasDerivWithinAt) (fun x hx => hC x hx) hs ht
  have hD : ∀ t ∈ Icc (-a) a, ∀ s ∈ Icc (-a) a, (φ t - φ s) ^ 2 ≤ (C ^ 2 * (2 * a)) * |t - s| := by
    intro t ht s hs
    have h1 : |φ t - φ s| ≤ C * |t - s| := by
      rw [hφ]; simp only
      calc |(Gc L η α t).re - (Gc L η α s).re| = |(Gc L η α t - Gc L η α s).re| := by rw [sub_re]
        _ ≤ ‖Gc L η α t - Gc L η α s‖ := Complex.abs_re_le_norm _
        _ ≤ C * ‖t - s‖ := hLip t ht s hs
        _ = C * |t - s| := by rw [Real.norm_eq_abs]
    have h2 : |t - s| ≤ 2 * a := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
    have h3 : (φ t - φ s) ^ 2 ≤ (C * |t - s|) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc (φ t - φ s) ^ 2 ≤ (C * |t - s|) ^ 2 := h3
      _ = C ^ 2 * |t - s| * |t - s| := by ring
      _ ≤ C ^ 2 * |t - s| * (2 * a) := by gcongr
      _ = _ := by ring
  obtain ⟨hm, harch, -, -⟩ := ind_energy ha hc hMb hD (by positivity)
  refine ⟨fun u => ?_, fun u hu => ?_, hm, harch⟩
  · unfold gK
    by_cases h : u ∈ Icc (-a) a
    · have h' : -u ∈ Icc (-a) a := ⟨by linarith [h.2], by linarith [h.1]⟩
      rw [indicator_of_mem h, indicator_of_mem h', gK_re hp hint, gK_re hp hint]
      simp only [Gc, neg_neg]; rw [add_comm]
    · have h' : -u ∉ Icc (-a) a := fun h' => h ⟨by linarith [h'.2], by linarith [h'.1]⟩
      rw [indicator_of_notMem h, indicator_of_notMem h']
  · unfold gK
    apply indicator_of_notMem
    intro h; have := abs_le.2 ⟨h.1, h.2⟩; linarith

/-- **`‖ĝ(t)‖ ≤ B/‖t‖` on the strip** (integration by parts on the window). -/
theorem ghat_inv (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {a : ℝ} (ha : 0 ≤ a) :
    ∃ B, 0 ≤ B ∧ ∀ t ∈ PilotWeil.strip (-1) 1, t ≠ 0 → ‖ghatC (gK L η α a) a t‖ ≤ B / ‖t‖ := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_Gc hp (α := α)).continuousOn (s := Icc (-a) a))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_Gcd hp (α := α)).continuousOn (s := Icc (-a) a))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨by linarith, le_rfl⟩)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC a ⟨by linarith, le_rfl⟩)
  refine ⟨(2 * M + 2 * a * C) * Real.exp a, by positivity, fun t ht ht0 => ?_⟩
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht0
  have hIt : I * t ≠ 0 := mul_ne_zero I_ne_zero ht0
  have hItn : ‖I * t‖ = ‖t‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  set v : ℝ → ℂ := fun x => Complex.exp (I * t * x) / (I * t)
  have hv : ∀ x : ℝ, HasDerivAt v (Complex.exp (I * t * x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => I * t * (x : ℂ)) (I * t) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (I * t)
    have := (h1.cexp).div_const (I * t)
    convert this using 1; field_simp
  have hexp : ∀ x ∈ Icc (-a) a, ‖Complex.exp (I * t * x)‖ ≤ Real.exp a := by
    intro x hx
    rw [Complex.norm_exp]; apply Real.exp_le_exp.2
    have : (I * t * (x : ℂ)).re = -(t.im * x) := by simp [mul_re, mul_im]
    rw [this]
    have h1 : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
    have h2 : |x| ≤ a := abs_le.2 ⟨hx.1, hx.2⟩
    calc -(t.im * x) ≤ |t.im * x| := neg_le_abs _
      _ = |t.im| * |x| := abs_mul _ _
      _ ≤ 1 * a := by gcongr
      _ = a := one_mul a
  have hvn : ∀ x ∈ Icc (-a) a, ‖v x‖ ≤ Real.exp a / ‖t‖ := by
    intro x hx; simp only [v, norm_div, hItn]; gcongr; exact hexp x hx
  have hg : ghatC (gK L η α a) a t = ∫ x in (-a)..a, Gc L η α x * Complex.exp (I * t * x) := by
    unfold ghatC
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    rw [gK_eq_Gc hp hint hx]
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -a) (b := a)
    (u := Gc L η α) (u' := Gcd L η α) (v := v) (v' := fun x : ℝ => Complex.exp (I * t * x))
    (fun x _ => hasDerivAt_Gc hp x) (fun x _ => hv x)
    ((continuous_Gcd hp).intervalIntegrable _ _) ((by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (I * t * x)).intervalIntegrable _ _)
  rw [hg, hIBP]
  have hma : a ∈ Icc (-a) a := ⟨by linarith, le_rfl⟩
  have hmma : -a ∈ Icc (-a) a := ⟨le_rfl, by linarith⟩
  have hint2 : ‖∫ x in (-a)..a, Gcd L η α x * v x‖ ≤ C * (Real.exp a / ‖t‖) * |a - -a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le (by linarith)] at hx
    have hx' : x ∈ Icc (-a) a := ⟨hx.1.le, hx.2⟩
    rw [norm_mul]; gcongr
    · exact hC x hx'
    · exact hvn x hx'
  have habs : |a - -a| = 2 * a := by rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (by linarith)]
  rw [habs] at hint2
  calc ‖Gc L η α a * v a - Gc L η α (-a) * v (-a) - ∫ x in (-a)..a, Gcd L η α x * v x‖
      ≤ ‖Gc L η α a‖ * ‖v a‖ + ‖Gc L η α (-a)‖ * ‖v (-a)‖ + ‖∫ x in (-a)..a, Gcd L η α x * v x‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) le_rfl)
        rw [norm_mul, norm_mul]
    _ ≤ M * (Real.exp a / ‖t‖) + M * (Real.exp a / ‖t‖) + C * (Real.exp a / ‖t‖) * (2 * a) := by
        gcongr
        · exact hM a hma
        · exact hvn a hma
        · exact hM (-a) hmma
        · exact hvn (-a) hmma
    _ = (2 * M + 2 * a * C) * Real.exp a / ‖t‖ := by ring

theorem weilExplicit_gK (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {a : ℝ} (ha : 0 < a) :
    WeilExplicit rhoXi (fun z => ghatC (gK L η α a) a z ^ 2) (hsq (gK L η α a) a) := by
  have hpr := probe_gK hp hint ha.le (α := α)
  obtain ⟨B, hB, hb⟩ := ghat_inv hp hint ha.le (α := α)
  obtain ⟨K, hK⟩ := ghat_strip_of_inv ha.le hB hpr.intervalIntegrable hb
  exact weilExplicit_Xi (striptest_sq (ghatC_differentiable hpr.intervalIntegrable) hK)
    (fun t => even_ghat_sq hpr.even a t) (hsq_ofReal hpr ha.le)

/-- Pointwise zero-side bound: `‖ĝ(t)‖² ≤ 720 P²(1+D₀)² ‖1/(t²+4)‖` at every zero of `Ξ`. -/
theorem ghat_zero_sq_le (ht : Tail L η α) (hint : ∫ x, Hr L η α x = 0) {a : ℝ} (hLa : Real.exp a = L)
    {t : ℂ} (hti : |t.im| < 1 / 2) (hX : Xi t = 0) :
    ‖ghatC (gK L η α a) a t‖ ^ 2 ≤ 720 * kP η ^ 2 * (1 + kD0 L η) ^ 2 * ‖1 / (t ^ 2 + 4)‖ := by
  have hp := ht.par
  have ha0 : 0 ≤ a := by rw [← Real.exp_le_exp, Real.exp_zero, hLa]; exact ht.one
  have ht0 : t ≠ 0 := by rintro rfl; exact Xi_zero_ne_zero hX
  have hti' : |t.im| ≤ 1 / 2 := hti.le
  have htim' : |(-t).im| ≤ 1 / 2 := by rw [neg_im, abs_neg]; exact hti'
  have hP := (kP_pos hp.pos).le
  have hD := kD0_nonneg (L := L) hp.pos
  set Mx := 6 * kP η * (1 + kD0 L η)
  have hMx : 0 ≤ Mx := by positivity
  have hdec := ghat_zero_decomp hp hint ha0 hLa hti hX
  have hsum : ‖ghatC (gK L η α a) a t‖ ≤ ‖Tt L η α a t‖ + ‖Tt L η α a (-t)‖ := by
    rw [hdec, norm_neg]; exact norm_add_le _ _
  -- `t² + 4 ≠ 0` and `‖t² + 4‖ ≤ ‖t‖² + 4`
  have hre : 0 < (t ^ 2 + 4).re := by
    have : t.im ^ 2 ≤ 1 / 4 := by nlinarith [abs_lt.1 hti, sq_abs t.im]
    simp [sq, mul_re]; nlinarith [sq_nonneg t.re]
  have hne : t ^ 2 + 4 ≠ 0 := fun h => by rw [h, zero_re] at hre; exact lt_irrefl 0 hre
  have hn4 : 0 < ‖t ^ 2 + 4‖ := norm_pos_iff.2 hne
  have hup : ‖t ^ 2 + 4‖ ≤ ‖t‖ ^ 2 + 4 := by
    refine (norm_add_le _ _).trans ?_; rw [norm_pow]; norm_num
  have hinv : ‖1 / (t ^ 2 + 4)‖ = 1 / ‖t ^ 2 + 4‖ := by rw [norm_div, norm_one]
  rw [hinv]
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht0
  rcases le_or_gt 1 ‖t‖ with h1 | h1
  · -- `‖ĝ‖ ≤ 2Mx/‖t‖`
    have hb : ‖ghatC (gK L η α a) a t‖ ≤ 2 * Mx / ‖t‖ := by
      refine hsum.trans ?_
      have h1 := tail_ibp ht hLa hti' ht0
      have h2 := tail_ibp ht hLa htim' (neg_ne_zero.2 ht0)
      rw [norm_neg] at h2
      simp only [Tt]
      calc _ ≤ Mx / ‖t‖ + Mx / ‖t‖ := add_le_add h1 h2
        _ = 2 * Mx / ‖t‖ := by ring
    have hsq : ‖ghatC (gK L η α a) a t‖ ^ 2 ≤ (2 * Mx) ^ 2 / ‖t‖ ^ 2 := by
      exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans (le_of_eq (div_pow _ _ _))
    have h5 : ‖t ^ 2 + 4‖ ≤ 5 * ‖t‖ ^ 2 := by nlinarith
    calc ‖ghatC (gK L η α a) a t‖ ^ 2 ≤ (2 * Mx) ^ 2 / ‖t‖ ^ 2 := hsq
      _ ≤ (2 * Mx) ^ 2 * 5 / ‖t ^ 2 + 4‖ := by
          rw [div_le_div_iff₀ (by positivity) hn4]; nlinarith [sq_nonneg (2 * Mx)]
      _ = 720 * kP η ^ 2 * (1 + kD0 L η) ^ 2 * (1 / ‖t ^ 2 + 4‖) := by simp only [Mx]; ring
  · -- `‖ĝ‖ ≤ 4P`
    have hb : ‖ghatC (gK L η α a) a t‖ ≤ 4 * kP η := by
      refine hsum.trans ?_
      have h1 := tail_le0 ht hLa hti'
      have h2 := tail_le0 ht hLa htim'
      simp only [Tt]; linarith
    have h5 : ‖t ^ 2 + 4‖ ≤ 5 := by nlinarith
    have hP1 : 4 * kP η ≤ 2 * Mx := by simp only [Mx]; nlinarith
    calc ‖ghatC (gK L η α a) a t‖ ^ 2 ≤ (2 * Mx) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb.trans hP1) 2
      _ ≤ (2 * Mx) ^ 2 * 5 / ‖t ^ 2 + 4‖ := by
          rw [le_div_iff₀ hn4]; nlinarith [sq_nonneg (2 * Mx)]
      _ = 720 * kP η ^ 2 * (1 + kD0 L η) ^ 2 * (1 / ‖t ^ 2 + 4‖) := by simp only [Mx]; ring

/-- **The zero side.** `Q(g) ≤ 720 P²(1+D₀)² Σ_ρ ‖1/(t_ρ²+4)‖`. -/
theorem weilQ_gK_le (ht : Tail L η α) (hint : ∫ x, Hr L η α x = 0) {a : ℝ} (ha : 0 < a)
    (hLa : Real.exp a = L) :
    weilQ a (gK L η α a) ≤ 720 * kP η ^ 2 * (1 + kD0 L η) ^ 2 *
      ∑' p : Bool × ZeroIdx (sqF Xi), ‖1 / (((rhoXi p - 1 / 2) / Complex.I) ^ 2 + 4)‖ := by
  have hp := ht.par
  have H := weilQ_eq_zero_sum (probe_gK hp hint ha.le) ha (weilExplicit_gK hp hint ha)
  have Hre := Complex.reCLM.hasSum H
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at Hre
  refine hasSum_le (fun p => ?_) Hre (summable_four_Xi.hasSum.mul_left _)
  calc _ ≤ ‖ghatC (gK L η α a) a ((rhoXi p - 1 / 2) / Complex.I) ^ 2‖ := Complex.re_le_norm _
    _ = _ := norm_pow _ _
    _ ≤ _ := ghat_zero_sq_le ht hint hLa (im_rhoXi p) (Xi_rhoXi p)

end Kaiser

#print axioms Kaiser.probe_gK
#print axioms Kaiser.ghat_inv
#print axioms Kaiser.weilExplicit_gK

#print axioms Kaiser.KF_real
#print axioms Kaiser.ghat_zero_decomp
#print axioms Kaiser.weilQ_gK_le
