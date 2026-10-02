import Mathlib
import KaiserMellin
import WeilZeta

/-! # The Kaiser trial's full transform vanishes at every zero of `Ξ` (round 163, part 5)

`Kf = h + H` (self-dual) and `KF = E Kf`. For `x > 0`, `KF x = E H x + E H (1/x)` (Poisson), with
`E H x = 0` for `x < 1/L` (Paley–Wiener), so `KF = O(x^{∓3/2})` at `∞` and `0`. Its Mellin transform
is analytic on `|Re s| < 3/2` and equals `ζ(s + ½)·𝓜Kf(s + ½)` for `½ < Re s < 3/2` (`mellin_E`).
By the identity theorem on the convex half-strips `−½ < Re s < 1`, `±Im s > 0`, the identity holds at
`s = it` for every zero `t` of `Ξ`, where `ζ(½ + it) = 0`. Hence (`integral_KF_zero`)

  `∫_ℝ KF(eᵘ) e^{itu} du = 0`   whenever `Ξ(t) = 0`.
-/

open Complex Filter Topology MeasureTheory Real Set Asymptotics

noncomputable section

namespace Kaiser

open Pilot1ca Pilot1bt

variable {L η α : ℝ}

/-- The self-dual trial `f = h + H`. -/
def Kf (L η α : ℝ) (x : ℝ) : ℂ := kh L η α x + Hr L η α x

/-- Connes' periodisation of the trial. -/
def KF (L η α : ℝ) : ℝ → ℂ := E (Kf L η α)

theorem continuous_Kf (hp : Par L η) : Continuous (Kf L η α) :=
  (continuous_kh hp).add continuous_Hr

theorem Kf_bound (hp : Par L η) : ∃ C, ∀ x, 0 < x → ‖Kf L η α x‖ ≤ C / (1 + x ^ 2) := by
  obtain ⟨M, hM⟩ := (continuous_kh hp (α := α)).bounded_above_of_compact_support
    (hasCompactSupport_kh hp)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hA := kA_nonneg L η α
  have hL : 0 ≤ L := by linarith [hp.big, hp.pos]
  refine ⟨M * (1 + L ^ 2) + kA L η α, fun x hx => ?_⟩
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hH := norm_Hr_le hp x (α := α)
  have hk : ‖kh L η α x‖ ≤ M * (1 + L ^ 2) / (1 + x ^ 2) := by
    rcases le_or_gt x L with h | h
    · rw [le_div_iff₀ hd]
      have : 1 + x ^ 2 ≤ 1 + L ^ 2 := by nlinarith
      nlinarith [hM x, norm_nonneg (kh L η α x)]
    · rw [kh_vanish hp (by rwa [abs_of_pos hx]), norm_zero]; positivity
  calc ‖Kf L η α x‖ ≤ ‖kh L η α x‖ + ‖Hr L η α x‖ := norm_add_le _ _
    _ ≤ M * (1 + L ^ 2) / (1 + x ^ 2) + kA L η α / (1 + x ^ 2) := add_le_add hk hH
    _ = (M * (1 + L ^ 2) + kA L η α) / (1 + x ^ 2) := by ring

theorem summable_Hr_nat' (hp : Par L η) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => Hr L η α ((n + 1) * x) :=
  (summable_Hr_nat hp (inv_pos.2 hx) (α := α)).congr fun n => by rw [div_inv_eq_mul]

theorem E_add (hp : Par L η) {x : ℝ} (hx : 0 < x) :
    E (Kf L η α) x = E (kh L η α) x + E (Hr L η α) x := by
  unfold E Kf
  rw [← mul_add, ← (summable_kh_nat hp hx).tsum_add (summable_Hr_nat' hp hx)]

/-- `KF x = E H x + E H (1/x)`. -/
theorem KF_eq (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {x : ℝ} (hx : 0 < x) :
    KF L η α x = E (Hr L η α) x + E (Hr L η α) (1 / x) := by
  rw [KF, E_add hp hx, poisson_E hp hint hx, add_comm]

/-- `E h y = 0` for `y > L`. -/
theorem Ekh_zero (hp : Par L η) {y : ℝ} (hy : L < y) : E (kh L η α) y = 0 := by
  unfold E
  have : ∀ n : ℕ, kh L η α ((n + 1) * y) = 0 := fun n => by
    apply kh_vanish hp
    have hy0 : 0 < y := by linarith [hp.big, hp.pos]
    rw [abs_of_pos (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  simp [this]

/-- `E H x = 0` for `0 < x < 1/L`. -/
theorem EHr_zero (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {x : ℝ} (hx : 0 < x) (hxL : x * L < 1) :
    E (Hr L η α) x = 0 := by
  have h := poisson_E hp hint (inv_pos.2 hx) (α := α)
  rw [one_div, inv_inv] at h
  rw [← h]
  apply Ekh_zero hp
  have h1 : L = (x * L) * x⁻¹ := by field_simp
  rw [h1]
  calc x * L * x⁻¹ < 1 * x⁻¹ := mul_lt_mul_of_pos_right hxL (inv_pos.2 hx)
    _ = x⁻¹ := one_mul _

theorem tsum_inv_sq_succ_le : ∑' n : ℕ, ((n : ℝ) + 1)⁻¹ ^ 2 ≤ 2 := by
  have h := hasSum_zeta_two
  have hs : HasSum (fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2) (π ^ 2 / 6) := by
    rw [← hasSum_nat_add_iff' 1] at h
    simpa [Finset.sum_range_one, one_div, inv_pow] using h
  rw [hs.tsum_eq]
  have := Real.pi_lt_d2; nlinarith [Real.pi_pos]

/-- `‖E H x‖ ≤ 2A x^{−3/2}`. -/
theorem EHr_bound (hp : Par L η) {x : ℝ} (hx : 0 < x) :
    ‖E (Hr L η α) x‖ ≤ 2 * kA L η α * x ^ (-(3 / 2 : ℝ)) := by
  have hA := kA_nonneg L η α
  have hb : ∀ n : ℕ, ‖Hr L η α ((n + 1) * x)‖ ≤ kA L η α * x⁻¹ ^ 2 * ((n : ℝ) + 1)⁻¹ ^ 2 := by
    intro n
    refine (norm_Hr_le hp _).trans ?_
    have hn : (0 : ℝ) < n + 1 := by positivity
    rw [div_le_iff₀ (by positivity)]
    have e : kA L η α * x⁻¹ ^ 2 * ((n : ℝ) + 1)⁻¹ ^ 2 * (1 + ((n + 1) * x) ^ 2)
        = kA L η α * (x⁻¹ ^ 2 * ((n : ℝ) + 1)⁻¹ ^ 2 + 1) := by field_simp
    rw [e]; nlinarith [sq_nonneg (x⁻¹ * ((n : ℝ) + 1)⁻¹)]
  have hsum := summable_inv_sq_succ.mul_left (kA L η α * x⁻¹ ^ 2)
  unfold E
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt x * ‖∑' n : ℕ, Hr L η α ((n + 1) * x)‖
      ≤ Real.sqrt x * ∑' n : ℕ, kA L η α * x⁻¹ ^ 2 * ((n : ℝ) + 1)⁻¹ ^ 2 := by
        gcongr; exact tsum_of_norm_bounded hsum.hasSum hb
    _ = Real.sqrt x * (kA L η α * x⁻¹ ^ 2) * ∑' n : ℕ, ((n : ℝ) + 1)⁻¹ ^ 2 := by
        rw [tsum_mul_left]; ring
    _ ≤ Real.sqrt x * (kA L η α * x⁻¹ ^ 2) * 2 := by gcongr; exact tsum_inv_sq_succ_le
    _ = 2 * kA L η α * x ^ (-(3 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, show (-(3 / 2 : ℝ)) = 1 / 2 - 2 by norm_num, Real.rpow_sub hx,
          Real.rpow_two, inv_pow]; field_simp

theorem continuousOn_EHr (hp : Par L η) : ContinuousOn (E (Hr L η α)) (Ioi 0) := by
  intro x₀ hx₀
  have hx₀ : (0 : ℝ) < x₀ := hx₀
  have hA := kA_nonneg L η α
  set δ := x₀ / 2
  have hδ : 0 < δ := by positivity
  have hc : ContinuousOn (fun x => ∑' n : ℕ, Hr L η α ((n + 1) * x)) (Ioi δ) := by
    refine continuousOn_tsum (fun n => (continuous_Hr.comp (continuous_const.mul continuous_id)).continuousOn)
      (summable_inv_sq_succ.mul_left (kA L η α * δ⁻¹ ^ 2)) fun n x hx => ?_
    have hx : δ < x := hx
    have hn : (0 : ℝ) < n + 1 := by positivity
    refine (norm_Hr_le hp _).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have hxd : δ ^ 2 ≤ x ^ 2 := by nlinarith
    have e : kA L η α * δ⁻¹ ^ 2 * ((n : ℝ) + 1)⁻¹ ^ 2 * (1 + ((n + 1) * x) ^ 2)
        ≥ kA L η α * (x ^ 2 / δ ^ 2) := by
      have : δ⁻¹ ^ 2 * ((n : ℝ) + 1)⁻¹ ^ 2 * (1 + ((n + 1) * x) ^ 2) ≥ x ^ 2 / δ ^ 2 := by
        rw [ge_iff_le, div_le_iff₀ (by positivity)]
        field_simp
        nlinarith [sq_nonneg ((n : ℝ) + 1), sq_nonneg x]
      nlinarith
    have : kA L η α ≤ kA L η α * (x ^ 2 / δ ^ 2) := by
      have : 1 ≤ x ^ 2 / δ ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith
    linarith
  have hsqrt : ContinuousOn (fun x : ℝ => (Real.sqrt x : ℂ)) (Ioi δ) :=
    (continuous_ofReal.comp Real.continuous_sqrt).continuousOn
  have hmem : Ioi δ ∈ 𝓝 x₀ := Ioi_mem_nhds (by simp only [δ]; linarith)
  exact ((hsqrt.mul hc).continuousAt hmem).continuousWithinAt

theorem continuousOn_KF (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) :
    ContinuousOn (KF L η α) (Ioi 0) := by
  have h1 := continuousOn_EHr hp (α := α)
  have h2 : ContinuousOn (fun x : ℝ => E (Hr L η α) (1 / x)) (Ioi 0) := by
    refine h1.comp (continuousOn_const.div continuousOn_id fun x hx => (ne_of_gt hx)) fun x hx => ?_
    exact one_div_pos.2 (mem_Ioi.1 hx)
  exact (h1.add h2).congr fun x hx => KF_eq hp hint hx

theorem KF_top (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) :
    KF L η α =O[atTop] (· ^ (-(3 / 2 : ℝ))) := by
  refine IsBigO.of_bound (2 * kA L η α) ?_
  have hL : 0 < L := by linarith [hp.big, hp.pos]
  filter_upwards [eventually_gt_atTop L] with x hx
  have hx0 : 0 < x := by linarith
  rw [KF_eq hp hint hx0, EHr_zero hp hint (one_div_pos.2 hx0) (by rw [one_div, inv_mul_lt_iff₀ hx0]; linarith),
    add_zero, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  exact EHr_bound hp hx0

theorem KF_bot (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) :
    KF L η α =O[𝓝[>] 0] (· ^ (-(-(3 / 2) : ℝ))) := by
  refine IsBigO.of_bound (2 * kA L η α) ?_
  have hL : 0 < L := by linarith [hp.big, hp.pos]
  have hmem : Ioo (0 : ℝ) L⁻¹ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (inv_pos.2 hL)
  filter_upwards [hmem] with x hx
  obtain ⟨hx0, hxL⟩ := hx
  rw [KF_eq hp hint hx0, EHr_zero hp hint hx0 (by
    have := mul_lt_mul_of_pos_right hxL hL; rwa [inv_mul_cancel₀ hL.ne'] at this), zero_add,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  refine (EHr_bound hp (one_div_pos.2 hx0)).trans (le_of_eq ?_)
  rw [one_div, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]


theorem differentiableAt_mellin_KF (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {s : ℂ}
    (h1 : -(3 / 2) < s.re) (h2 : s.re < 3 / 2) : DifferentiableAt ℂ (mellin (KF L η α)) s :=
  mellin_differentiableAt_of_isBigO_rpow
    ((continuousOn_KF hp hint).locallyIntegrableOn measurableSet_Ioi) (KF_top hp hint) h2
    (KF_bot hp hint) (by linarith)

theorem differentiableAt_rhs (hp : Par L η) {s : ℂ} (h1 : -(1 / 2) < s.re) (h2 : s.re < 3 / 2)
    (hs : s.im ≠ 0) :
    DifferentiableAt ℂ (fun s => riemannZeta (s + 1 / 2) * mellin (Kf L η α) (s + 1 / 2)) s := by
  obtain ⟨C, hC⟩ := Kf_bound hp (α := α)
  have hz : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (s + 1 / 2)) s := by
    refine (differentiableAt_riemannZeta ?_).comp s (differentiableAt_id.add_const _)
    intro h; apply hs; have := congrArg Complex.im h; simpa using this
  have hm : DifferentiableAt ℂ (fun s : ℂ => mellin (Kf L η α) (s + 1 / 2)) s := by
    refine (mellin_differentiableAt_of_isBigO_rpow
      ((continuous_Kf hp).continuousOn.locallyIntegrableOn measurableSet_Ioi)
      (isBigO_top_of_bound hC) ?_ (isBigO_bot_of_bound hC) ?_).comp s
      (differentiableAt_id.add_const _)
    · simp; linarith
    · simp; linarith
  exact hz.mul hm

/-- The half-strip `−½ < Re s < 1`, `σ · Im s > 0`. -/
def hstrip (σ : ℝ) : Set ℂ := {s | -(1 / 2) < s.re ∧ s.re < 1 ∧ 0 < σ * s.im}

theorem isOpen_hstrip (σ : ℝ) : IsOpen (hstrip σ) := by
  unfold hstrip
  simp only [Set.ofPred_and]
  exact (isOpen_lt continuous_const continuous_re).inter ((isOpen_lt continuous_re continuous_const).inter
    (isOpen_lt continuous_const (continuous_const.mul continuous_im)))

theorem convex_hstrip (σ : ℝ) : Convex ℝ (hstrip σ) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [hstrip, Set.mem_ofPred_eq, add_re, add_im, smul_re, smul_im, smul_eq_mul]
  rcases eq_or_lt_of_le ha with h | h
  · subst h
    have hb1 : b = 1 := by linarith
    subst hb1; simp only [zero_mul, zero_add, one_mul]; exact ⟨hy1, hy2, hy3⟩
  · refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_pos h (by linarith : (0:ℝ) < x.re + 1 / 2), mul_nonneg hb (by linarith : (0:ℝ) ≤ y.re + 1 / 2)]
    · nlinarith [mul_pos h (by linarith : (0:ℝ) < 1 - x.re), mul_nonneg hb (by linarith : (0:ℝ) ≤ 1 - y.re)]
    · nlinarith [mul_pos h hx3, mul_nonneg hb hy3.le]

/-- **The Mellin identity on both half-strips.** -/
theorem mellin_KF_eq (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {s : ℂ} (hs : s ∈ hstrip σ) :
    mellin (KF L η α) s = riemannZeta (s + 1 / 2) * mellin (Kf L η α) (s + 1 / 2) := by
  obtain ⟨C, hC⟩ := Kf_bound hp (α := α)
  set U := hstrip σ
  have hU := isOpen_hstrip σ
  have hne : ∀ z ∈ U, z.im ≠ 0 := fun z hz h => by
    have := hz.2.2; rw [h, mul_zero] at this; exact lt_irrefl 0 this
  have hf : AnalyticOnNhd ℂ (mellin (KF L η α)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    exact (differentiableAt_mellin_KF hp hint (by linarith [hz.1]) (by linarith [hz.2.1])).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun s => riemannZeta (s + 1 / 2) * mellin (Kf L η α) (s + 1 / 2)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    exact (differentiableAt_rhs hp hz.1 (by linarith [hz.2.1]) (hne z hz)).differentiableWithinAt
  set z₀ : ℂ := 3 / 4 + σ * I
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> subst h <;> norm_num
  have hz₀ : z₀ ∈ U := by
    simp only [U, hstrip, Set.mem_ofPred_eq, z₀, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
      I_re, I_im]
    norm_num; nlinarith
  have hW : {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} ∈ 𝓝 z₀ := by
    refine ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)).mem_nhds ?_
    simp only [z₀]; norm_num
  have hev : mellin (KF L η α) =ᶠ[𝓝 z₀] fun s => riemannZeta (s + 1 / 2) * mellin (Kf L η α) (s + 1 / 2) := by
    filter_upwards [hW] with z hz
    exact mellin_E (continuous_Kf hp).continuousOn hC hz.1 (by linarith [hz.2])
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_hstrip σ).isPreconnected hz₀ hev hs

/-- **Vanishing at the zeros of `Ξ`.** -/
theorem mellin_KF_zero (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {t : ℂ} (ht : |t.im| < 1 / 2)
    (hX : Xi t = 0) : mellin (KF L η α) (I * t) = 0 := by
  have hre : (I * t).re = -t.im := by simp [mul_re]
  have him : (I * t).im = t.re := by simp [mul_im]
  have htr : t.re ≠ 0 := by
    intro h
    have : t = I * (t.im : ℂ) := by apply Complex.ext <;> simp [h]
    exact Xi_I_mul_ne_zero t.im (this ▸ hX)
  have hζ : riemannZeta (I * t + 1 / 2) = 0 := by
    have hz := (nontrivial_iff_Xi (I * t + 1 / 2)).2 (by
      rw [show (I * t + 1 / 2 - 1 / 2) / I = t by field_simp; ring]; exact hX)
    exact hz.1
  obtain ⟨hl, hr⟩ := abs_lt.1 ht
  rcases lt_or_gt_of_ne htr with h | h
  · rw [mellin_KF_eq hp hint (σ := -1) (Or.inr rfl) ⟨by linarith, by linarith, by rw [him]; linarith⟩,
      hζ, zero_mul]
  · rw [mellin_KF_eq hp hint (σ := 1) (Or.inl rfl) ⟨by linarith, by linarith, by rw [him]; linarith⟩,
      hζ, zero_mul]

/-- The full-line transform is the Mellin transform on the imaginary axis. -/
theorem integral_KF (t : ℂ) :
    ∫ u : ℝ, KF L η α (Real.exp u) * Complex.exp (I * t * u) = mellin (KF L η α) (I * t) := by
  rw [mellin, ← integral_comp_exp]
  congr 1; funext u
  have hpow : ((Real.exp u : ℝ) : ℂ) ^ (I * t - 1) = Complex.exp ((I * t - 1) * u) := by
    rw [Complex.ofReal_exp, cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
    ring_nf
  rw [smul_eq_mul, hpow, Complex.real_smul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  ring_nf

/-- **The trial's full transform vanishes at every zero of `Ξ` in the strip.** -/
theorem integral_KF_zero (hp : Par L η) (hint : ∫ x, Hr L η α x = 0) {t : ℂ} (ht : |t.im| < 1 / 2)
    (hX : Xi t = 0) : ∫ u : ℝ, KF L η α (Real.exp u) * Complex.exp (I * t * u) = 0 := by
  rw [integral_KF, mellin_KF_zero hp hint ht hX]

end Kaiser

#print axioms Kaiser.mellin_KF_eq
#print axioms Kaiser.mellin_KF_zero
#print axioms Kaiser.integral_KF_zero

#print axioms Kaiser.KF_eq
#print axioms Kaiser.KF_top
#print axioms Kaiser.KF_bot
