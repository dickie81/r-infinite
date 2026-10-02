import Mathlib
import StructureD

/-! # Smoothing probes without leaving `[−a, a]` (analytic input for Theorem C)

Translation and dilation are continuous in `L²`; box averages converge to the identity in `L²` and
contract the archimedean energy; dilation towards `1` converges in archimedean energy. -/

open Real Filter Topology MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## Dilation is continuous in `L²` -/

theorem memLp_dil {g : ℝ → ℝ} (hg : MemLp g 2 volume) {l : ℝ} (hl : l ≠ 0) :
    MemLp (fun x => g (x / l)) 2 volume := by
  have hm : AEStronglyMeasurable (fun x => g (x / l)) volume := by
    have := hg.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) (inv_ne_zero hl))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [Function.comp, smul_eq_mul, div_eq_inv_mul]
  exact (memLp_two_iff_integrable_sq hm).2 (hg.integrable_sq.comp_div hl)

theorem normSq_dil (g : ℝ → ℝ) (l : ℝ) : normSq (fun x => g (x / l)) = |l| * normSq g := by
  unfold normSq
  rw [Measure.integral_comp_div (fun y => g y ^ 2) l, smul_eq_mul]

theorem tendsto_normSq_dil {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    Tendsto (fun l => normSq (fun x => g (x / l) - g x)) (𝓝 1) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨φ, hc, hs, hφ, happ⟩ := exists_cc_approx hg (show 0 < ε / 48 by positivity)
  obtain ⟨⟨R, hR, hsupp⟩, huc⟩ := cc_data hc hs
  set ε' := min 1 (ε / (96 * R))
  have hε' : 0 < ε' := lt_min one_pos (by positivity)
  obtain ⟨ρ, hρ, hmod⟩ := huc ε' hε'
  set η := min (1 / 2) (ρ / (4 * R))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hball : ∀ᶠ l in 𝓝 (1 : ℝ), |l - 1| < η := by
    have := Metric.ball_mem_nhds (1 : ℝ) hη
    filter_upwards [this] with l hl
    rwa [Metric.mem_ball, Real.dist_eq] at hl
  filter_upwards [hball] with l hl
  have hl1 : |l - 1| < 1 / 2 := lt_of_lt_of_le hl (min_le_left _ _)
  have hl2 : |l - 1| < ρ / (4 * R) := lt_of_lt_of_le hl (min_le_right _ _)
  have hlpos : 1 / 2 < l := by linarith [neg_abs_le (l - 1)]
  have hlt : l < 3 / 2 := by linarith [le_abs_self (l - 1)]
  have hl0 : l ≠ 0 := by linarith
  -- the continuous part
  have hφd : normSq (fun x => φ (x / l) - φ x) ≤ ε' * (2 * (2 * R)) := by
    refine normSq_le_box (F := fun x => φ (x / l) - φ x) ((memLp_dil hφ hl0).sub hφ) (by linarith) fun x => ?_
    by_cases hx : x ∈ Icc (-(2 * R)) (2 * R)
    · rw [indicator_of_mem hx]
      have hxR : |x| ≤ 2 * R := abs_le.2 hx
      have hd : |x / l - x| < ρ := by
        have e : x / l - x = x * (1 - l) / l := by field_simp
        rw [e, abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < l), abs_sub_comm,
          div_lt_iff₀ (by linarith)]
        calc |x| * |l - 1| ≤ 2 * R * |l - 1| := mul_le_mul_of_nonneg_right hxR (abs_nonneg _)
          _ < 2 * R * (ρ / (4 * R)) := mul_lt_mul_of_pos_left hl2 (by linarith)
          _ = ρ / 2 := by field_simp; norm_num
          _ ≤ ρ * l := by nlinarith
      have h1 := hmod _ _ hd
      have h2 : |φ (x / l) - φ x| ^ 2 ≤ ε' ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1.le 2
      have h3 : ε' ^ 2 ≤ ε' := by nlinarith [min_le_left 1 (ε / (96 * R))]
      rw [sq_abs] at h2; linarith
    · rw [indicator_of_notMem hx]
      have h1 : 2 * R < |x| := by
        by_contra hc'; push Not at hc'; exact hx (abs_le.1 hc')
      have h2 : R < |x / l| := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < l), lt_div_iff₀ (by linarith)]
        nlinarith
      rw [hsupp x (by linarith), hsupp _ h2]; simp
  have hm1 : MemLp (fun x => g (x / l) - φ (x / l)) 2 volume :=
    (memLp_dil hg hl0).sub (memLp_dil hφ hl0)
  have hm2 : MemLp (fun x => φ (x / l) - φ x) 2 volume := (memLp_dil hφ hl0).sub hφ
  have hm3 : MemLp (fun x => φ x - g x) 2 volume := hφ.sub hg
  have hsplit := normSq_add3_le hm1 hm2 hm3
  have e : (fun x => (g (x / l) - φ (x / l)) + (φ (x / l) - φ x) + (φ x - g x))
      = fun x => g (x / l) - g x := by funext x; ring
  rw [e] at hsplit
  have e1 : normSq (fun x => g (x / l) - φ (x / l)) = |l| * normSq (fun x => g x - φ x) :=
    normSq_dil (fun x => g x - φ x) l
  rw [e1, normSq_neg_sub g φ, abs_of_pos (by linarith : (0 : ℝ) < l)] at hsplit
  have hR' : ε' * (2 * (2 * R)) ≤ ε / 24 := by
    have := min_le_right 1 (ε / (96 * R))
    calc ε' * (2 * (2 * R)) ≤ ε / (96 * R) * (2 * (2 * R)) :=
          mul_le_mul_of_nonneg_right this (by linarith)
      _ = ε / 24 := by field_simp; ring
  have hN := normSq_nonneg (fun x => g x - φ x)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (normSq_nonneg _)]
  nlinarith

/-! ## Box averages -/

/-- The box average `Av δ g (x) = δ⁻¹ ∫_{−δ/2}^{δ/2} g(x + s) ds`. -/
def Av (δ : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ := δ⁻¹ * ∫ s in (-(δ / 2))..(δ / 2), g (x + s)

theorem memLp_shift_left {g : ℝ → ℝ} (hg : MemLp g 2 volume) (x : ℝ) :
    MemLp (fun s => g (x + s)) 2 volume :=
  hg.comp_measurePreserving (measurePreserving_add_left volume x)

/-- Jensen's inequality on an interval. -/
theorem sq_avg_le {φ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h1 : IntervalIntegrable φ volume (-(δ / 2)) (δ / 2))
    (h2 : IntervalIntegrable (fun s => φ s ^ 2) volume (-(δ / 2)) (δ / 2)) :
    (∫ s in (-(δ / 2))..(δ / 2), φ s) ^ 2 ≤ δ * ∫ s in (-(δ / 2))..(δ / 2), φ s ^ 2 := by
  set I := ∫ s in (-(δ / 2))..(δ / 2), φ s
  set J := ∫ s in (-(δ / 2))..(δ / 2), φ s ^ 2
  set c := I / δ
  have h0 : 0 ≤ ∫ s in (-(δ / 2))..(δ / 2), (φ s - c) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have e : (∫ s in (-(δ / 2))..(δ / 2), (φ s - c) ^ 2) = J - 2 * c * I + c ^ 2 * δ := by
    have hpt : ∀ s, (φ s - c) ^ 2 = φ s ^ 2 - (2 * c) * φ s + c ^ 2 := fun s => by ring
    simp only [hpt]
    rw [intervalIntegral.integral_add (h2.sub (h1.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub h2 (h1.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [e] at h0
  have e2 : J - 2 * c * I + c ^ 2 * δ = J - I ^ 2 / δ := by simp only [c]; field_simp; ring
  rw [e2, sub_nonneg, div_le_iff₀ hδ] at h0
  linarith

/-- **Averaging over shifts, in `L²`.** For measurable `G ∈ L²`, if every
`‖G(· + s) − cG‖² ≤ B` for `|s| ≤ δ/2`, then `‖δ⁻¹∫(G(· + s) − cG) ds‖² ≤ B`. -/
theorem normSq_avg_le {G : ℝ → ℝ} (hGm : Measurable G) (hG : MemLp G 2 volume) (c : ℝ)
    {δ B : ℝ} (hδ : 0 < δ)
    (hb : ∀ s, |s| ≤ δ / 2 → normSq (fun x => G (x + s) - c * G x) ≤ B) :
    normSq (fun x => δ⁻¹ * ∫ s in (-(δ / 2))..(δ / 2), (G (x + s) - c * G x)) ≤ B := by
  set ν := volume.restrict (Ioc (-(δ / 2)) (δ / 2))
  set F : ℝ → ℝ → ℝ := fun x s => (G (x + s) - c * G x) ^ 2
  have hsec : ∀ s, MemLp (fun x => G (x + s) - c * G x) 2 volume :=
    fun s => (memLp_shift hG s).sub (hG.const_mul c)
  have hFm : Measurable (Function.uncurry F) := by
    have h1 : Measurable fun p : ℝ × ℝ => G (p.1 + p.2) := hGm.comp (measurable_fst.add measurable_snd)
    have h2 : Measurable fun p : ℝ × ℝ => G p.1 := hGm.comp measurable_fst
    exact ((h1.sub (h2.const_mul c)).pow_const 2)
  have hB0 : 0 ≤ B := (normSq_nonneg _).trans (hb 0 (by rw [abs_zero]; linarith))
  have hint : Integrable (Function.uncurry F) (volume.prod ν) := by
    refine (integrable_prod_iff' hFm.aestronglyMeasurable).2 ⟨Eventually.of_forall fun s =>
      (hsec s).integrable_sq, ?_⟩
    have hmeas : AEStronglyMeasurable (fun s => ∫ x, ‖Function.uncurry F (x, s)‖) ν :=
      (hFm.norm.stronglyMeasurable.integral_prod_left' (μ := volume)).aestronglyMeasurable
    refine Integrable.mono' (integrable_const B) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    have hs' : |s| ≤ δ / 2 := abs_le.2 ⟨hs.1.le, hs.2⟩
    have e : (∫ x, ‖Function.uncurry F (x, s)‖) = normSq (fun x => G (x + s) - c * G x) := by
      unfold normSq; congr 1; funext x
      simp only [Function.uncurry, F, Real.norm_eq_abs, abs_pow, sq_abs]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e]
    exact hb s hs'
  have hνfin : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hδ2 : -(δ / 2) ≤ δ / 2 := by linarith
  -- pointwise Jensen
  have hpt : ∀ x, (δ⁻¹ * ∫ s in (-(δ / 2))..(δ / 2), (G (x + s) - c * G x)) ^ 2
      ≤ δ⁻¹ * ∫ s, F x s ∂ν := by
    intro x
    have hG1 := memLp_intervalIntegrable (memLp_shift_left hG x) (-(δ / 2)) (δ / 2)
    have hG2 : IntervalIntegrable (fun s => G (x + s) ^ 2) volume (-(δ / 2)) (δ / 2) :=
      (memLp_shift_left hG x).integrable_sq.intervalIntegrable
    have h1 : IntervalIntegrable (fun s => G (x + s) - c * G x) volume (-(δ / 2)) (δ / 2) :=
      hG1.sub intervalIntegrable_const
    have h2 : IntervalIntegrable (fun s => (G (x + s) - c * G x) ^ 2) volume (-(δ / 2)) (δ / 2) := by
      have := (hG2.sub (hG1.const_mul (2 * (c * G x)))).add
        (intervalIntegrable_const (c := (c * G x) ^ 2))
      exact this.congr fun s _ => by ring
    have hj := sq_avg_le hδ h1 h2
    have e : (∫ s, F x s ∂ν) = ∫ s in (-(δ / 2))..(δ / 2), (G (x + s) - c * G x) ^ 2 := by
      rw [intervalIntegral.integral_of_le hδ2]
    rw [e, mul_pow]
    have hinv : (δ⁻¹) ^ 2 * δ = δ⁻¹ := by field_simp
    calc δ⁻¹ ^ 2 * (∫ s in (-(δ / 2))..(δ / 2), (G (x + s) - c * G x)) ^ 2
        ≤ δ⁻¹ ^ 2 * (δ * ∫ s in (-(δ / 2))..(δ / 2), (G (x + s) - c * G x) ^ 2) :=
          mul_le_mul_of_nonneg_left hj (sq_nonneg _)
      _ = _ := by rw [← mul_assoc, hinv]
  have hR : Integrable (fun x => δ⁻¹ * ∫ s, F x s ∂ν) volume :=
    (hint.integral_prod_left).const_mul _
  have hle : normSq (fun x => δ⁻¹ * ∫ s in (-(δ / 2))..(δ / 2), (G (x + s) - c * G x))
      ≤ ∫ x, δ⁻¹ * ∫ s, F x s ∂ν :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hR
      (Eventually.of_forall hpt)
  have hswap : (∫ x, (∫ s, F x s ∂ν)) = ∫ s, (∫ x, F x s) ∂ν := integral_integral_swap hint
  have hin : (∫ s, (∫ x, F x s) ∂ν) ≤ ∫ s, B ∂ν := by
    refine integral_mono_ae (hint.integral_prod_right) (integrable_const B) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    exact hb s (abs_le.2 ⟨hs.1.le, hs.2⟩)
  have hconst : (∫ s, B ∂ν) = B * δ := by
    rw [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [integral_const_mul, hswap] at hle
  have : δ⁻¹ * (B * δ) = B := by field_simp
  calc _ ≤ δ⁻¹ * ∫ s, (∫ x, F x s) ∂ν := hle
    _ ≤ δ⁻¹ * (B * δ) := by rw [← hconst]; exact mul_le_mul_of_nonneg_left hin (by positivity)
    _ = B := this

theorem exists_meas_version {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    ∃ G, Measurable G ∧ MemLp G 2 volume ∧ g =ᵐ[volume] G :=
  ⟨hg.aestronglyMeasurable.mk g, hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
    hg.ae_eq hg.aestronglyMeasurable.ae_eq_mk, hg.aestronglyMeasurable.ae_eq_mk⟩

theorem shift_ae {g G : ℝ → ℝ} (h : g =ᵐ[volume] G) (x : ℝ) :
    (fun s => g (x + s)) =ᵐ[volume] fun s => G (x + s) :=
  (measurePreserving_add_left volume x).quasiMeasurePreserving.ae_eq_comp h

theorem shift_ae' {g G : ℝ → ℝ} (h : g =ᵐ[volume] G) (x : ℝ) :
    (fun s => g (s + x)) =ᵐ[volume] fun s => G (s + x) :=
  (measurePreserving_add_right volume x).quasiMeasurePreserving.ae_eq_comp h

theorem Av_congr {g G : ℝ → ℝ} (h : g =ᵐ[volume] G) (δ : ℝ) : Av δ g = Av δ G := by
  funext x; unfold Av; congr 1
  exact intervalIntegral.integral_congr_ae ((shift_ae h x).mono fun s hs _ => hs)

theorem Av_sub_eq {G : ℝ → ℝ} (hG : MemLp G 2 volume) {δ : ℝ} (hδ : 0 < δ) (c x : ℝ) :
    Av δ G x - c * G x = δ⁻¹ * ∫ s in (-(δ / 2))..(δ / 2), (G (x + s) - c * G x) := by
  unfold Av
  rw [intervalIntegral.integral_sub (memLp_intervalIntegrable (memLp_shift_left hG x) _ _)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
  field_simp; ring

/-- **Box averages contract `L²`.** -/
theorem normSq_Av_le {g : ℝ → ℝ} (hg : MemLp g 2 volume) {δ : ℝ} (hδ : 0 < δ) :
    normSq (Av δ g) ≤ normSq g := by
  obtain ⟨G, hGm, hG, hgG⟩ := exists_meas_version hg
  rw [Av_congr hgG, normSq_congr_ae hgG]
  have := normSq_avg_le hGm hG 0 hδ (B := normSq G) fun s _ => by
    simp only [zero_mul, sub_zero]; exact (normSq_shift G s).le
  have e : Av δ G = fun x => δ⁻¹ * ∫ s in (-(δ / 2))..(δ / 2), (G (x + s) - 0 * G x) := by
    funext x; rw [← Av_sub_eq hG hδ 0 x]; ring
  rw [e]; exact this

/-- **Box averages approximate the identity**, quantitatively. -/
theorem normSq_Av_sub_le {g : ℝ → ℝ} (hg : MemLp g 2 volume) {δ η : ℝ} (hδ : 0 < δ)
    (hb : ∀ s, |s| ≤ δ / 2 → normSq (fun t => g (t + s) - g t) ≤ η) :
    normSq (fun x => Av δ g x - g x) ≤ η := by
  obtain ⟨G, hGm, hG, hgG⟩ := exists_meas_version hg
  have e1 : normSq (fun x => Av δ g x - g x) = normSq (fun x => Av δ G x - G x) := by
    rw [Av_congr hgG]; exact normSq_congr_ae (hgG.mono fun x hx => by simp only [hx])
  have e2 : ∀ s, normSq (fun t => g (t + s) - g t) = normSq (fun t => G (t + s) - G t) := by
    intro s
    exact normSq_congr_ae ((shift_ae' hgG s).mp (hgG.mono fun t h1 h2 => by simp only [h1, h2]))
  rw [e1]
  have := normSq_avg_le hGm hG 1 hδ (B := η) fun s hs => by
    simp only [one_mul]; rw [← e2]; exact hb s hs
  have e : (fun x => Av δ G x - G x)
      = fun x => δ⁻¹ * ∫ s in (-(δ / 2))..(δ / 2), (G (x + s) - 1 * G x) := by
    funext x; rw [← Av_sub_eq hG hδ 1 x, one_mul]
  rw [e]; exact this

theorem tendsto_Av {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    Tendsto (fun δ => normSq (fun x => Av δ g x - g x)) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := Metric.tendsto_nhds.1 (tendsto_normSq_shift hg) (ε / 2) (by positivity)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 h
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < ρ := by
    have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < ρ := nhdsWithin_le_nhds (Iio_mem_nhds hρ)
    exact h1.and h2
  filter_upwards [hev] with δ ⟨hδ, hδρ⟩
  have hb : ∀ s, |s| ≤ δ / 2 → normSq (fun t => g (t + s) - g t) ≤ ε / 2 := by
    intro s hs
    have := hball (y := s) (by rw [Real.dist_eq, sub_zero]; linarith)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (normSq_nonneg _)] at this
    exact this.le
  have := normSq_Av_sub_le hg hδ hb
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (normSq_nonneg _)]
  linarith

/-! ## Shape of box averages -/

theorem Av_prim {g : ℝ → ℝ} (hg : MemLp g 2 volume) (δ x : ℝ) :
    Av δ g x = δ⁻¹ * ((∫ t in (0 : ℝ)..(x + δ / 2), g t) - ∫ t in (0 : ℝ)..(x - δ / 2), g t) := by
  unfold Av
  rw [intervalIntegral.integral_comp_add_left (fun t => g t) x,
    intervalIntegral.integral_interval_sub_left (memLp_intervalIntegrable hg _ _)
      (memLp_intervalIntegrable hg _ _)]
  congr 2

theorem Av_continuous {g : ℝ → ℝ} (hg : MemLp g 2 volume) (δ : ℝ) : Continuous (Av δ g) := by
  have hP := intervalIntegral.continuous_primitive (fun a b => memLp_intervalIntegrable hg a b) 0
  have : Av δ g = fun x => δ⁻¹ * ((∫ t in (0 : ℝ)..(x + δ / 2), g t) - ∫ t in (0 : ℝ)..(x - δ / 2), g t) :=
    funext (Av_prim hg δ)
  rw [this]
  exact continuous_const.mul ((hP.comp (continuous_id.add continuous_const)).sub
    (hP.comp (continuous_id.sub continuous_const)))

theorem Av_hasDerivAt {g : ℝ → ℝ} (hg : MemLp g 2 volume) (hc : Continuous g) (δ x : ℝ) :
    HasDerivAt (Av δ g) (δ⁻¹ * (g (x + δ / 2) - g (x - δ / 2))) x := by
  have : Av δ g = fun x => δ⁻¹ * ((∫ t in (0 : ℝ)..(x + δ / 2), g t) - ∫ t in (0 : ℝ)..(x - δ / 2), g t) :=
    funext (Av_prim hg δ)
  rw [this]
  have h1 := ((hc.integral_hasStrictDerivAt 0 (x + δ / 2)).hasDerivAt).comp_add_const x (δ / 2)
  have h2 := ((hc.integral_hasStrictDerivAt 0 (x - δ / 2)).hasDerivAt).comp_sub_const x (δ / 2)
  exact (h1.sub h2).const_mul δ⁻¹

theorem Av_even {g : ℝ → ℝ} (heven : ∀ t, g (-t) = g t) (δ x : ℝ) : Av δ g (-x) = Av δ g x := by
  unfold Av; congr 1
  have : (fun s => g (-x + s)) = fun s => g (x + -s) := by
    funext s; rw [← heven]; congr 1; ring
  rw [this, intervalIntegral.integral_comp_neg (fun s => g (x + s)), neg_neg]

theorem Av_supp {g : ℝ → ℝ} {r δ : ℝ} (hδ : 0 < δ) (hs : ∀ t, r < |t| → g t = 0) (x : ℝ)
    (hx : r + δ / 2 < |x|) : Av δ g x = 0 := by
  unfold Av
  have : (∫ s in (-(δ / 2))..(δ / 2), g (x + s)) = ∫ s in (-(δ / 2))..(δ / 2), (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun s hsI => ?_
    rw [uIcc_of_le (by linarith)] at hsI
    refine hs _ ?_
    have := abs_add_le (x + s) (-s)
    rw [add_neg_cancel_right, abs_neg] at this
    have : |s| ≤ δ / 2 := abs_le.2 ⟨hsI.1, hsI.2⟩
    linarith
  rw [this, intervalIntegral.integral_zero, mul_zero]

theorem Av_shift (δ : ℝ) (g : ℝ → ℝ) (t u : ℝ) : Av δ g (t + u) = Av δ (fun y => g (y + u)) t := by
  unfold Av; congr 1
  exact intervalIntegral.integral_congr fun s _ => by simp only; ring_nf

theorem Av_sub {g h : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) (δ x : ℝ) :
    Av δ (fun t => g t - h t) x = Av δ g x - Av δ h x := by
  unfold Av
  rw [← mul_sub, intervalIntegral.integral_sub (memLp_intervalIntegrable (memLp_shift_left hg x) _ _)
    (memLp_intervalIntegrable (memLp_shift_left hh x) _ _)]

/-- **Box averages contract the archimedean integrand.** -/
theorem archIntegrand_Av_le {g : ℝ → ℝ} (hg : MemLp g 2 volume) (hA : MemLp (Av δ g) 2 volume)
    (hδ : 0 < δ) {u : ℝ} (hu : 0 < u) : archIntegrand (Av δ g) u ≤ archIntegrand g u := by
  rw [archIntegrand_eq hA, archIntegrand_eq hg]
  have e : (fun t => Av δ g t - Av δ g (t + u)) = Av δ (fun t => g t - g (t + u)) := by
    funext t; rw [Av_shift, Av_sub hg (memLp_shift hg u)]
  rw [e]
  have hm : MemLp (fun t => g t - g (t + u)) 2 volume := hg.sub (memLp_shift hg u)
  have := normSq_Av_le hm hδ
  have hk := (kerK_pos hu).le
  nlinarith

theorem memLp_Av {g : ℝ → ℝ} (hg : MemLp g 2 volume) {r δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ t, r < |t| → g t = 0) : MemLp (Av δ g) 2 volume :=
  (Av_continuous hg δ).memLp_of_hasCompactSupport
    (hasCompactSupport_of_supp (a := r + δ / 2) (Av_supp hδ hs))

/-- **A box average of a probe is a probe**, on a support larger by `δ/2`. -/
theorem probe_Av {g : ℝ → ℝ} {r δ : ℝ} (hp : Probe r g) (hδ : 0 < δ) : Probe (r + δ / 2) (Av δ g) := by
  have hA := memLp_Av hp.memL2 hδ hp.supp
  refine ⟨Av_even hp.even δ, Av_supp hδ hp.supp, hA, ?_⟩
  refine Integrable.mono' hp.arch (measurable_archIntegrand hA).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg hA hu)]
  exact archIntegrand_Av_le hp.memL2 hA hδ hu

/-! ## Box averages converge in archimedean energy -/

theorem Av_sub_self_shift {g : ℝ → ℝ} (hg : MemLp g 2 volume) (δ u : ℝ) :
    (fun t => (Av δ g t - g t) - (Av δ g (t + u) - g (t + u)))
      = fun t => Av δ (fun y => g y - g (y + u)) t - (g t - g (t + u)) := by
  funext t; rw [Av_sub hg (memLp_shift hg u), ← Av_shift]; ring

theorem tendsto_archE_Av {r : ℝ} {g : ℝ → ℝ} (hp : Probe r g) :
    Tendsto (fun δ => archE (fun x => Av δ g x - g x)) (𝓝[>] 0) (𝓝 0) := by
  have hg := hp.memL2
  have hmem : ∀ δ, 0 < δ → MemLp (fun x => Av δ g x - g x) 2 volume :=
    fun δ hδ => (memLp_Av hg hδ hp.supp).sub hg
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have key : Tendsto (fun δ => ∫ u in Ioi (0 : ℝ), archIntegrand (fun x => Av δ g x - g x) u)
      (𝓝[>] 0) (𝓝 (∫ u in Ioi (0 : ℝ), (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => 4 * archIntegrand g u) ?_ ?_
      (hp.arch.const_mul 4) ?_
    · filter_upwards [hpos] with δ hδ
      exact (measurable_archIntegrand (hmem δ hδ)).aestronglyMeasurable
    · filter_upwards [hpos] with δ hδ
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 < u := hu
      rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg (hmem δ hδ) hu0),
        archIntegrand_eq (hmem δ hδ), archIntegrand_eq hg, Av_sub_self_shift hg]
      have hm : MemLp (fun y => g y - g (y + u)) 2 volume := hg.sub (memLp_shift hg u)
      have h1 := normSq_sub_le (memLp_Av hm hδ (r := r + u) (fun t ht => by
        rw [hp.supp t (by linarith [abs_nonneg u]), hp.supp (t + u) (by
          have := abs_add_le (t + u) (-u); rw [add_neg_cancel_right, abs_neg] at this
          have : |u| = u := abs_of_pos hu0; linarith)]; ring)) hm
      have h2 := normSq_Av_le hm hδ
      have hk := (kerK_pos hu0).le
      nlinarith
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 < u := hu
      have hm : MemLp (fun y => g y - g (y + u)) 2 volume := hg.sub (memLp_shift hg u)
      have ht := (tendsto_Av hm).mul_const (kerK u / 2)
      rw [zero_mul] at ht
      refine ht.congr' ?_
      filter_upwards [hpos] with δ hδ
      rw [archIntegrand_eq (hmem δ hδ), Av_sub_self_shift hg]; ring
  rw [integral_zero] at key
  exact key

/-! ## The kernel `kerK` -/

theorem kerK_eq' {x : ℝ} (hx : 0 < x) :
    kerK x = 2 / (Real.exp (x / 2) - Real.exp (-(3 * x / 2))) := by
  unfold kerK
  have hs : Real.sinh x = Real.exp (x / 2) * (Real.exp (x / 2) - Real.exp (-(3 * x / 2))) / 2 := by
    rw [Real.sinh_eq, mul_sub, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hD : 0 < Real.exp (x / 2) - Real.exp (-(3 * x / 2)) := by
    rw [sub_pos]; exact Real.exp_lt_exp.2 (by linarith)
  rw [hs]; field_simp

theorem kerK_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : kerK y ≤ kerK x := by
  rw [kerK_eq' hx, kerK_eq' (lt_of_lt_of_le hx hxy)]
  have hD : 0 < Real.exp (x / 2) - Real.exp (-(3 * x / 2)) := by
    rw [sub_pos]; exact Real.exp_lt_exp.2 (by linarith)
  apply div_le_div_of_nonneg_left (by norm_num) hD
  have h1 : Real.exp (x / 2) ≤ Real.exp (y / 2) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-(3 * y / 2)) ≤ Real.exp (-(3 * x / 2)) := Real.exp_le_exp.2 (by linarith)
  linarith

theorem kerK_half_le {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) : kerK (v / 2) ≤ 3 * kerK v := by
  unfold kerK
  have hs2 : 0 < Real.sinh (v / 2) := Real.sinh_pos_iff.2 (by linarith)
  have hsv : Real.sinh v = 2 * Real.sinh (v / 2) * Real.cosh (v / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  have hc : Real.cosh (v / 2) ≤ 3 / 2 := by
    have h1 : Real.cosh (v / 2) ≤ Real.cosh (1 / 2) :=
      Real.cosh_le_cosh.2 (by rw [abs_of_pos (by linarith), abs_of_pos (by norm_num)]; linarith)
    have h2 : Real.exp (1 / 2) < 2 := by
      have e : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
      have := Real.exp_one_lt_d9
      nlinarith [Real.exp_pos (1 / 2)]
    have h3 : Real.exp (-(1 / 2)) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
    have h4 : Real.cosh (1 / 2) ≤ 3 / 2 := by rw [Real.cosh_eq]; linarith
    linarith
  have hc0 : 0 < Real.cosh (v / 2) := Real.cosh_pos _
  have he : Real.exp (v / 2 / 2) ≤ Real.exp (v / 2) := Real.exp_le_exp.2 (by linarith)
  rw [hsv, div_le_iff₀ hs2]
  rw [show 3 * (Real.exp (v / 2) / (2 * Real.sinh (v / 2) * Real.cosh (v / 2))) * Real.sinh (v / 2)
      = 3 * Real.exp (v / 2) / (2 * Real.cosh (v / 2)) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.exp_pos (v / 2 / 2)]

theorem kerK_far {v : ℝ} (hv : 1 ≤ v) : kerK (v / 2) ≤ 32 * Real.exp (-(1 / 8) * v) := by
  have h := u_archK_le (u := v / 2) (by linarith)
  unfold kerK
  have hk : 0 ≤ Real.exp (v / 2 / 2) / Real.sinh (v / 2) :=
    (div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 (by linarith))).le
  have e : Real.exp (-(1 / 4) * (v / 2)) = Real.exp (-(1 / 8) * v) := by ring_nf
  rw [e] at h
  nlinarith [Real.exp_pos (-(1 / 8) * v)]


theorem continuousAt_kerK {x : ℝ} (hx : 0 < x) : ContinuousAt kerK x := by
  unfold kerK
  exact (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousAt.div
    Real.continuous_sinh.continuousAt (Real.sinh_pos_iff.2 hx).ne'

/-! ## The shift profile `F_g(v) = ‖g − g(· + v)‖²` -/

def Fsh (g : ℝ → ℝ) (v : ℝ) : ℝ := normSq (fun t => g t - g (t + v))

theorem Fsh_le {g : ℝ → ℝ} (hg : MemLp g 2 volume) (v : ℝ) : Fsh g v ≤ 4 * normSq g := by
  have := normSq_sub_le hg (memLp_shift hg v)
  rw [normSq_shift] at this; unfold Fsh; linarith

theorem Fsh_nonneg (g : ℝ → ℝ) (v : ℝ) : 0 ≤ Fsh g v := normSq_nonneg _

theorem Fsh_continuous {g : ℝ → ℝ} (hg : MemLp g 2 volume) : Continuous (Fsh g) := by
  have hF : Fsh g = fun v => 2 * (autocorr g 0 - autocorr g v) := funext fun v => normSq_sub_shift hg v
  rw [hF]; exact continuous_const.mul (continuous_const.sub (continuous_autocorr hg))

/-! ## Dilated probes -/

theorem archIntegrand_dil {g : ℝ → ℝ} (hg : MemLp g 2 volume) {l : ℝ} (hl : 0 < l) (u : ℝ) :
    archIntegrand (fun x => g (x / l)) u = l * Fsh g (u / l) / 2 * kerK u := by
  rw [archIntegrand_eq (memLp_dil hg hl.ne')]
  have e : (fun t => g (t / l) - g ((t + u) / l)) = fun t => g (t / l) - g (t / l + u / l) := by
    funext t; rw [add_div]
  have := normSq_dil (fun y => g y - g (y + u / l)) l
  rw [e, this, abs_of_pos hl]; rfl

/-- `F_g(v)·K(v/2)` is integrable for a probe `g`. -/
theorem integrableOn_Fsh_half {r : ℝ} {g : ℝ → ℝ} (hp : Probe r g) :
    IntegrableOn (fun v => Fsh g v * kerK (v / 2)) (Ioi 0) := by
  have hg := hp.memL2
  have m1 : Measurable (Fsh g) := (Fsh_continuous hg).measurable
  have m2 : Measurable (fun v : ℝ => kerK (v / 2)) := kerK_measurable.comp (measurable_id.div_const 2)
  have hmeas : AEStronglyMeasurable (fun v => Fsh g v * kerK (v / 2)) (volume.restrict (Ioi 0)) :=
    (m1.mul m2).aestronglyMeasurable
  have hA : ∀ v, 0 < v → Fsh g v * kerK v = 2 * archIntegrand g v := by
    intro v _; rw [archIntegrand_eq hg]; unfold Fsh; ring
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' ((hp.arch.mono_set Ioc_subset_Ioi_self).const_mul 6)
      (hmeas.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl))
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => ?_))
    have hk := kerK_half_le hv.1 hv.2
    have hF := Fsh_nonneg g v
    have hk0 : 0 ≤ kerK (v / 2) := (kerK_pos (by linarith [hv.1])).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hF hk0)]
    have := hA v hv.1
    nlinarith [mul_le_mul_of_nonneg_left hk hF]
  · refine Integrable.mono'
      ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 8)).const_mul (4 * normSq g * 32))
      (hmeas.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl))
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_))
    have hv1 : 1 ≤ v := le_of_lt hv
    have hk := kerK_far hv1
    have hF := Fsh_le hg v
    have hF0 := Fsh_nonneg g v
    have hk0 : 0 ≤ kerK (v / 2) := (kerK_pos (by linarith)).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hF0 hk0)]
    have hN := normSq_nonneg g
    calc Fsh g v * kerK (v / 2) ≤ (4 * normSq g) * (32 * Real.exp (-(1 / 8) * v)) :=
          mul_le_mul hF hk hk0 (by linarith)
      _ = 4 * normSq g * 32 * Real.exp (-(1 / 8) * v) := by ring

/-- **A dilation of a probe is a probe**, for `½ ≤ l ≤ 1`. -/
theorem probe_dil {r : ℝ} (hr : 0 ≤ r) {g : ℝ → ℝ} (hp : Probe r g) {l : ℝ} (hl : 1 / 2 ≤ l)
    (hl1 : l ≤ 1) : Probe r (fun x => g (x / l)) := by
  have hl0 : 0 < l := by linarith
  have hg := hp.memL2
  refine ⟨fun u => by rw [neg_div, hp.even], fun u hu => hp.supp _ ?_, memLp_dil hg hl0.ne', ?_⟩
  · rw [abs_div, abs_of_pos hl0, lt_div_iff₀ hl0]; nlinarith
  · have hK := integrableOn_Fsh_half hp
    have hiff := integrableOn_Ioi_comp_mul_left_iff
      (fun u => l * Fsh g (u / l) / 2 * kerK u) 0 hl0
    rw [mul_zero] at hiff
    have hfun : archIntegrand (fun x => g (x / l)) = fun u => l * Fsh g (u / l) / 2 * kerK u :=
      funext (archIntegrand_dil hg hl0)
    rw [hfun, ← hiff]
    refine Integrable.mono' (hK.const_mul (l / 2)) ?_
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_))
    · have m1 : Measurable (fun v => Fsh g (l * v / l)) :=
        (Fsh_continuous hg).measurable.comp ((measurable_const_mul l).div_const l)
      exact (((m1.const_mul l).div_const 2).mul
        (kerK_measurable.comp (measurable_const_mul l))).aestronglyMeasurable
    · have hv0 : 0 < v := hv
      rw [mul_div_cancel_left₀ v hl0.ne']
      have hk := kerK_anti (x := v / 2) (y := l * v) (by linarith) (by nlinarith)
      have hk0 : 0 ≤ kerK (l * v) := (kerK_pos (by positivity)).le
      have hF0 := Fsh_nonneg g v
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc l * Fsh g v / 2 * kerK (l * v) ≤ l * Fsh g v / 2 * kerK (v / 2) :=
            mul_le_mul_of_nonneg_left hk (by positivity)
        _ = l / 2 * (Fsh g v * kerK (v / 2)) := by ring

/-! ## A dominated-convergence lemma with moving dominators (Pratt/Scheffé) -/

theorem tendsto_integral_pratt {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μ : Measure ℝ} {Φ B : ι → ℝ → ℝ} {A : ℝ → ℝ}
    (hA : Integrable A μ) (hA0 : ∀ᵐ x ∂μ, 0 ≤ A x)
    (hB : ∀ᶠ i in l, Integrable (B i) μ) (hB0 : ∀ᶠ i in l, ∀ᵐ x ∂μ, 0 ≤ B i x)
    (hΦ : ∀ᶠ i in l, Integrable (Φ i) μ) (hΦ0 : ∀ᶠ i in l, ∀ᵐ x ∂μ, 0 ≤ Φ i x)
    (hΦB : ∀ᶠ i in l, ∀ᵐ x ∂μ, Φ i x ≤ 2 * B i x + 2 * A x)
    (hΦlim : ∀ᵐ x ∂μ, Tendsto (fun i => Φ i x) l (𝓝 0))
    (hBlim : ∀ᵐ x ∂μ, Tendsto (fun i => B i x) l (𝓝 (A x)))
    (hint : Tendsto (fun i => ∫ x, B i x ∂μ) l (𝓝 (∫ x, A x ∂μ))) :
    Tendsto (fun i => ∫ x, Φ i x ∂μ) l (𝓝 0) := by
  set m : ι → ℝ → ℝ := fun i x => min (Φ i x) (4 * A x)
  set p : ι → ℝ → ℝ := fun i x => max (A x - B i x) 0
  have hm_int : ∀ᶠ i in l, Integrable (m i) μ := by
    filter_upwards [hΦ, hΦ0] with i hi hi0
    refine Integrable.mono' (hA.const_mul 4) (hi.aestronglyMeasurable.inf
      (hA.aestronglyMeasurable.const_mul 4)) ?_
    filter_upwards [hi0, hA0] with x hx hax
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx (by linarith))]
    exact min_le_right _ _
  have hp_int : ∀ᶠ i in l, Integrable (p i) μ := by
    filter_upwards [hB, hB0] with i hi hi0
    refine Integrable.mono' hA ((hA.aestronglyMeasurable.sub hi.aestronglyMeasurable).sup
      aestronglyMeasurable_const) ?_
    filter_upwards [hi0, hA0] with x hx hax
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) hax
  have hm_lim : Tendsto (fun i => ∫ x, m i x ∂μ) l (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := l) (fun x => 4 * A x)
      (F := m) (f := fun _ => 0) (hm_int.mono fun i hi => hi.aestronglyMeasurable) ?_
      (hA.const_mul 4) ?_
    · simpa using this
    · filter_upwards [hΦ0] with i hi0
      filter_upwards [hi0, hA0] with x hx hax
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx (by linarith))]
      exact min_le_right _ _
    · filter_upwards [hΦlim, hA0] with x hx hax
      have := hx.min (tendsto_const_nhds (x := 4 * A x))
      rwa [min_eq_left (by linarith)] at this
  have hp_lim : Tendsto (fun i => ∫ x, p i x ∂μ) l (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := l) A
      (F := p) (f := fun _ => 0) (hp_int.mono fun i hi => hi.aestronglyMeasurable) ?_ hA ?_
    · simpa using this
    · filter_upwards [hB0] with i hi0
      filter_upwards [hi0, hA0] with x hx hax
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith) hax
    · filter_upwards [hBlim] with x hx
      have := (tendsto_const_nhds (x := A x)).sub hx |>.max (tendsto_const_nhds (x := (0 : ℝ)))
      rwa [sub_self, max_self] at this
  have hU : Tendsto (fun i => (∫ x, m i x ∂μ) + 2 * ((∫ x, B i x ∂μ) - ∫ x, A x ∂μ)
      + 4 * ∫ x, p i x ∂μ) l (𝓝 0) := by
    have h2 : Tendsto (fun i => (∫ x, B i x ∂μ) - ∫ x, A x ∂μ) l (𝓝 0) := by
      have := hint.sub (tendsto_const_nhds (x := ∫ x, A x ∂μ)); rwa [sub_self] at this
    have := (hm_lim.add (h2.const_mul 2)).add (hp_lim.const_mul 4)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
  · filter_upwards [hΦ0] with i hi0
    exact integral_nonneg_of_ae hi0
  · filter_upwards [hΦ, hB, hm_int, hp_int, hΦB] with i hi hbi hmi hpi hΦBi
    have hsum : Integrable (fun x => m i x + 2 * (B i x - A x) + 4 * p i x) μ :=
      (hmi.add ((hbi.sub hA).const_mul 2)).add (hpi.const_mul 4)
    have hle : (∫ x, Φ i x ∂μ) ≤ ∫ x, (m i x + 2 * (B i x - A x) + 4 * p i x) ∂μ := by
      refine integral_mono_ae hi hsum ?_
      filter_upwards [hΦBi] with x hx
      simp only [m, p]
      rcases le_total (Φ i x) (4 * A x) with h | h
      · rw [min_eq_left h]
        have : 0 ≤ 2 * (B i x - A x) + 4 * max (A x - B i x) 0 := by
          rcases le_total (A x - B i x) 0 with h' | h'
          · rw [max_eq_right h']; linarith
          · rw [max_eq_left h']; linarith
        linarith
      · rw [min_eq_right h]
        have := le_max_right (A x - B i x) 0
        linarith
    have e1 : (∫ x, (m i x + 2 * (B i x - A x) + 4 * p i x) ∂μ)
        = (∫ x, (m i x + 2 * (B i x - A x)) ∂μ) + ∫ x, 4 * p i x ∂μ :=
      integral_add (hmi.add ((hbi.sub hA).const_mul 2)) (hpi.const_mul 4)
    have e2 : (∫ x, (m i x + 2 * (B i x - A x)) ∂μ) = (∫ x, m i x ∂μ) + ∫ x, 2 * (B i x - A x) ∂μ :=
      integral_add hmi ((hbi.sub hA).const_mul 2)
    have e3 : (∫ x, 2 * (B i x - A x) ∂μ) = 2 * ((∫ x, B i x ∂μ) - ∫ x, A x ∂μ) := by
      rw [integral_const_mul, integral_sub hbi hA]
    have e4 : (∫ x, 4 * p i x ∂μ) = 4 * ∫ x, p i x ∂μ := integral_const_mul _ _
    rw [e1, e2, e3, e4] at hle
    exact hle

/-! ## Dilation converges in archimedean energy -/

theorem archIntegrand_neg (g : ℝ → ℝ) (u : ℝ) :
    archIntegrand (fun t => -g t) u = archIntegrand g u := by
  have := archIntegrand_smul (-1) g u
  simp only [neg_one_mul, neg_one_sq, one_mul] at this; exact this

theorem archIntegrand_sub_le {g h : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    {u : ℝ} (hu : 0 < u) :
    archIntegrand (fun t => g t - h t) u ≤ 2 * archIntegrand g u + 2 * archIntegrand h u := by
  have := archIntegrand_add_le hg hh.neg hu (h := fun t => -h t)
  rw [archIntegrand_neg] at this
  simpa [sub_eq_add_neg] using this

theorem tendsto_archE_dil {r : ℝ} (hr : 0 ≤ r) {g : ℝ → ℝ} (hp : Probe r g) :
    Tendsto (fun l => archE (fun x => g (x / l) - g x)) (𝓝[<] 1) (𝓝 0) := by
  have hg := hp.memL2
  set μ := volume.restrict (Ioi (0 : ℝ))
  have hl : ∀ᶠ l in 𝓝[<] (1 : ℝ), 1 / 2 < l ∧ l < 1 := by
    have h1 : ∀ᶠ l in 𝓝[<] (1 : ℝ), l < 1 := self_mem_nhdsWithin
    have h2 : ∀ᶠ l in 𝓝[<] (1 : ℝ), 1 / 2 < l := nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num))
    exact h2.and h1
  have hpd : ∀ᶠ l in 𝓝[<] (1 : ℝ), Probe r (fun x => g (x / l)) :=
    hl.mono fun l h => probe_dil hr hp h.1.le h.2.le
  have hA : ∀ u, archIntegrand g u = Fsh g u / 2 * kerK u := fun u => by
    rw [archIntegrand_eq hg]; rfl
  unfold archE
  refine tendsto_integral_pratt (μ := μ) (A := archIntegrand g)
    (B := fun l => archIntegrand (fun x => g (x / l))) hp.arch
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu =>
      archIntegrand_nonneg hg hu))
    (hpd.mono fun l h => h.arch)
    (hpd.mono fun l h => (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun u hu => archIntegrand_nonneg h.memL2 hu))
    (hpd.mono fun l h => (probe_add_sub h hp).2.arch)
    (hpd.mono fun l h => (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun u hu => archIntegrand_nonneg (h.memL2.sub hg) hu))
    (hpd.mono fun l h => (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun u hu => archIntegrand_sub_le h.memL2 hg hu)) ?_ ?_ ?_
  · -- pointwise: the difference energy density tends to 0
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 < u := hu
    have hN := (tendsto_normSq_dil hg).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    have hup : Tendsto (fun l => 4 * normSq (fun x => g (x / l) - g x) / 2 * kerK u) (𝓝[<] 1)
        (𝓝 0) := by
      have := (hN.const_mul 4).div_const 2 |>.mul_const (kerK u); simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hpd] with l h
      exact archIntegrand_nonneg (h.memL2.sub hg) hu0
    · filter_upwards [hpd] with l h
      have hm : MemLp (fun x => g (x / l) - g x) 2 volume := h.memL2.sub hg
      rw [archIntegrand_eq hm]
      have := normSq_sub_le hm (memLp_shift hm u)
      rw [normSq_shift (fun x => g (x / l) - g x) u] at this
      have hk := (kerK_pos hu0).le
      nlinarith
  · -- pointwise: the dilated energy density tends to the original one
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hc : ContinuousAt (fun l : ℝ => l * Fsh g (u / l) / 2 * kerK u) 1 := by
      have h1 : ContinuousAt (fun l : ℝ => Fsh g (u / l)) 1 :=
        (Fsh_continuous hg).continuousAt.comp (continuousAt_const.div continuousAt_id one_ne_zero)
      exact ((continuousAt_id.mul h1).div_const 2).mul continuousAt_const
    have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simp only [one_mul, div_one] at ht
    rw [hA u]
    refine ht.congr' ?_
    filter_upwards [hl] with l h
    rw [archIntegrand_dil hg (by linarith)]
  · -- the total dilated energy converges
    have hsub : ∀ l, 0 < l → (∫ u in Ioi (0 : ℝ), archIntegrand (fun x => g (x / l)) u)
        = l ^ 2 * ∫ v in Ioi (0 : ℝ), Fsh g v / 2 * kerK (l * v) := by
      intro l hl0
      have e1 : (fun u => archIntegrand (fun x => g (x / l)) u)
          = fun u => l * Fsh g (u / l) / 2 * kerK u := funext (archIntegrand_dil hg hl0)
      rw [e1]
      have := integral_comp_mul_left_Ioi (fun u => l * Fsh g (u / l) / 2 * kerK u) 0 hl0
      rw [mul_zero] at this
      have h2 : (∫ x in Ioi (0 : ℝ), l * Fsh g (x / l) / 2 * kerK x)
          = l * ∫ x in Ioi (0 : ℝ), l * Fsh g (l * x / l) / 2 * kerK (l * x) := by
        rw [this, smul_eq_mul]; field_simp
      rw [h2, ← integral_const_mul, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
      rw [mul_div_cancel_left₀ v hl0.ne']; ring
    have hdct : Tendsto (fun l => ∫ v in Ioi (0 : ℝ), Fsh g v / 2 * kerK (l * v)) (𝓝[<] 1)
        (𝓝 (∫ v in Ioi (0 : ℝ), Fsh g v / 2 * kerK v)) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun v => Fsh g v / 2 * kerK (v / 2)) ?_ ?_ ((integrableOn_Fsh_half hp).div_const 2 |>.congr
          (Eventually.of_forall fun v => by simp only; ring)) ?_
      · exact Eventually.of_forall fun l => ((((Fsh_continuous hg).measurable.div_const 2).mul
          (kerK_measurable.comp (measurable_const_mul l)))).aestronglyMeasurable
      · filter_upwards [hl] with l h
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
        have hv0 : 0 < v := hv
        have hk := kerK_anti (x := v / 2) (y := l * v) (by linarith) (by nlinarith)
        have hk0 : 0 ≤ kerK (l * v) := (kerK_pos (by nlinarith)).le
        have hF := Fsh_nonneg g v
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left hk (by positivity)
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
        have hv0 : 0 < v := hv
        have hk : Tendsto (fun l => kerK (l * v)) (𝓝[<] 1) (𝓝 (kerK v)) := by
          have h1 : Tendsto (fun l : ℝ => l * v) (𝓝 1) (𝓝 v) := by
            have := (continuous_id.mul continuous_const).tendsto 1 (f := fun l : ℝ => l * v)
            simpa using this
          exact ((continuousAt_kerK hv0).tendsto.comp h1).mono_left nhdsWithin_le_nhds
        exact hk.const_mul _
    have hl2 : Tendsto (fun l : ℝ => l ^ 2) (𝓝[<] 1) (𝓝 1) := by
      have := ((continuous_pow 2).tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 1))
      simpa using this
    have := hl2.mul hdct
    rw [one_mul] at this
    have hAint : (∫ u in Ioi (0 : ℝ), archIntegrand g u) = ∫ v in Ioi (0 : ℝ), Fsh g v / 2 * kerK v :=
      setIntegral_congr_fun measurableSet_Ioi fun v _ => hA v
    rw [hAint]
    refine this.congr' ?_
    filter_upwards [hl] with l h
    rw [hsub l (by linarith)]

/-! ## Bookkeeping for the approximants -/

theorem archIntegrand_add3_le {g h k : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hk : MemLp k 2 volume) {u : ℝ} (hu : 0 < u) :
    archIntegrand (fun t => g t + h t + k t) u
      ≤ 4 * archIntegrand g u + 4 * archIntegrand h u + 4 * archIntegrand k u := by
  rw [archIntegrand_eq (g := fun t => g t + h t + k t) ((hg.add hh).add hk), archIntegrand_eq hg,
    archIntegrand_eq hh, archIntegrand_eq hk]
  have m1 : MemLp (fun t => g t - g (t + u)) 2 volume := hg.sub (memLp_shift hg u)
  have m2 : MemLp (fun t => h t - h (t + u)) 2 volume := hh.sub (memLp_shift hh u)
  have m3 : MemLp (fun t => k t - k (t + u)) 2 volume := hk.sub (memLp_shift hk u)
  have e : (fun t => (g t + h t + k t) - (g (t + u) + h (t + u) + k (t + u)))
      = fun t => (g t - g (t + u)) + (h t - h (t + u)) + (k t - k (t + u)) := by funext t; ring
  rw [e]
  have := normSq_add3_le m1 m2 m3
  have hk0 := (kerK_pos hu).le
  nlinarith

/-- `∫_{u>0} F ≤ ∫_{u>0} G` from a pointwise bound, `F ≥ 0`, `G` integrable. -/
theorem setIntegral_Ioi_le {F G : ℝ → ℝ} (hG : IntegrableOn G (Ioi 0))
    (h0 : ∀ u, 0 < u → 0 ≤ F u) (hle : ∀ u, 0 < u → F u ≤ G u) :
    (∫ u in Ioi (0 : ℝ), F u) ≤ ∫ u in Ioi (0 : ℝ), G u :=
  integral_mono_of_nonneg ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall h0)) hG
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hle))

/-- The second difference `c(φ(x + δ) − 2φ(x) + φ(x − δ))` has at most `24c²` times the energy
density of `φ`. -/
theorem archIntegrand_d2_le {φ : ℝ → ℝ} (hφ : MemLp φ 2 volume) (c δ : ℝ) {u : ℝ} (hu : 0 < u) :
    archIntegrand (fun x => c * (φ (x + δ) - 2 * φ x + φ (x - δ))) u
      ≤ 24 * c ^ 2 * archIntegrand φ u := by
  have hm : MemLp (fun x => c * (φ (x + δ) - 2 * φ x + φ (x - δ))) 2 volume := by
    have h3 : MemLp (fun x => φ (x - δ)) 2 volume := by
      simpa [sub_eq_add_neg] using memLp_shift hφ (-δ)
    exact (((memLp_shift hφ δ).sub (hφ.const_mul 2)).add h3).const_mul c
  set D : ℝ → ℝ := fun t => φ t - φ (t + u)
  have hD : MemLp D 2 volume := hφ.sub (memLp_shift hφ u)
  rw [archIntegrand_eq hm, archIntegrand_eq hφ]
  have e : (fun t => c * (φ (t + δ) - 2 * φ t + φ (t - δ))
      - c * (φ (t + u + δ) - 2 * φ (t + u) + φ (t + u - δ)))
      = fun t => c * (D (t + δ) + (-2) * D t + D (t + -δ)) := by
    funext t; simp only [D]
    rw [show t + u + δ = t + δ + u by ring, show t + u - δ = t + -δ + u by ring,
      show t - δ = t + -δ by ring]
    ring
  rw [e, normSq_smul]
  have h1 := normSq_add3_le (memLp_shift hD δ) (hD.const_mul (-2)) (memLp_shift hD (-δ))
  rw [normSq_shift, normSq_shift, normSq_smul] at h1
  have hk0 := (kerK_pos hu).le
  have hc := sq_nonneg c
  have : c ^ 2 * normSq (fun t => D (t + δ) + -2 * D t + D (t + -δ)) ≤ c ^ 2 * (24 * normSq D) := by
    apply mul_le_mul_of_nonneg_left _ hc; nlinarith
  unfold D at this ⊢
  nlinarith

/-- A dilation of a probe is a probe on the dilated support. -/
theorem probe_dil' {r : ℝ} (hr : 0 ≤ r) {g : ℝ → ℝ} (hp : Probe r g) {l : ℝ} (hl : 1 / 2 ≤ l)
    (hl1 : l ≤ 1) : Probe (l * r) (fun x => g (x / l)) := by
  have h := probe_dil hr hp hl hl1
  have hl0 : 0 < l := by linarith
  refine ⟨h.even, fun u hu => hp.supp _ ?_, h.memL2, h.arch⟩
  rw [abs_div, abs_of_pos hl0, lt_div_iff₀ hl0]; linarith

end Pilot1ca

#print axioms Pilot1ca.tendsto_normSq_shift
#print axioms Pilot1ca.tendsto_normSq_dil
#print axioms Pilot1ca.normSq_Av_le
#print axioms Pilot1ca.tendsto_Av
#print axioms Pilot1ca.probe_Av
#print axioms Pilot1ca.tendsto_archE_Av
#print axioms Pilot1ca.probe_dil
#print axioms Pilot1ca.tendsto_integral_pratt
#print axioms Pilot1ca.tendsto_archE_dil
