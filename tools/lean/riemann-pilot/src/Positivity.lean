import Mathlib
import Uniqueness

/-! # The pole-free form `Q₀`: existence, one sign, uniqueness

`Q₀ = Q − 2ĝ(i/2)² = (ψ(¼) − log π)‖g‖² + E(g) − 2S(g)`: Theorem 1bn(i)'s form with the pole term
dropped (Theorem 1bt's form). Replacing `g` by `|g|` does not increase `Q₀` (Beurling–Deny): the
archimedean term is a jump-type Dirichlet form, and the prime term has non-negative weights. At a
ground state the two sides are equal. That forces the cross-correlation of `g⁺` and `g⁻` to vanish, so
every ground state has one sign. A one-signed element of the ground-state space with `∫ = 0` is `0`,
so the ground state is unique up to sign.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## `Q₀` and its ground states -/

/-- The pole-free form `Q₀ = Q − 2ĝ(i/2)²`. -/
def weilQ0 (a : ℝ) (g : ℝ → ℝ) : ℝ := weilQ a g - 2 * poleR g a ^ 2

/-- A ground state of `Q₀`: a normalised probe minimising `Q₀`. -/
def IsGroundState0 (a : ℝ) (g : ℝ → ℝ) : Prop :=
  Probe a g ∧ normSq g = 1 ∧ ∀ h, Probe a h → normSq h = 1 → weilQ0 a g ≤ weilQ0 a h

theorem weilQ0_eq' (a : ℝ) (g : ℝ → ℝ) :
    weilQ0 a g = weilConst * normSq g + archE g - 2 * primeS g := by
  unfold weilQ0; rw [weilQ_eq']; ring

theorem weilQ0_ge {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) :
    (weilConst - 2 * primeWeight a) * normSq g ≤ weilQ0 a g := by
  have hA := archE_nonneg hp
  have hS := (le_abs_self _).trans (abs_prime_sum_le hp)
  rw [weilQ0_eq']
  unfold primeS
  nlinarith

theorem weilQ0_congr_ae {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') (a : ℝ) :
    weilQ0 a g = weilQ0 a g' := by
  unfold weilQ0; rw [weilQ_congr_ae h, poleR_congr_ae h]

theorem weilQ0_zero (a : ℝ) : weilQ0 a (fun _ => 0) = 0 := by
  unfold weilQ0; rw [weilQ_zero]; simp [poleR]

theorem weilQ0_smul (a : ℝ) (g : ℝ → ℝ) (c : ℝ) :
    weilQ0 a (fun t => c * g t) = c ^ 2 * weilQ0 a g := by
  unfold weilQ0; rw [weilQ_smul, poleR_smul]; ring

theorem weilQ0_add_sub {a : ℝ} {g h : ℝ → ℝ} (hg : Probe a g) (hh : Probe a h) :
    weilQ0 a (fun t => g t + h t) + weilQ0 a (fun t => g t - h t)
      = 2 * weilQ0 a g + 2 * weilQ0 a h := by
  have := weilQ_add_sub hg hh
  unfold weilQ0
  rw [poleR_add hg.memL2 hh.memL2, poleR_sub hg.memL2 hh.memL2]
  linear_combination this

theorem weilQ0_eq_weilQc (a : ℝ) (g : ℝ → ℝ) : weilQ0 a g = weilQc 0 a g := by
  unfold weilQ0 weilQc weilQ nonArch archE; ring

theorem exists_groundState0 {a : ℝ} (ha : 0 < a) : ∃ g, IsGroundState0 a g := by
  obtain ⟨g, hp, hn, hmin⟩ := exists_min_weilQc ha (c := 0) le_rfl
  exact ⟨g, hp, hn, fun h hph hnh => by
    rw [weilQ0_eq_weilQc, weilQ0_eq_weilQc]; exact hmin h hph hnh⟩

/-! ## Beurling–Deny: `Q₀(|g|) ≤ Q₀(g)` -/

theorem memLp_abs {g : ℝ → ℝ} (hg : MemLp g 2 volume) : MemLp (fun t => |g t|) 2 volume := by
  simpa [Real.norm_eq_abs] using hg.norm

theorem autocorr_le_abs {g : ℝ → ℝ} (hg : MemLp g 2 volume) (u : ℝ) :
    autocorr g u ≤ autocorr (fun t => |g t|) u := by
  unfold autocorr
  refine integral_mono (integrable_mul_shift hg u) (integrable_mul_shift (memLp_abs hg) u)
    fun t => ?_
  simp only
  rw [← abs_mul]; exact le_abs_self _

theorem autocorr_abs_zero (g : ℝ → ℝ) : autocorr (fun t => |g t|) 0 = autocorr g 0 := by
  simp [autocorr, abs_mul_abs_self]

theorem archIntegrand_abs_le {g : ℝ → ℝ} (hg : MemLp g 2 volume) {u : ℝ} (hu : 0 < u) :
    archIntegrand (fun t => |g t|) u ≤ archIntegrand g u := by
  unfold archIntegrand
  rw [autocorr_abs_zero]
  exact mul_le_mul_of_nonneg_right (by linarith [autocorr_le_abs hg u])
    (div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu)).le

theorem probe_abs {a : ℝ} {g : ℝ → ℝ} (hg : Probe a g) : Probe a (fun t => |g t|) := by
  have hm := memLp_abs hg.memL2
  refine ⟨fun u => by simp only [hg.even], fun u hu => by simp [hg.supp u hu], hm, ?_⟩
  refine hg.arch.mono' (measurable_archIntegrand hm).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg hm hu)]
  exact archIntegrand_abs_le hg.memL2 hu

theorem normSq_abs (g : ℝ → ℝ) : normSq (fun t => |g t|) = normSq g := by
  simp [normSq, sq_abs]

theorem archE_abs_le {a : ℝ} {g : ℝ → ℝ} (hg : Probe a g) :
    archE (fun t => |g t|) ≤ archE g :=
  setIntegral_mono_on (probe_abs hg).arch hg.arch measurableSet_Ioi
    fun _ hu => archIntegrand_abs_le hg.memL2 hu

theorem primeS_le_abs {a : ℝ} {g : ℝ → ℝ} (hg : Probe a g) :
    primeS g ≤ primeS (fun t => |g t|) := by
  unfold primeS
  rw [prime_sum_eq hg.supp, prime_sum_eq (probe_abs hg).supp]
  refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (autocorr_le_abs hg.memL2 _)
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))

/-- **Beurling–Deny for `Q₀`**: `Q₀(|g|) ≤ Q₀(g)`. -/
theorem weilQ0_abs_le {a : ℝ} {g : ℝ → ℝ} (hg : Probe a g) :
    weilQ0 a (fun t => |g t|) ≤ weilQ0 a g := by
  rw [weilQ0_eq', weilQ0_eq', normSq_abs]
  linarith [archE_abs_le hg, primeS_le_abs hg]

/-! ## A one-signed criterion -/

/-- **Tonelli, lintegral form**: for `p, m ≥ 0`, if `∫⁻ p(t)m(t+u) dt = ∫⁻ m(t)p(t+u) dt = 0` for
a.e. `u > 0`, then `(∫⁻ p)(∫⁻ m) = 0`. -/
theorem tonelli_zero {p m : ℝ → ℝ} (hp : Measurable p) (hm : Measurable m)
    (hp0 : ∀ t, 0 ≤ p t)
    (h : ∀ᵐ u ∂(volume.restrict (Ioi 0)),
      (∫⁻ t, ENNReal.ofReal (p t * m (t + u))) = 0 ∧ (∫⁻ t, ENNReal.ofReal (m t * p (t + u))) = 0) :
    (∫⁻ t, ENNReal.ofReal (p t)) * (∫⁻ t, ENNReal.ofReal (m t)) = 0 := by
  set L : ℝ → ENNReal := fun u => ∫⁻ t, ENNReal.ofReal (p t * m (t + u)) with hL
  have hF : Measurable (Function.uncurry fun (u t : ℝ) => ENNReal.ofReal (p t * m (t + u))) :=
    ENNReal.measurable_ofReal.comp
      ((hp.comp measurable_snd).mul (hm.comp (measurable_snd.add measurable_fst)))
  have hLm : Measurable L := hF.lintegral_prod_right' (ν := volume)
  have hswap : ∫⁻ u, L u = (∫⁻ t, ENNReal.ofReal (p t)) * ∫⁻ t, ENNReal.ofReal (m t) := by
    simp only [hL]
    rw [lintegral_lintegral_swap hF.aemeasurable,
      ← lintegral_mul_const (∫⁻ t, ENNReal.ofReal (m t)) hp.ennreal_ofReal]
    congr 1; funext t
    simp_rw [ENNReal.ofReal_mul (hp0 t)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact lintegral_add_left_eq_self (fun s => ENNReal.ofReal (m s)) t
  have hpos : ∫⁻ u in Ioi 0, L u = 0 := by
    rw [lintegral_eq_zero_iff hLm]
    exact h.mono fun u hu => hu.1
  have hrefl : ∀ v, L (-v) = ∫⁻ t, ENNReal.ofReal (m t * p (t + v)) := by
    intro v
    simp only [hL]
    rw [← lintegral_add_right_eq_self (fun t => ENNReal.ofReal (p t * m (t + -v))) v]
    congr 1; funext t
    rw [add_neg_cancel_right, mul_comm]
  have hneg : ∫⁻ u in Iic 0, L u = 0 := by
    have e : ∫⁻ u in Iic 0, L u = ∫⁻ v in Ici 0, L (-v) := by
      rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Ici,
        ← lintegral_neg_eq_self]
      congr 1; funext v
      by_cases hv : 0 ≤ v
      · simp [hv]
      · have : ¬ (-v ≤ 0) := by linarith
        simp [hv, this]
    rw [e, setLIntegral_congr Ioi_ae_eq_Ici.symm]
    rw [lintegral_eq_zero_iff (show Measurable fun v => L (-v) from hLm.comp measurable_neg)]
    exact h.mono fun u hu => by show L (-u) = 0; rw [hrefl]; exact hu.2
  rw [← hswap, ← lintegral_add_compl _ measurableSet_Ioi, compl_Ioi, hpos, hneg, add_zero]

/-- **If `|g|` and `g` have the same autocorrelation at almost every `u > 0`, then `g` has one
sign.** Write `g = g⁺ − g⁻`. Then `f_{|g|}(u) − f_g(u) = 2(X(u) + X(−u))` with
`X(u) = ∫ g⁺(t)g⁻(t+u) dt ≥ 0`, so `X = 0` a.e. and `(∫g⁺)(∫g⁻) = ∫ X = 0` (Tonelli). -/
theorem one_sign_of_autocorr {g : ℝ → ℝ} (hgm : Measurable g) (hg : MemLp g 2 volume)
    (h : ∀ᵐ u ∂(volume.restrict (Ioi 0)), autocorr (fun t => |g t|) u = autocorr g u) :
    (0 ≤ᵐ[volume] g) ∨ (g ≤ᵐ[volume] 0) := by
  set gp : ℝ → ℝ := fun t => (g t + |g t|) / 2 with hgp
  set gm : ℝ → ℝ := fun t => (|g t| - g t) / 2 with hgm'
  have hgp0 : ∀ t, 0 ≤ gp t := fun t => by
    simp only [hgp]; linarith [neg_abs_le (g t)]
  have hgm0 : ∀ t, 0 ≤ gm t := fun t => by
    simp only [hgm']; linarith [le_abs_self (g t)]
  have hgpm : Measurable gp := (hgm.add hgm.abs).div_const 2
  have hgmm : Measurable gm := (hgm.abs.sub hgm).div_const 2
  have hpL : MemLp gp 2 volume := by
    have := (hg.add (memLp_abs hg)).const_mul (1 / 2 : ℝ)
    convert this using 1; funext t; simp only [hgp, Pi.add_apply]; ring
  have hmL : MemLp gm 2 volume := by
    have := ((memLp_abs hg).sub hg).const_mul (1 / 2 : ℝ)
    convert this using 1; funext t; simp only [hgm', Pi.sub_apply]; ring
  set X : ℝ → ℝ := fun u => ∫ t, gp t * gm (t + u) with hX
  have hX0 : ∀ u, 0 ≤ X u := fun u =>
    integral_nonneg fun t => mul_nonneg (hgp0 t) (hgm0 _)
  have hY : ∀ u, (∫ t, gm t * gp (t + u)) = X (-u) := by
    intro u
    have := integral_add_right_eq_self (μ := volume) (fun s => gp s * gm (s + -u)) u
    simp only [add_neg_cancel_right] at this
    rw [hX]; simp only
    rw [← this]; congr 1; funext t; ring
  -- `f_{|g|}(u) − f_g(u) = 2(X(u) + X(−u))`
  have hdiff : ∀ u, autocorr (fun t => |g t|) u - autocorr g u = 2 * (X u + X (-u)) := by
    intro u
    have hY := hY u
    have i1 := integrable_mul_shift (memLp_abs hg) u
    have i2 := integrable_mul_shift hg u
    have i3 : Integrable (fun t => 2 * (gp t * gm (t + u))) :=
      (integrable_mul_shift₂ hpL hmL u).const_mul 2
    have i4 : Integrable (fun t => 2 * (gm t * gp (t + u))) :=
      (integrable_mul_shift₂ hmL hpL u).const_mul 2
    rw [← hY]
    unfold autocorr
    rw [← integral_sub i1 i2, mul_add, hX]
    simp only
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add i3 i4]
    congr 1; funext t; simp only [hgp, hgm']
    rw [← abs_mul]
    rcases le_total 0 (g t) with h1 | h1 <;> rcases le_total 0 (g (t + u)) with h2 | h2 <;>
      simp [abs_of_nonneg, abs_of_nonpos, h1, h2, mul_nonneg, mul_nonpos_iff] <;> ring
  -- `X(u) = X(−u) = 0` for a.e. `u > 0`
  have hae : ∀ᵐ u ∂(volume.restrict (Ioi 0)), X u = 0 ∧ X (-u) = 0 := by
    filter_upwards [h] with u hu
    have := hdiff u
    rw [hu, sub_self] at this
    have h1 := hX0 u
    have h2 := hX0 (-u)
    constructor <;> linarith
  -- Tonelli: `(∫⁻ g⁺)(∫⁻ g⁻) = 0`
  have hlin : ∀ {p m : ℝ → ℝ}, MemLp p 2 volume → MemLp m 2 volume → (∀ t, 0 ≤ p t) →
      (∀ t, 0 ≤ m t) → ∀ u, (∫⁻ t, ENNReal.ofReal (p t * m (t + u)))
        = ENNReal.ofReal (∫ t, p t * m (t + u)) := fun hp hm hp0 hm0 u =>
    (ofReal_integral_eq_lintegral_ofReal (integrable_mul_shift₂ hp hm u)
      (Eventually.of_forall fun t => mul_nonneg (hp0 t) (hm0 _))).symm
  have htot := tonelli_zero hgpm hgmm hgp0 (hae.mono fun u hu => by
    rw [hlin hpL hmL hgp0 hgm0, hlin hmL hpL hgm0 hgp0, hY u]
    simp only [hX] at hu ⊢
    rw [hu.1, hu.2]; simp)
  rcases mul_eq_zero.1 htot with h0 | h0
  · -- `g⁺ = 0`: `g ≤ 0`
    right
    have := (lintegral_eq_zero_iff hgpm.ennreal_ofReal).1 h0
    filter_upwards [this] with t ht
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at ht
    have := hgp0 t
    simp only [hgp] at ht this
    simp only [Pi.zero_apply]
    linarith [le_abs_self (g t), abs_nonneg (g t)]
  · left
    have := (lintegral_eq_zero_iff hgmm.ennreal_ofReal).1 h0
    filter_upwards [this] with t ht
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at ht
    have := hgm0 t
    simp only [hgm'] at ht this
    simp only [Pi.zero_apply]
    linarith [neg_abs_le (g t), abs_nonneg (g t)]

/-! ## The ground-state space of `Q₀` -/

/-- `Q₀` is a `ProbeForm`. -/
theorem weilQ0_form (a : ℝ) : ProbeForm a (weilQ0 a) where
  zero := weilQ0_zero a
  smul := weilQ0_smul a
  add_sub := weilQ0_add_sub
  congr_ae := fun h => weilQ0_congr_ae h a
  bdd := ⟨weilConst - 2 * primeWeight a, by
    rintro q ⟨h, hp, hn, rfl⟩
    have := weilQ0_ge hp; rwa [hn, mul_one] at this⟩

abbrev lam0 (a : ℝ) : ℝ := (weilQ0_form a).inf

theorem lam0_le {a : ℝ} {h : ℝ → ℝ} (hp : Probe a h) (hn : normSq h = 1) : lam0 a ≤ weilQ0 a h :=
  (weilQ0_form a).inf_le hp hn

theorem lam0_mul_le {a : ℝ} {g : ℝ → ℝ} (hg : Probe a g) : lam0 a * normSq g ≤ weilQ0 a g :=
  (weilQ0_form a).inf_mul_le hg

/-- The ground-state space of `Q₀`. -/
abbrev groundSpace0 (a : ℝ) : Submodule ℝ (ℝ → ℝ) := (weilQ0_form a).space

theorem isGroundState0_iff {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} :
    IsGroundState0 a g ↔ g ∈ groundSpace0 a ∧ normSq g = 1 :=
  (weilQ0_form a).isMin_iff ha

/-! ## Ground states of `Q₀` have one sign, and are unique -/

theorem probe_integrable {a : ℝ} {g : ℝ → ℝ} (hg : Probe a g) : Integrable g := by
  have hfin : IsFiniteMeasure (volume.restrict (Icc (-a) a)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have h1 : IntegrableOn g (Icc (-a) a) := (hg.memL2.restrict _).integrable (by norm_num)
  refine (integrableOn_iff_integrable_of_support_subset fun u hu => ?_).1 h1
  rw [Function.mem_support] at hu
  have : |u| ≤ a := by
    by_contra h'; exact hu (hg.supp u (lt_of_not_ge h'))
  exact abs_le.1 this

/-- **Every ground state of `Q₀` has one sign.** At a ground state `Q₀(|g|) = Q₀(g)`. The
archimedean integrands of `g` and `|g|` then agree a.e. on `(0, ∞)`, and
`one_sign_of_autocorr` applies. -/
theorem groundState0_one_sign {a : ℝ} {g : ℝ → ℝ} (hg : IsGroundState0 a g) :
    (0 ≤ᵐ[volume] g) ∨ (g ≤ᵐ[volume] 0) := by
  obtain ⟨hp, hn, hmin⟩ := hg
  have hpa := probe_abs hp
  have h1 := hmin _ hpa (by rw [normSq_abs, hn])
  have hA := archE_abs_le hp
  have hS := primeS_le_abs hp
  have hEq : archE (fun t => |g t|) = archE g := by
    rw [weilQ0_eq', weilQ0_eq', normSq_abs] at h1; linarith
  have hint : IntegrableOn (fun u => archIntegrand g u - archIntegrand (fun t => |g t|) u)
      (Ioi 0) := hp.arch.sub hpa.arch
  have hzero : ∫ u in Ioi 0, (archIntegrand g u - archIntegrand (fun t => |g t|) u) = 0 := by
    rw [integral_sub hp.arch hpa.arch]; unfold archE at hEq; linarith
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      fun u => archIntegrand g u - archIntegrand (fun t => |g t|) u :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu =>
      sub_nonneg.2 (archIntegrand_abs_le hp.memL2 hu))
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hzero
  have hauto : ∀ᵐ u ∂(volume.restrict (Ioi 0)),
      autocorr (fun t => |g t|) u = autocorr g u := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with u hu hu0
    have hK : 0 < Real.exp (u / 2) / Real.sinh u :=
      div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu0)
    simp only [Pi.zero_apply] at hu
    unfold archIntegrand at hu
    rw [autocorr_abs_zero] at hu
    have : (autocorr (fun t => |g t|) u - autocorr g u)
        * (Real.exp (u / 2) / Real.sinh u) = 0 := by linear_combination hu
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hK.ne'
  -- pass to a measurable representative
  have hge : g =ᵐ[volume] hp.memL2.aestronglyMeasurable.mk g :=
    hp.memL2.aestronglyMeasurable.ae_eq_mk
  set g' := hp.memL2.aestronglyMeasurable.mk g
  have hg'm : Measurable g' := hp.memL2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hg'L : MemLp g' 2 volume := MemLp.ae_eq hge hp.memL2
  have habse : (fun t => |g t|) =ᵐ[volume] fun t => |g' t| :=
    hge.mono fun t ht => by simp only [ht]
  have hauto' : ∀ᵐ u ∂(volume.restrict (Ioi 0)),
      autocorr (fun t => |g' t|) u = autocorr g' u := by
    filter_upwards [hauto] with u hu
    rw [← autocorr_congr_ae habse u, ← autocorr_congr_ae hge u]; exact hu
  rcases one_sign_of_autocorr hg'm hg'L hauto' with h | h
  · left; filter_upwards [h, hge] with t h1 h2; rw [h2]; exact h1
  · right; filter_upwards [h, hge] with t h1 h2; rw [h2]; exact h1

theorem integral_ne_zero_of_one_sign {g : ℝ → ℝ} (hi : Integrable g) (hn : normSq g = 1)
    (hs : (0 ≤ᵐ[volume] g) ∨ (g ≤ᵐ[volume] 0)) : ∫ t, g t ≠ 0 := by
  intro h0
  have hz : g =ᵐ[volume] 0 := by
    rcases hs with hs | hs
    · exact (integral_eq_zero_iff_of_nonneg_ae hs hi).1 h0
    · have hneg : 0 ≤ᵐ[volume] fun t => -g t :=
        hs.mono fun t ht => by simp only [Pi.zero_apply] at ht ⊢; linarith
      have := (integral_eq_zero_iff_of_nonneg_ae hneg hi.neg).1 (by rw [integral_neg, h0, neg_zero])
      filter_upwards [this] with t ht
      simp only [Pi.zero_apply] at ht ⊢; linarith
  have := normSq_congr_ae hz
  rw [hn] at this
  simp [normSq] at this

/-- **The ground state of `Q₀` is unique up to sign.** -/
theorem groundState0_unique {a : ℝ} (ha : 0 < a) {g h : ℝ → ℝ}
    (hg : IsGroundState0 a g) (hh : IsGroundState0 a h) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t := by
  have hgS := ((isGroundState0_iff ha).1 hg).1
  have hhS := ((isGroundState0_iff ha).1 hh).1
  have hgi := probe_integrable hg.1
  have hhi := probe_integrable hh.1
  set sg := ∫ t, g t with hsgd
  set sh := ∫ t, h t with hshd
  have hsg : sg ≠ 0 := integral_ne_zero_of_one_sign hgi hg.2.1 (groundState0_one_sign hg)
  set v : ℝ → ℝ := fun t => sh * g t - sg * h t with hv
  have hvS : v ∈ groundSpace0 a :=
    (groundSpace0 a).sub_mem ((groundSpace0 a).smul_mem sh hgS) ((groundSpace0 a).smul_mem sg hhS)
  have hvi : ∫ t, v t = 0 := by
    simp only [hv]
    rw [integral_sub (hgi.const_mul sh) (hhi.const_mul sg), integral_const_mul,
      integral_const_mul]
    ring
  rcases (normSq_nonneg v).lt_or_eq with hpos | h0
  · exfalso
    set c := 1 / Real.sqrt (normSq v) with hc
    have hu : IsGroundState0 a (fun t => c * v t) :=
      (isGroundState0_iff ha).2 ⟨(groundSpace0 a).smul_mem c hvS, by
        show normSq (fun t => c * v t) = 1
        rw [normSq_smul, hc, div_pow, Real.sq_sqrt hpos.le]; field_simp⟩
    apply integral_ne_zero_of_one_sign (probe_integrable hu.1) hu.2.1 (groundState0_one_sign hu)
    rw [integral_const_mul, hvi, mul_zero]
  · have hz := ae_zero_of_normSq hvS.1.memL2 h0.symm
    set r := sh / sg with hr
    have hhr : h =ᵐ[volume] fun t => r * g t := by
      filter_upwards [hz] with t ht
      simp only [hv, Pi.zero_apply] at ht
      rw [hr]; field_simp; linarith
    have hn := normSq_congr_ae hhr
    rw [hh.2.1, normSq_smul, hg.2.1, mul_one] at hn
    have hr2 : r = 1 ∨ r = -1 := by
      have : (r - 1) * (r + 1) = 0 := by linear_combination -hn
      rcases mul_eq_zero.1 this with h1 | h1
      · left; linarith
      · right; linarith
    rcases hr2 with h1 | h1
    · left
      filter_upwards [hhr] with t ht
      rw [ht, h1, one_mul]
    · right
      filter_upwards [hhr] with t ht
      rw [ht, h1]; ring

/-- **`Q₀` has a unique ground state up to sign, and it can be taken non-negative.** -/
theorem exists_unique_groundState0 {a : ℝ} (ha : 0 < a) :
    ∃ φ, IsGroundState0 a φ ∧ (0 ≤ᵐ[volume] φ) ∧
      ∀ g, IsGroundState0 a g → g =ᵐ[volume] φ ∨ g =ᵐ[volume] fun t => -φ t := by
  obtain ⟨g, hg⟩ := exists_groundState0 ha
  rcases groundState0_one_sign hg with hs | hs
  · exact ⟨g, hg, hs, fun h hh => groundState0_unique ha hh hg⟩
  · have hgs : IsGroundState0 a (fun t => (-1) * g t) :=
      (isGroundState0_iff ha).2 ⟨(groundSpace0 a).smul_mem (-1) ((isGroundState0_iff ha).1 hg).1,
        by show normSq (fun t => (-1) * g t) = 1; rw [normSq_smul, hg.2.1]; norm_num⟩
    refine ⟨fun t => (-1) * g t, hgs, hs.mono fun t ht => ?_, fun h hh => groundState0_unique ha hh hgs⟩
    simp only [Pi.zero_apply] at ht ⊢; linarith

end Pilot1ca

#print axioms Pilot1ca.weilQ0_add_sub
#print axioms Pilot1ca.exists_groundState0
#print axioms Pilot1ca.isGroundState0_iff
#print axioms Pilot1ca.weilQ0_abs_le
#print axioms Pilot1ca.one_sign_of_autocorr
#print axioms Pilot1ca.groundState0_one_sign
#print axioms Pilot1ca.groundState0_unique
#print axioms Pilot1ca.exists_unique_groundState0
