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

/-- The non-archimedean part of `Q₀`: the constant and prime terms. -/
def nonArch0 (_a : ℝ) (g : ℝ → ℝ) : ℝ :=
  ((Complex.digamma (1 / 4)).re - Real.log π) * normSq g
    - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * autocorr g (Real.log n)

theorem weilQ0_eq_nonArch0_add (a : ℝ) (g : ℝ → ℝ) : weilQ0 a g = nonArch0 a g + archE g := by
  unfold weilQ0 weilQ nonArch0 archE; ring

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

theorem exists_groundState0 {a : ℝ} (ha : 0 < a) : ∃ g, IsGroundState0 a g := by
  set Sv : Set ℝ := {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ weilQ0 a h = q} with hSv
  have hne : Sv.Nonempty := ⟨_, box a, box_probe a, normSq_box ha, rfl⟩
  have hbdd : BddBelow Sv := by
    refine ⟨weilConst - 2 * primeWeight a, ?_⟩
    rintro q ⟨h, hp, hn, rfl⟩
    have := weilQ0_ge hp; rwa [hn, mul_one] at this
  obtain ⟨q, hqa, hq, hqS⟩ := exists_seq_tendsto_sInf hne hbdd
  choose h hp hn hQ using hqS
  set lam := sInf Sv with hlam
  -- the non-archimedean part is bounded below, so the archimedean energy is bounded above
  have hNA : ∀ g, Probe a g → normSq g = 1 → weilConst - 2 * primeWeight a ≤ nonArch0 a g := by
    intro g hpg hng
    have hprime := (le_abs_self _).trans (abs_prime_sum_le hpg)
    unfold nonArch0 weilConst
    rw [hng] at hprime ⊢
    linarith
  have hC : ∀ j, archE (h j) ≤ q 0 - (weilConst - 2 * primeWeight a) := by
    intro j
    have e := weilQ0_eq_nonArch0_add a (h j)
    have := hNA (h j) (hp j) (hn j)
    have hqj : q j ≤ q 0 := hqa (Nat.zero_le j)
    rw [hQ j] at e
    linarith
  obtain ⟨φ, hφ, G, hG, hlim⟩ := exists_convergent_subseq ha hp (B := 1) (fun j => (hn j).le) hC
  set G' := symCut a G with hG'def
  have hG' : MemLp G' 2 volume := memLp_symCut a hG
  have hlim' : Tendsto (fun j => normSq (fun t => h (φ j) t - G' t)) atTop (𝓝 0) :=
    squeeze_zero (fun j => integral_nonneg fun t => sq_nonneg _)
      (fun j => normSq_sub_symCut_le (hp (φ j)) hG) hlim
  have hmem : ∀ j, MemLp (h (φ j)) 2 volume := fun j => (hp (φ j)).memL2
  -- continuity of the non-archimedean terms
  have hnorm : Tendsto (fun j => normSq (h (φ j))) atTop (𝓝 (normSq G')) := by
    simp_rw [normSq_eq_mul]
    exact tendsto_integral_mul hmem hmem hG' hG' hlim' hlim'
  have hnormG : normSq G' = 1 := by
    have h1 : Tendsto (fun j => normSq (h (φ j))) atTop (𝓝 1) := by
      simp only [hn]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hnorm h1
  have hauto : ∀ u, Tendsto (fun j => autocorr (h (φ j)) u) atTop (𝓝 (autocorr G' u)) := by
    intro u
    have hsh : ∀ j, normSq (fun t => h (φ j) (t + u) - G' (t + u))
        = normSq (fun t => h (φ j) t - G' t) :=
      fun j => normSq_shift (fun t => h (φ j) t - G' t) u
    unfold autocorr
    exact tendsto_integral_mul hmem (fun j => memLp_shift (hmem j) u) hG' (memLp_shift hG' u)
      hlim' (hlim'.congr fun j => (hsh j).symm)
  have hsuppG' : ∀ u, a < |u| → G' u = 0 := symCut_supp a G
  have hprimeT : Tendsto
      (fun j => ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n
        * autocorr (h (φ j)) (Real.log n)) atTop
      (𝓝 (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * autocorr G' (Real.log n))) := by
    have e1 : ∀ j, (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n
        * autocorr (h (φ j)) (Real.log n))
        = ∑ n ∈ Finset.range (primeCut a), ArithmeticFunction.vonMangoldt n / Real.sqrt n
          * autocorr (h (φ j)) (Real.log n) := fun j => prime_sum_eq (hp (φ j)).supp
    simp_rw [e1]
    rw [prime_sum_eq hsuppG']
    exact tendsto_finsetSum _ fun n _ => (hauto _).const_mul _
  have hnonArch : Tendsto (fun j => nonArch0 a (h (φ j))) atTop (𝓝 (nonArch0 a G')) := by
    unfold nonArch0
    exact (hnorm.const_mul _).sub (hprimeT.const_mul 2)
  -- the archimedean energies converge to `λ − nonArch(G')`
  have hqφ : Tendsto (fun j => q (φ j)) atTop (𝓝 lam) := hq.comp hφ.tendsto_atTop
  have hA : Tendsto (fun j => archE (h (φ j))) atTop (𝓝 (lam - nonArch0 a G')) := by
    have e : ∀ j, archE (h (φ j)) = q (φ j) - nonArch0 a (h (φ j)) := by
      intro j; rw [← hQ (φ j), weilQ0_eq_nonArch0_add]; ring
    simp_rw [e]
    exact hqφ.sub hnonArch
  -- Fatou: the limit's archimedean integral converges and is at most the limit
  obtain ⟨hint, hle⟩ := fatou_real measurableSet_Ioi
    (f := fun j => archIntegrand (h (φ j))) (F := archIntegrand G')
    (fun j => (hp (φ j)).arch) (fun j u hu => archIntegrand_nonneg (hmem j) hu)
    (fun u _ => by
      unfold archIntegrand
      exact ((hauto 0).sub (hauto u)).mul_const _) hA
  have hPG : Probe a G' := ⟨symCut_even a G, hsuppG', hG', hint⟩
  refine ⟨G', hPG, hnormG, fun h' hp' hn' => ?_⟩
  have hQG : weilQ0 a G' ≤ lam := by
    rw [weilQ0_eq_nonArch0_add]; unfold archE; linarith
  exact hQG.trans (csInf_le hbdd ⟨h', hp', hn', rfl⟩)


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
  -- `f_{|g|}(u) − f_g(u) = 2(X(u) + X(−u))`
  have hdiff : ∀ u, autocorr (fun t => |g t|) u - autocorr g u = 2 * (X u + X (-u)) := by
    intro u
    have hY : (∫ t, gm t * gp (t + u)) = X (-u) := by
      have := integral_add_right_eq_self (μ := volume) (fun s => gp s * gm (s + -u)) u
      simp only [add_neg_cancel_right] at this
      rw [hX]; simp only
      rw [← this]; congr 1; funext t; ring
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
  -- Tonelli: `∫⁻ ofReal X = (∫⁻ g⁺)(∫⁻ g⁻)`
  have hF : Measurable (Function.uncurry fun (u t : ℝ) => ENNReal.ofReal (gp t * gm (t + u))) :=
    ENNReal.measurable_ofReal.comp
      ((hgpm.comp measurable_snd).mul (hgmm.comp (measurable_snd.add measurable_fst)))
  have hXl : ∀ u, ENNReal.ofReal (X u) = ∫⁻ t, ENNReal.ofReal (gp t * gm (t + u)) := fun u =>
    ofReal_integral_eq_lintegral_ofReal (integrable_mul_shift₂ hpL hmL u)
      (Eventually.of_forall fun t => mul_nonneg (hgp0 t) (hgm0 _))
  have htonelli : ∫⁻ u, ENNReal.ofReal (X u)
      = (∫⁻ t, ENNReal.ofReal (gp t)) * ∫⁻ s, ENNReal.ofReal (gm s) := by
    simp_rw [hXl]
    rw [lintegral_lintegral_swap hF.aemeasurable,
      ← lintegral_mul_const (∫⁻ s, ENNReal.ofReal (gm s)) hgpm.ennreal_ofReal]
    congr 1; funext t
    simp_rw [ENNReal.ofReal_mul (hgp0 t)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact lintegral_add_left_eq_self (fun s => ENNReal.ofReal (gm s)) t
  -- `∫⁻ ofReal X = 0`: split at `0` and reflect the negative half
  have hXm : Measurable fun u => ENNReal.ofReal (X u) := by
    have := hF.lintegral_prod_right' (ν := (volume : Measure ℝ))
    simp only [Function.uncurry_apply_pair] at this
    simpa only [hXl] using this
  have hpos : ∫⁻ u in Ioi 0, ENNReal.ofReal (X u) = 0 := by
    rw [lintegral_eq_zero_iff hXm]
    exact hae.mono fun u hu => by simp [hu.1]
  have hneg : ∫⁻ u in Iic 0, ENNReal.ofReal (X u) = 0 := by
    have e : ∫⁻ u in Iic 0, ENNReal.ofReal (X u) = ∫⁻ v in Ici 0, ENNReal.ofReal (X (-v)) := by
      rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Ici,
        ← lintegral_neg_eq_self]
      congr 1; funext v
      by_cases hv : 0 ≤ v
      · simp [hv]
      · have : ¬ (-v ≤ 0) := by linarith
        simp [hv, this]
    rw [e, setLIntegral_congr Ioi_ae_eq_Ici.symm]
    rw [lintegral_eq_zero_iff (show Measurable fun v => ENNReal.ofReal (X (-v)) from
      hXm.comp measurable_neg)]
    exact hae.mono fun u hu => by simp [hu.2]
  have htot : ∫⁻ u, ENNReal.ofReal (X u) = 0 := by
    rw [← lintegral_add_compl _ measurableSet_Ioi, compl_Ioi, hpos, hneg, add_zero]
  rw [htonelli] at htot
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

def lam0 (a : ℝ) : ℝ := sInf {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ weilQ0 a h = q}

theorem lam0_bdd (a : ℝ) : BddBelow {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ weilQ0 a h = q} := by
  refine ⟨weilConst - 2 * primeWeight a, ?_⟩
  rintro q ⟨h, hp, hn, rfl⟩
  have := weilQ0_ge hp; rwa [hn, mul_one] at this

theorem lam0_le {a : ℝ} {h : ℝ → ℝ} (hp : Probe a h) (hn : normSq h = 1) : lam0 a ≤ weilQ0 a h :=
  csInf_le (lam0_bdd a) ⟨h, hp, hn, rfl⟩

theorem lam0_mul_le {a : ℝ} {g : ℝ → ℝ} (hg : Probe a g) : lam0 a * normSq g ≤ weilQ0 a g := by
  rcases (normSq_nonneg g).lt_or_eq with hpos | h0
  · set c := 1 / Real.sqrt (normSq g) with hc
    have hc2 : c ^ 2 * normSq g = 1 := by
      rw [hc, div_pow, Real.sq_sqrt hpos.le]; field_simp
    have h1 := lam0_le (probe_smul hg c) (by rw [normSq_smul]; exact hc2)
    rw [weilQ0_smul a g c] at h1
    have hc0 : 0 < c ^ 2 := by positivity
    have : lam0 a * normSq g * c ^ 2 ≤ weilQ0 a g * c ^ 2 :=
      calc lam0 a * normSq g * c ^ 2 = lam0 a * (c ^ 2 * normSq g) := by ring
        _ = lam0 a := by rw [hc2, mul_one]
        _ ≤ c ^ 2 * weilQ0 a g := h1
        _ = weilQ0 a g * c ^ 2 := by ring
    exact le_of_mul_le_mul_right this hc0
  · have hz := ae_zero_of_normSq hg.memL2 h0.symm
    rw [← h0, mul_zero, weilQ0_congr_ae hz]
    exact le_of_eq (weilQ0_zero a).symm

/-- The ground-state space of `Q₀`. -/
def groundSpace0 (a : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {g | Probe a g ∧ weilQ0 a g = lam0 a * normSq g}
  zero_mem' := by
    refine ⟨probe_zero a, ?_⟩
    show weilQ0 a (fun _ => 0) = lam0 a * normSq (fun _ => 0)
    rw [weilQ0_zero]; simp [normSq]
  add_mem' := by
    rintro g h ⟨hg, hgq⟩ ⟨hh, hhq⟩
    obtain ⟨hp, hm⟩ := probe_add_sub hg hh
    refine ⟨hp, ?_⟩
    show weilQ0 a (fun t => g t + h t) = lam0 a * normSq (fun t => g t + h t)
    have hQ := weilQ0_add_sub hg hh
    have hN := normSq_add_sub hg.memL2 hh.memL2
    have r1 := lam0_mul_le hp
    have r2 := lam0_mul_le hm
    have : weilQ0 a (fun t => g t + h t) - lam0 a * normSq (fun t => g t + h t)
        + (weilQ0 a (fun t => g t - h t) - lam0 a * normSq (fun t => g t - h t)) = 0 := by
      linear_combination hQ - lam0 a * hN + 2 * hgq + 2 * hhq
    linarith
  smul_mem' := by
    rintro c g ⟨hg, hgq⟩
    refine ⟨probe_smul hg c, ?_⟩
    show weilQ0 a (fun t => c * g t) = lam0 a * normSq (fun t => c * g t)
    rw [weilQ0_smul a g c, normSq_smul, hgq]; ring

theorem isGroundState0_iff {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} :
    IsGroundState0 a g ↔ g ∈ groundSpace0 a ∧ normSq g = 1 := by
  constructor
  · rintro ⟨hp, hn, hmin⟩
    refine ⟨⟨hp, ?_⟩, hn⟩
    rw [hn, mul_one]
    refine le_antisymm ?_ (lam0_le hp hn)
    refine le_csInf ⟨_, box a, box_probe a, normSq_box ha, rfl⟩ ?_
    rintro q ⟨h, hph, hnh, rfl⟩
    exact hmin h hph hnh
  · rintro ⟨⟨hp, hq⟩, hn⟩
    refine ⟨hp, hn, fun h hph hnh => ?_⟩
    rw [hq, hn, mul_one]
    exact lam0_le hph hnh

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
