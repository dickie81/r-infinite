import Mathlib
import GroundStateExists

/-! # The ground-state space, and when the ground state is unique

1. **The ground states are the unit sphere of a linear space.** `Q` satisfies the parallelogram law
   and `Q(cg) = c²Q(g)` on probes, and probes are closed under sums and multiples. So
   `R(g) = Q(g) − λ₁‖g‖²`, which is `≥ 0` on probes, has a zero set closed under addition
   (`R(g + h) + R(g − h) = 2R(g) + 2R(h)`). That zero set is the submodule `groundSpace`, and
   `IsGroundState a g ↔ g ∈ groundSpace ∧ ‖g‖² = 1`.

2. **The uniqueness criterion.** If two ground states are not equal up to sign (a.e.), then
   `ĝ(i/2)·g − g'(i/2)·g'`, normalised, is a ground state with `ĝ(i/2) = 0`, i.e. orthogonal to
   `w = 1_{[−a,a]}e^{−u/2}`. So **if no ground state is orthogonal to `w`, the ground state is unique
   up to sign.** Equivalently, a gap `λ₁ < λ_⊥` between `λ₁` and the minimum `λ_⊥` of `Q` over probes
   with `ĝ(i/2) = 0` forces uniqueness. On those probes `Q` equals the pole-free form `Q₀`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## a.e. invariance -/

theorem poleR_congr_ae {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') (a : ℝ) :
    poleR g a = poleR g' a := by
  unfold poleR
  apply intervalIntegral.integral_congr_ae
  filter_upwards [h] with _ ht _
  rw [ht]

theorem normSq_congr_ae {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') : normSq g = normSq g' :=
  integral_congr_ae (h.mono fun t ht => by simp only [ht])

theorem weilQ_congr_ae {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') (a : ℝ) :
    weilQ a g = weilQ a g' := by
  unfold weilQ
  rw [poleR_congr_ae h, normSq_congr_ae h, archIntegrand_congr_ae h]
  simp_rw [autocorr_congr_ae h]

theorem ae_zero_of_normSq {g : ℝ → ℝ} (hg : MemLp g 2 volume) (h0 : normSq g = 0) :
    g =ᵐ[volume] 0 := by
  have := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg (g t)) hg.integrable_sq).1 h0
  filter_upwards [this] with t ht
  simpa using ht

theorem normSq_nonneg (g : ℝ → ℝ) : 0 ≤ normSq g := integral_nonneg fun _ => sq_nonneg _

/-! ## The terms of `Q` are quadratic -/

/-- The prime sum `S(g) = Σ Λ(n)/√n · f(log n)`. -/
def primeS (g : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * autocorr g (Real.log n)

theorem weilQ_eq' (a : ℝ) (g : ℝ → ℝ) :
    weilQ a g = 2 * poleR g a ^ 2 + weilConst * normSq g + archE g - 2 * primeS g := rfl

theorem autocorr_add_sub {g h : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) (u : ℝ) :
    autocorr (fun t => g t + h t) u + autocorr (fun t => g t - h t) u
      = 2 * autocorr g u + 2 * autocorr h u := by
  have i1 : Integrable (fun t => (g t + h t) * (g (t + u) + h (t + u))) :=
    integrable_mul_shift (hg.add hh) u
  have i2 : Integrable (fun t => (g t - h t) * (g (t + u) - h (t + u))) :=
    integrable_mul_shift (hg.sub hh) u
  have i3 : Integrable (fun t => 2 * (g t * g (t + u))) := (integrable_mul_shift hg u).const_mul 2
  have i4 : Integrable (fun t => 2 * (h t * h (t + u))) := (integrable_mul_shift hh u).const_mul 2
  unfold autocorr
  rw [← integral_add i1 i2, ← integral_const_mul, ← integral_const_mul, ← integral_add i3 i4]
  congr 1; funext t; ring

theorem autocorr_smul (c : ℝ) (g : ℝ → ℝ) (u : ℝ) :
    autocorr (fun t => c * g t) u = c ^ 2 * autocorr g u := by
  unfold autocorr; rw [← integral_const_mul]; congr 1; funext t; ring

theorem normSq_add_sub {g h : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    normSq (fun t => g t + h t) + normSq (fun t => g t - h t) = 2 * normSq g + 2 * normSq h := by
  simp only [← autocorr_zero]
  exact autocorr_add_sub hg hh 0

theorem normSq_smul (c : ℝ) (g : ℝ → ℝ) : normSq (fun t => c * g t) = c ^ 2 * normSq g := by
  simp only [← autocorr_zero]; exact autocorr_smul c g 0

theorem poleR_integrable {g : ℝ → ℝ} (hg : MemLp g 2 volume) (a : ℝ) :
    IntervalIntegrable (fun u => g u * Real.exp (-(u / 2))) volume (-a) a :=
  (memLp_intervalIntegrable hg _ _).mul_continuousOn (by fun_prop)

theorem poleR_add {g h : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) (a : ℝ) :
    poleR (fun t => g t + h t) a = poleR g a + poleR h a := by
  unfold poleR
  rw [← intervalIntegral.integral_add (poleR_integrable hg a) (poleR_integrable hh a)]
  congr 1; funext u; ring

theorem poleR_sub {g h : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) (a : ℝ) :
    poleR (fun t => g t - h t) a = poleR g a - poleR h a := by
  unfold poleR
  rw [← intervalIntegral.integral_sub (poleR_integrable hg a) (poleR_integrable hh a)]
  congr 1; funext u; ring

theorem poleR_smul (c : ℝ) (g : ℝ → ℝ) (a : ℝ) : poleR (fun t => c * g t) a = c * poleR g a := by
  unfold poleR; rw [← intervalIntegral.integral_const_mul]; congr 1; funext u; ring

theorem archIntegrand_add_sub {g h : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (u : ℝ) : archIntegrand (fun t => g t + h t) u + archIntegrand (fun t => g t - h t) u
      = 2 * archIntegrand g u + 2 * archIntegrand h u := by
  have e0 := autocorr_add_sub hg hh 0
  have eu := autocorr_add_sub hg hh u
  unfold archIntegrand
  linear_combination (Real.exp (u / 2) / Real.sinh u) * e0 - (Real.exp (u / 2) / Real.sinh u) * eu

theorem archIntegrand_smul (c : ℝ) (g : ℝ → ℝ) (u : ℝ) :
    archIntegrand (fun t => c * g t) u = c ^ 2 * archIntegrand g u := by
  unfold archIntegrand; rw [autocorr_smul, autocorr_smul]; ring

/-! ## Probes form a vector space -/

theorem probe_zero (a : ℝ) : Probe a (fun _ => 0) := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, MemLp.zero, ?_⟩
  have : archIntegrand (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
    funext u; simp [archIntegrand, autocorr]
  rw [this]; exact integrableOn_zero

theorem weilQ_zero (a : ℝ) : weilQ a (fun _ => 0) = 0 := by
  simp [weilQ, poleR, normSq, archIntegrand, autocorr]

theorem probe_smul {a : ℝ} {g : ℝ → ℝ} (hg : Probe a g) (c : ℝ) :
    Probe a (fun t => c * g t) := by
  refine ⟨fun u => by rw [hg.even], fun u hu => by rw [hg.supp u hu, mul_zero],
    hg.memL2.const_mul c, ?_⟩
  have : archIntegrand (fun t => c * g t) = fun u => c ^ 2 * archIntegrand g u := by
    funext u; exact archIntegrand_smul c g u
  rw [this]; exact hg.arch.const_mul _

theorem probe_add_sub {a : ℝ} {g h : ℝ → ℝ} (hg : Probe a g) (hh : Probe a h) :
    Probe a (fun t => g t + h t) ∧ Probe a (fun t => g t - h t) := by
  have hmp : MemLp (fun t => g t + h t) 2 volume := hg.memL2.add hh.memL2
  have hmm : MemLp (fun t => g t - h t) 2 volume := hg.memL2.sub hh.memL2
  have hb : IntegrableOn (fun u => 2 * archIntegrand g u + 2 * archIntegrand h u) (Ioi 0) :=
    (hg.arch.const_mul 2).add (hh.arch.const_mul 2)
  have hnn : ∀ f : ℝ → ℝ, MemLp f 2 volume → ∀ u ∈ Ioi (0 : ℝ), 0 ≤ archIntegrand f u :=
    fun f hf u hu => archIntegrand_nonneg hf hu
  constructor
  · refine ⟨fun u => by rw [hg.even, hh.even], fun u hu => by rw [hg.supp u hu, hh.supp u hu,
      add_zero], hmp, ?_⟩
    refine hb.mono' (measurable_archIntegrand hmp).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn _ hmp u hu)]
    have := archIntegrand_add_sub hg.memL2 hh.memL2 u
    linarith [hnn _ hmm u hu]
  · refine ⟨fun u => by rw [hg.even, hh.even], fun u hu => by rw [hg.supp u hu, hh.supp u hu,
      sub_zero], hmm, ?_⟩
    refine hb.mono' (measurable_archIntegrand hmm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn _ hmm u hu)]
    have := archIntegrand_add_sub hg.memL2 hh.memL2 u
    linarith [hnn _ hmp u hu]

/-! ## `Q` is a quadratic form on probes -/

theorem archE_add_sub {a : ℝ} {g h : ℝ → ℝ} (hg : Probe a g) (hh : Probe a h) :
    archE (fun t => g t + h t) + archE (fun t => g t - h t) = 2 * archE g + 2 * archE h := by
  obtain ⟨hp, hm⟩ := probe_add_sub hg hh
  unfold archE
  rw [← integral_add hp.arch hm.arch, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hg.arch.const_mul 2) (hh.arch.const_mul 2)]
  congr 1; funext u; exact archIntegrand_add_sub hg.memL2 hh.memL2 u

theorem primeS_add_sub {a : ℝ} {g h : ℝ → ℝ} (hg : Probe a g) (hh : Probe a h) :
    primeS (fun t => g t + h t) + primeS (fun t => g t - h t) = 2 * primeS g + 2 * primeS h := by
  obtain ⟨hp, hm⟩ := probe_add_sub hg hh
  unfold primeS
  rw [prime_sum_eq hp.supp, prime_sum_eq hm.supp, prime_sum_eq hg.supp, prime_sum_eq hh.supp,
    ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have := autocorr_add_sub hg.memL2 hh.memL2 (Real.log n)
  linear_combination (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * this

/-- **The parallelogram law for Weil's form.** -/
theorem weilQ_add_sub {a : ℝ} {g h : ℝ → ℝ} (hg : Probe a g) (hh : Probe a h) :
    weilQ a (fun t => g t + h t) + weilQ a (fun t => g t - h t)
      = 2 * weilQ a g + 2 * weilQ a h := by
  have hN := normSq_add_sub hg.memL2 hh.memL2
  have hA := archE_add_sub hg hh
  have hS := primeS_add_sub hg hh
  simp only [weilQ_eq']
  rw [poleR_add hg.memL2 hh.memL2, poleR_sub hg.memL2 hh.memL2]
  linear_combination weilConst * hN + hA - 2 * hS

theorem weilQ_smul (a : ℝ) (g : ℝ → ℝ) (c : ℝ) :
    weilQ a (fun t => c * g t) = c ^ 2 * weilQ a g := by
  have hA : archE (fun t => c * g t) = c ^ 2 * archE g := by
    unfold archE; rw [← integral_const_mul]; congr 1; funext u; exact archIntegrand_smul c g u
  have hS : primeS (fun t => c * g t) = c ^ 2 * primeS g := by
    unfold primeS; rw [← tsum_mul_left]; congr 1; funext n; rw [autocorr_smul]; ring
  simp only [weilQ_eq']
  rw [poleR_smul, normSq_smul, hA, hS]
  ring

/-! ## The ground energy and the ground-state space -/

/-- A quadratic form on probes, as `λ₁` and the ground-state space need it: `Q(0) = 0`,
`Q(cg) = c²Q(g)`, the parallelogram law, invariance under a.e. equality, and a lower bound
`Q(g) ≥ m‖g‖²`. Weil's form `Q` and the pole-free `Q₀` are instances. -/
structure ProbeForm (a : ℝ) (Q : (ℝ → ℝ) → ℝ) : Prop where
  zero : Q (fun _ => 0) = 0
  smul : ∀ g c, Q (fun t => c * g t) = c ^ 2 * Q g
  add_sub : ∀ {g h}, Probe a g → Probe a h →
    Q (fun t => g t + h t) + Q (fun t => g t - h t) = 2 * Q g + 2 * Q h
  congr_ae : ∀ {g g'}, g =ᵐ[volume] g' → Q g = Q g'
  bdd : BddBelow {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ Q h = q}

namespace ProbeForm

variable {a : ℝ} {Q : (ℝ → ℝ) → ℝ}

/-- The ground energy `inf {Q(g) : g a probe, ‖g‖ = 1}`. -/
def inf (_ : ProbeForm a Q) : ℝ := sInf {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ Q h = q}

theorem inf_le (F : ProbeForm a Q) {h : ℝ → ℝ} (hp : Probe a h) (hn : normSq h = 1) : F.inf ≤ Q h :=
  csInf_le F.bdd ⟨h, hp, hn, rfl⟩

theorem inf_mul_le (F : ProbeForm a Q) {g : ℝ → ℝ} (hg : Probe a g) : F.inf * normSq g ≤ Q g := by
  rcases (normSq_nonneg g).lt_or_eq with hpos | h0
  · set c := 1 / Real.sqrt (normSq g) with hc
    have hc2 : c ^ 2 * normSq g = 1 := by
      rw [hc, div_pow, Real.sq_sqrt hpos.le]; field_simp
    have h1 := F.inf_le (probe_smul hg c) (by rw [normSq_smul]; exact hc2)
    rw [F.smul g c] at h1
    have hc0 : 0 < c ^ 2 := by positivity
    have : F.inf * normSq g * c ^ 2 ≤ Q g * c ^ 2 :=
      calc F.inf * normSq g * c ^ 2 = F.inf * (c ^ 2 * normSq g) := by ring
        _ = F.inf := by rw [hc2, mul_one]
        _ ≤ c ^ 2 * Q g := h1
        _ = Q g * c ^ 2 := by ring
    exact le_of_mul_le_mul_right this hc0
  · have hz := ae_zero_of_normSq hg.memL2 h0.symm
    rw [← h0, mul_zero, F.congr_ae hz]
    exact le_of_eq F.zero.symm

/-- The ground-state space: probes with `Q(g) = inf·‖g‖²`. A submodule of `ℝ → ℝ`. -/
def space (F : ProbeForm a Q) : Submodule ℝ (ℝ → ℝ) where
  carrier := {g | Probe a g ∧ Q g = F.inf * normSq g}
  zero_mem' := by
    refine ⟨probe_zero a, ?_⟩
    show Q (fun _ => 0) = F.inf * normSq (fun _ => 0)
    rw [F.zero]; simp [normSq]
  add_mem' := by
    rintro g h ⟨hg, hgq⟩ ⟨hh, hhq⟩
    obtain ⟨hp, hm⟩ := probe_add_sub hg hh
    refine ⟨hp, ?_⟩
    show Q (fun t => g t + h t) = F.inf * normSq (fun t => g t + h t)
    have hQ := F.add_sub hg hh
    have hN := normSq_add_sub hg.memL2 hh.memL2
    have r1 := F.inf_mul_le hp
    have r2 := F.inf_mul_le hm
    have : Q (fun t => g t + h t) - F.inf * normSq (fun t => g t + h t)
        + (Q (fun t => g t - h t) - F.inf * normSq (fun t => g t - h t)) = 0 := by
      linear_combination hQ - F.inf * hN + 2 * hgq + 2 * hhq
    linarith
  smul_mem' := by
    rintro c g ⟨hg, hgq⟩
    refine ⟨probe_smul hg c, ?_⟩
    show Q (fun t => c * g t) = F.inf * normSq (fun t => c * g t)
    rw [F.smul g c, normSq_smul, hgq]; ring

/-- The normalised minimisers are exactly the unit vectors of the ground-state space. -/
theorem isMin_iff (F : ProbeForm a Q) (ha : 0 < a) {g : ℝ → ℝ} :
    (Probe a g ∧ normSq g = 1 ∧ ∀ h, Probe a h → normSq h = 1 → Q g ≤ Q h) ↔
      g ∈ F.space ∧ normSq g = 1 := by
  constructor
  · rintro ⟨hp, hn, hmin⟩
    refine ⟨⟨hp, ?_⟩, hn⟩
    rw [hn, mul_one]
    refine le_antisymm ?_ (F.inf_le hp hn)
    refine le_csInf ⟨_, box a, box_probe a, normSq_box ha, rfl⟩ ?_
    rintro q ⟨h, hph, hnh, rfl⟩
    exact hmin h hph hnh
  · rintro ⟨⟨hp, hq⟩, hn⟩
    refine ⟨hp, hn, fun h hph hnh => ?_⟩
    rw [hq, hn, mul_one]
    exact F.inf_le hph hnh

/-- **Uniqueness up to sign from a functional**: if `L`, linear on the ground-state space, vanishes on
no unit vector of it, any two unit vectors of the space agree up to sign (round 335; `groundState_unique`
takes `L = ĝ(i/2)` and `groundState0_unique` takes `L = ∫`). -/
theorem unique_of_functional (F : ProbeForm a Q) (L : (ℝ → ℝ) → ℝ)
    (hLs : ∀ g c, g ∈ F.space → L (fun t => c * g t) = c * L g)
    (hLsub : ∀ {g h}, g ∈ F.space → h ∈ F.space → L (fun t => g t - h t) = L g - L h)
    (hL : ∀ v ∈ F.space, normSq v = 1 → L v ≠ 0)
    {g h : ℝ → ℝ} (hgS : g ∈ F.space) (hgn : normSq g = 1) (hhS : h ∈ F.space)
    (hhn : normSq h = 1) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t := by
  have hLg : L g ≠ 0 := hL g hgS hgn
  have h1 : (fun t => L h * g t) ∈ F.space := F.space.smul_mem (L h) hgS
  have h2 : (fun t => L g * h t) ∈ F.space := F.space.smul_mem (L g) hhS
  set v : ℝ → ℝ := fun t => L h * g t - L g * h t with hv
  have hvS : v ∈ F.space := F.space.sub_mem h1 h2
  have hv0 : L v = 0 := by
    rw [hv, hLsub h1 h2, hLs _ _ hgS, hLs _ _ hhS]; ring
  rcases (normSq_nonneg v).lt_or_eq with hpos | h0
  · exfalso
    set c := 1 / Real.sqrt (normSq v) with hc
    have hcv : (fun t => c * v t) ∈ F.space := F.space.smul_mem c hvS
    apply hL _ hcv (by rw [normSq_smul, hc, div_pow, Real.sq_sqrt hpos.le]; field_simp)
    rw [hLs _ _ hvS, hv0, mul_zero]
  · have hz := ae_zero_of_normSq hvS.1.memL2 h0.symm
    set r := L h / L g with hr
    have hhr : h =ᵐ[volume] fun t => r * g t := by
      filter_upwards [hz] with t ht
      simp only [hv, Pi.zero_apply] at ht
      rw [hr]; field_simp; linarith
    have hn := normSq_congr_ae hhr
    rw [hhn, normSq_smul, hgn, mul_one] at hn
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

end ProbeForm

/-- Weil's form is a `ProbeForm`. -/
theorem weilQ_form (a : ℝ) : ProbeForm a (weilQ a) where
  zero := weilQ_zero a
  smul := weilQ_smul a
  add_sub := weilQ_add_sub
  congr_ae := fun h => weilQ_congr_ae h a
  bdd := ⟨weilConst - 2 * primeWeight a, by
    rintro q ⟨h, hp, hn, rfl⟩
    have := weilQ_ge hp; rwa [hn, mul_one] at this⟩

/-- The ground energy `λ₁(2a) = inf {Q(g) : g a probe, ‖g‖ = 1}`. -/
abbrev lam (a : ℝ) : ℝ := (weilQ_form a).inf

theorem lam_bdd (a : ℝ) : BddBelow {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ weilQ a h = q} :=
  (weilQ_form a).bdd

theorem lam_le {a : ℝ} {h : ℝ → ℝ} (hp : Probe a h) (hn : normSq h = 1) : lam a ≤ weilQ a h :=
  (weilQ_form a).inf_le hp hn

/-- **`R(g) = Q(g) − λ₁‖g‖² ≥ 0` on probes.** -/
theorem lam_mul_le {a : ℝ} {g : ℝ → ℝ} (hg : Probe a g) : lam a * normSq g ≤ weilQ a g :=
  (weilQ_form a).inf_mul_le hg

/-- **The ground-state space**: probes with `Q(g) = λ₁‖g‖²`. A submodule of `ℝ → ℝ`. -/
abbrev groundSpace (a : ℝ) : Submodule ℝ (ℝ → ℝ) := (weilQ_form a).space

/-- **The ground states are exactly the unit vectors of `groundSpace`.** -/
theorem isGroundState_iff {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} :
    IsGroundState a g ↔ g ∈ groundSpace a ∧ normSq g = 1 :=
  (weilQ_form a).isMin_iff ha

/-! ## The uniqueness criterion -/

theorem groundSpace_fun {a : ℝ} {g : ℝ → ℝ} (hg : g ∈ groundSpace a) (c : ℝ) :
    (fun t => c * g t) ∈ groundSpace a := (groundSpace a).smul_mem c hg

/-- **Uniqueness up to sign, criterion form**: if no ground state is orthogonal to `w`
(`ĝ(i/2) ≠ 0` for every ground state), the ground state is unique up to sign. -/
theorem groundState_unique {a : ℝ} (ha : 0 < a)
    (hw : ∀ v, IsGroundState a v → poleR v a ≠ 0) {g h : ℝ → ℝ}
    (hg : IsGroundState a g) (hh : IsGroundState a h) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t := by
  have hgS := (isGroundState_iff ha).1 hg
  have hhS := (isGroundState_iff ha).1 hh
  exact (weilQ_form a).unique_of_functional (fun f => poleR f a) (fun f c _ => poleR_smul c f a)
    (fun hf hg' => poleR_sub hf.1.memL2 hg'.1.memL2 a)
    (fun v hv hvn => hw v ((isGroundState_iff ha).2 ⟨hv, hvn⟩)) hgS.1 hgS.2 hhS.1 hhS.2

/-- **If two ground states are not equal up to sign, some ground state is orthogonal to
`w = 1_{[−a,a]}e^{−u/2}`**, i.e. has `ĝ(i/2) = 0`. -/
theorem exists_perp_of_not_unique {a : ℝ} (ha : 0 < a) {g h : ℝ → ℝ}
    (hg : IsGroundState a g) (hh : IsGroundState a h)
    (hne : ¬ (g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t)) :
    ∃ v, IsGroundState a v ∧ poleR v a = 0 := by
  by_contra hw
  push Not at hw
  exact hne (groundState_unique ha hw hg hh)

/-- `λ_⊥ = inf {Q(g) : g a probe, ‖g‖ = 1, ĝ(i/2) = 0}`, the minimum of `Q` (equivalently of the
pole-free `Q₀`) orthogonally to `w`. -/
def lamPerp (a : ℝ) : ℝ :=
  sInf {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ poleR h a = 0 ∧ weilQ a h = q}

/-- **Uniqueness up to sign, gap form**: `λ₁ < λ_⊥` forces a unique ground state. -/
theorem groundState_unique_of_gap {a : ℝ} (ha : 0 < a) (hgap : lam a < lamPerp a)
    {g h : ℝ → ℝ} (hg : IsGroundState a g) (hh : IsGroundState a h) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t := by
  refine groundState_unique ha (fun v hv hv0 => ?_) hg hh
  have hbdd : BddBelow {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ poleR h a = 0 ∧ weilQ a h = q} := by
    refine ⟨weilConst - 2 * primeWeight a, ?_⟩
    rintro q ⟨h, hp, hn, -, rfl⟩
    have := weilQ_ge hp; rwa [hn, mul_one] at this
  have h1 : lamPerp a ≤ weilQ a v := csInf_le hbdd ⟨v, hv.1, hv.2.1, hv0, rfl⟩
  have h2 : weilQ a v = lam a := by
    have := ((isGroundState_iff ha).1 hv).1.2
    rw [this, hv.2.1, mul_one]
  linarith

end Pilot1ca

#print axioms Pilot1ca.weilQ_add_sub
#print axioms Pilot1ca.weilQ_smul
#print axioms Pilot1ca.lam_mul_le
#print axioms Pilot1ca.isGroundState_iff
#print axioms Pilot1ca.exists_perp_of_not_unique
#print axioms Pilot1ca.groundState_unique
#print axioms Pilot1ca.groundState_unique_of_gap
#print axioms Pilot1ca.ProbeForm.unique_of_functional
