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

theorem autocorr_congr_ae {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') (u : ℝ) :
    autocorr g u = autocorr g' u := by
  unfold autocorr
  apply integral_congr_ae
  have h2 := (measurePreserving_add_right volume u).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [h, h2] with t h1 h2
  simp only [Function.comp_apply] at h2
  rw [h1, h2]

theorem poleR_congr_ae {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') (a : ℝ) :
    poleR g a = poleR g' a := by
  unfold poleR
  apply intervalIntegral.integral_congr_ae
  filter_upwards [h] with _ ht _
  rw [ht]

theorem normSq_congr_ae {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') : normSq g = normSq g' :=
  integral_congr_ae (h.mono fun t ht => by simp only [ht])

theorem archIntegrand_congr_ae {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') :
    archIntegrand g = archIntegrand g' := by
  funext u; unfold archIntegrand; rw [autocorr_congr_ae h 0, autocorr_congr_ae h u]

theorem weilQ_congr_ae {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') (a : ℝ) :
    weilQ a g = weilQ a g' := by
  unfold weilQ
  rw [poleR_congr_ae h, normSq_congr_ae h, archIntegrand_congr_ae h]
  simp_rw [autocorr_congr_ae h]

theorem measurable_archIntegrand {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    Measurable (archIntegrand g) := by
  have hm : Measurable (hg.aestronglyMeasurable.mk g) :=
    hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  rw [archIntegrand_congr_ae hg.aestronglyMeasurable.ae_eq_mk]
  unfold archIntegrand
  exact (measurable_const.sub (autocorr_stronglyMeasurable hm).measurable).mul
    ((Real.measurable_exp.comp (measurable_id.div_const 2)).div Real.measurable_sinh)

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

/-- The ground energy `λ₁(2a) = inf {Q(g) : g a probe, ‖g‖ = 1}`. -/
def lam (a : ℝ) : ℝ := sInf {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ weilQ a h = q}

theorem lam_bdd (a : ℝ) : BddBelow {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ weilQ a h = q} := by
  refine ⟨weilConst - 2 * primeWeight a, ?_⟩
  rintro q ⟨h, hp, hn, rfl⟩
  have := weilQ_ge hp; rwa [hn, mul_one] at this

theorem lam_le {a : ℝ} {h : ℝ → ℝ} (hp : Probe a h) (hn : normSq h = 1) : lam a ≤ weilQ a h :=
  csInf_le (lam_bdd a) ⟨h, hp, hn, rfl⟩

/-- **`R(g) = Q(g) − λ₁‖g‖² ≥ 0` on probes.** -/
theorem lam_mul_le {a : ℝ} {g : ℝ → ℝ} (hg : Probe a g) : lam a * normSq g ≤ weilQ a g := by
  rcases (normSq_nonneg g).lt_or_eq with hpos | h0
  · set c := 1 / Real.sqrt (normSq g) with hc
    have hc2 : c ^ 2 * normSq g = 1 := by
      rw [hc, div_pow, Real.sq_sqrt hpos.le]; field_simp
    have h1 := lam_le (probe_smul hg c) (by rw [normSq_smul]; exact hc2)
    rw [weilQ_smul a g c] at h1
    have hc0 : 0 < c ^ 2 := by positivity
    have : lam a * normSq g * c ^ 2 ≤ weilQ a g * c ^ 2 :=
      calc lam a * normSq g * c ^ 2 = lam a * (c ^ 2 * normSq g) := by ring
        _ = lam a := by rw [hc2, mul_one]
        _ ≤ c ^ 2 * weilQ a g := h1
        _ = weilQ a g * c ^ 2 := by ring
    exact le_of_mul_le_mul_right this hc0
  · have hz := ae_zero_of_normSq hg.memL2 h0.symm
    rw [← h0, mul_zero, weilQ_congr_ae hz]
    exact le_of_eq (weilQ_zero a).symm

/-- **The ground-state space**: probes with `Q(g) = λ₁‖g‖²`. A submodule of `ℝ → ℝ`. -/
def groundSpace (a : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {g | Probe a g ∧ weilQ a g = lam a * normSq g}
  zero_mem' := by
    refine ⟨probe_zero a, ?_⟩
    show weilQ a (fun _ => 0) = lam a * normSq (fun _ => 0)
    rw [weilQ_zero]; simp [normSq]
  add_mem' := by
    rintro g h ⟨hg, hgq⟩ ⟨hh, hhq⟩
    obtain ⟨hp, hm⟩ := probe_add_sub hg hh
    refine ⟨hp, ?_⟩
    show weilQ a (fun t => g t + h t) = lam a * normSq (fun t => g t + h t)
    have hQ := weilQ_add_sub hg hh
    have hN := normSq_add_sub hg.memL2 hh.memL2
    have r1 := lam_mul_le hp
    have r2 := lam_mul_le hm
    have : weilQ a (fun t => g t + h t) - lam a * normSq (fun t => g t + h t)
        + (weilQ a (fun t => g t - h t) - lam a * normSq (fun t => g t - h t)) = 0 := by
      linear_combination hQ - lam a * hN + 2 * hgq + 2 * hhq
    linarith
  smul_mem' := by
    rintro c g ⟨hg, hgq⟩
    refine ⟨probe_smul hg c, ?_⟩
    show weilQ a (fun t => c * g t) = lam a * normSq (fun t => c * g t)
    rw [weilQ_smul a g c, normSq_smul, hgq]; ring

/-- **The ground states are exactly the unit vectors of `groundSpace`.** -/
theorem isGroundState_iff {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} :
    IsGroundState a g ↔ g ∈ groundSpace a ∧ normSq g = 1 := by
  constructor
  · rintro ⟨hp, hn, hmin⟩
    refine ⟨⟨hp, ?_⟩, hn⟩
    rw [hn, mul_one]
    refine le_antisymm ?_ (lam_le hp hn)
    refine le_csInf ⟨_, box a, box_probe a, normSq_box ha, rfl⟩ ?_
    rintro q ⟨h, hph, hnh, rfl⟩
    exact hmin h hph hnh
  · rintro ⟨⟨hp, hq⟩, hn⟩
    refine ⟨hp, hn, fun h hph hnh => ?_⟩
    rw [hq, hn, mul_one]
    exact lam_le hph hnh

/-! ## The uniqueness criterion -/

theorem groundSpace_fun {a : ℝ} {g : ℝ → ℝ} (hg : g ∈ groundSpace a) (c : ℝ) :
    (fun t => c * g t) ∈ groundSpace a := (groundSpace a).smul_mem c hg

/-- **If two ground states are not equal up to sign, some ground state is orthogonal to
`w = 1_{[−a,a]}e^{−u/2}`**, i.e. has `ĝ(i/2) = 0`. -/
theorem exists_perp_of_not_unique {a : ℝ} (ha : 0 < a) {g h : ℝ → ℝ}
    (hg : IsGroundState a g) (hh : IsGroundState a h)
    (hne : ¬ (g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t)) :
    ∃ v, IsGroundState a v ∧ poleR v a = 0 := by
  have hgS := ((isGroundState_iff ha).1 hg).1
  have hhS := ((isGroundState_iff ha).1 hh).1
  set pg := poleR g a
  set ph := poleR h a
  by_cases hpg : pg = 0
  · exact ⟨g, hg, hpg⟩
  by_cases hph : ph = 0
  · exact ⟨h, hh, hph⟩
  set v : ℝ → ℝ := fun t => ph * g t - pg * h t with hv
  have hvS : v ∈ groundSpace a := by
    have := (groundSpace a).sub_mem (groundSpace_fun hgS ph) (groundSpace_fun hhS pg)
    exact this
  have hvm : MemLp v 2 volume := hvS.1.memL2
  have hvp : poleR v a = 0 := by
    rw [hv, poleR_sub (hg.1.memL2.const_mul ph) (hh.1.memL2.const_mul pg), poleR_smul, poleR_smul]
    ring
  rcases (normSq_nonneg v).lt_or_eq with hpos | h0
  · -- normalise `v`
    set c := 1 / Real.sqrt (normSq v) with hc
    refine ⟨fun t => c * v t, (isGroundState_iff ha).2 ⟨groundSpace_fun hvS c, ?_⟩, ?_⟩
    · rw [normSq_smul, hc, div_pow, Real.sq_sqrt hpos.le]; field_simp
    · rw [poleR_smul, hvp, mul_zero]
  · -- `v = 0` a.e.: `h = (ph/pg)·g` a.e., and the norms force `ph/pg = ±1`
    exfalso
    apply hne
    have hz := ae_zero_of_normSq hvm h0.symm
    set r := ph / pg with hr
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

/-- **Uniqueness up to sign, criterion form**: if no ground state is orthogonal to `w`
(`ĝ(i/2) ≠ 0` for every ground state), the ground state is unique up to sign. -/
theorem groundState_unique {a : ℝ} (ha : 0 < a)
    (hw : ∀ v, IsGroundState a v → poleR v a ≠ 0) {g h : ℝ → ℝ}
    (hg : IsGroundState a g) (hh : IsGroundState a h) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t := by
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := exists_perp_of_not_unique ha hg hh hne
  exact hw v hv hv0

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
