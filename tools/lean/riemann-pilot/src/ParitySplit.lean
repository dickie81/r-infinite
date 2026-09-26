import Mathlib
import OddPositivity
import PoleRelax

/-! # Weil's form splits by parity: positivity for every real `g` (round 125)

For a real `g` supported in `[−a, a]` (an `SProbe`), write `g = e + o` with `e(t) = (g(t) + g(−t))/2`
even and `o(t) = (g(t) − g(−t))/2` odd. Weil's functional of `F = g ⋆ g̃` (`weilQg`, OddPositivity.lean)
splits exactly:

  `weilQg a g = weilQ a e + weilQg a o`   (`weilQg_parity`).

* **The autocorrelation has no cross term** (`autocorr_parity`): the parallelogram law gives
  `f_{e+o} + f_{e−o} = 2f_e + 2f_o`, and `e − o = g(−·)` has the same autocorrelation as `g`
  (`autocorr_reflect`). So the constant, archimedean and prime terms, all linear in `f_g`, split.
* **The pole term splits too**: `ĝ(±i/2) = E ± O` with `E = ê(i/2)`, `O = ô(i/2)` (and
  `ê(−i/2) = E`, `ô(−i/2) = −O`), so `2ĝ(i/2)ĝ(−i/2) = 2E² − 2O²`, the sum of the two sectors'
  pole terms.

This is Zhu's parity splitting (his Lemma 6.1), cited in README round 39, now formalised on the pilot's
own definitions.

**Consequences.** The sector bounds combine into positivity for every real `g`:
* `weilQg_ge_twentieth_all`: `Q(g) ≥ ‖g‖²/20` for `0 < a ≤ 1/12`, **pure Lean** (even sector
  `weilQ_ge_twentieth`, odd sector `weilQodd_ge`);
* `weilQg_ge_all`: `Q(g) ≥ ‖g‖²/1000` for `0 < a ≤ 1/4`, granted the arb certificate `Cert14`
  (even sector `weilQ_ge_pole`).

Scope: positivity at these supports is known (Connes–Consani for `2a ≤ log 2`, as recalled). What is
new is a checked proof for every real `g`, both parities, on the pilot's definitions. It has no bearing
on RH, which needs every support.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-- The even part `(g(t) + g(−t))/2`. -/
def evenPart (g : ℝ → ℝ) (t : ℝ) : ℝ := (g t + g (-t)) / 2

/-- The odd part `(g(t) − g(−t))/2`. -/
def oddPart (g : ℝ → ℝ) (t : ℝ) : ℝ := (g t - g (-t)) / 2

/-! ## Reflection, and the autocorrelation split -/

/-- `g(−·)` has the same autocorrelation as `g`. -/
theorem autocorr_reflect (g : ℝ → ℝ) (u : ℝ) : autocorr (fun t => g (-t)) u = autocorr g u := by
  unfold autocorr
  have h1 := integral_neg_eq_self (fun t => g t * g (t - u)) volume
  have h2 := integral_add_right_eq_self (μ := volume) (fun t => g t * g (t - u)) u
  simp only [add_sub_cancel_right] at h2
  rw [show (fun t => g (-t) * g (-(t + u))) = fun t => g (-t) * g (-t - u) by
    funext t; ring_nf, h1, ← h2]
  congr 1; funext t; ring

theorem memLp_evenPart {g : ℝ → ℝ} (hg : MemLp g 2 volume) : MemLp (evenPart g) 2 volume := by
  have := (hg.add (memLp_neg hg)).const_mul (1 / 2 : ℝ)
  convert this using 1; funext t; simp only [evenPart, Pi.add_apply]; ring

theorem memLp_oddPart {g : ℝ → ℝ} (hg : MemLp g 2 volume) : MemLp (oddPart g) 2 volume := by
  have := (hg.sub (memLp_neg hg)).const_mul (1 / 2 : ℝ)
  convert this using 1; funext t; simp only [oddPart, Pi.sub_apply]; ring

/-- **No cross term**: `f_g = f_e + f_o`. -/
theorem autocorr_parity {g : ℝ → ℝ} (hg : MemLp g 2 volume) (u : ℝ) :
    autocorr g u = autocorr (evenPart g) u + autocorr (oddPart g) u := by
  have h := autocorr_add_sub (memLp_evenPart hg) (memLp_oddPart hg) u
  have e1 : (fun t => evenPart g t + oddPart g t) = g := by
    funext t; simp only [evenPart, oddPart]; ring
  have e2 : (fun t => evenPart g t - oddPart g t) = fun t => g (-t) := by
    funext t; simp only [evenPart, oddPart]; ring
  rw [e1, e2, autocorr_reflect] at h
  linarith

theorem normSq_parity {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    normSq g = normSq (evenPart g) + normSq (oddPart g) := by
  simp only [← autocorr_zero]; exact autocorr_parity hg 0

theorem archIntegrand_parity {g : ℝ → ℝ} (hg : MemLp g 2 volume) (u : ℝ) :
    archIntegrand g u = archIntegrand (evenPart g) u + archIntegrand (oddPart g) u := by
  unfold archIntegrand; rw [autocorr_parity hg 0, autocorr_parity hg u]; ring

/-! ## The parts are probes -/

theorem supp_evenPart {a : ℝ} {g : ℝ → ℝ} (hs : ∀ u, a < |u| → g u = 0) (u : ℝ) (hu : a < |u|) :
    evenPart g u = 0 := by
  simp only [evenPart, hs u hu, hs (-u) (by rwa [abs_neg])]; ring

theorem supp_oddPart {a : ℝ} {g : ℝ → ℝ} (hs : ∀ u, a < |u| → g u = 0) (u : ℝ) (hu : a < |u|) :
    oddPart g u = 0 := by
  simp only [oddPart, hs u hu, hs (-u) (by rwa [abs_neg])]; ring

/-- A nonnegative summand of an integrable nonnegative sum is integrable. -/
theorem arch_part {g p q : ℝ → ℝ} (hg : SProbe a g) (hp : MemLp p 2 volume) (hq : MemLp q 2 volume)
    (hsum : ∀ u, archIntegrand g u = archIntegrand p u + archIntegrand q u) :
    IntegrableOn (archIntegrand p) (Ioi 0) := by
  refine hg.arch.mono' (measurable_archIntegrand hp).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg hp hu), hsum]
  linarith [archIntegrand_nonneg hq hu]

theorem probe_evenPart {a : ℝ} {g : ℝ → ℝ} (hg : SProbe a g) : Probe a (evenPart g) :=
  ⟨fun u => by simp only [evenPart, neg_neg]; ring, supp_evenPart hg.supp,
    memLp_evenPart hg.memL2,
    arch_part hg (memLp_evenPart hg.memL2) (memLp_oddPart hg.memL2) (archIntegrand_parity hg.memL2)⟩

theorem oprobe_oddPart {a : ℝ} {g : ℝ → ℝ} (hg : SProbe a g) : OProbe a (oddPart g) :=
  ⟨fun u => by simp only [oddPart, neg_neg]; ring, supp_oddPart hg.supp,
    memLp_oddPart hg.memL2,
    arch_part hg (memLp_oddPart hg.memL2) (memLp_evenPart hg.memL2)
      (fun u => by rw [archIntegrand_parity hg.memL2 u]; ring)⟩

/-! ## The split -/

theorem archE_parity {a : ℝ} {g : ℝ → ℝ} (hg : SProbe a g) :
    archE g = archE (evenPart g) + archE (oddPart g) := by
  unfold archE
  rw [← integral_add (probe_evenPart hg).arch (oprobe_oddPart hg).arch]
  congr 1; funext u; exact archIntegrand_parity hg.memL2 u

theorem primeS_parity {a : ℝ} {g : ℝ → ℝ} (hg : SProbe a g) :
    primeS g = primeS (evenPart g) + primeS (oddPart g) := by
  unfold primeS
  rw [prime_sum_eq hg.supp, prime_sum_eq (supp_evenPart hg.supp), prime_sum_eq (supp_oddPart hg.supp),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [autocorr_parity hg.memL2]; ring

theorem poleR_parity {a : ℝ} {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    poleR g a = poleR (evenPart g) a + poleR (oddPart g) a := by
  rw [← poleR_add (memLp_evenPart hg) (memLp_oddPart hg)]
  congr 1; funext t; simp only [evenPart, oddPart]; ring

theorem poleL_parity {a : ℝ} {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    poleL g a = poleL (evenPart g) a + poleL (oddPart g) a := by
  have ii : ∀ {f : ℝ → ℝ}, MemLp f 2 volume →
      IntervalIntegrable (fun u => f u * Real.exp (u / 2)) volume (-a) a :=
    fun hf => (memLp_intervalIntegrable hf _ _).mul_continuousOn (by fun_prop)
  unfold poleL
  rw [← intervalIntegral.integral_add (ii (memLp_evenPart hg)) (ii (memLp_oddPart hg))]
  congr 1; funext u; simp only [evenPart, oddPart]; ring

/-- **The parity split** of Weil's functional for real `g`: `Q(g) = Q(e) + Q(o)`. -/
theorem weilQg_parity {a : ℝ} {g : ℝ → ℝ} (hg : SProbe a g) :
    weilQg a g = weilQ a (evenPart g) + weilQg a (oddPart g) := by
  have he := probe_evenPart hg
  have ho := oprobe_oddPart hg
  rw [← weilQg_even he]
  unfold weilQg
  rw [poleR_parity hg.memL2, poleL_parity hg.memL2, poleL_even he, poleL_odd ho,
    normSq_parity hg.memL2, archE_parity hg, primeS_parity hg]
  ring

/-! ## Positivity for every real `g` -/

/-- A bound on normalised even probes is a bound `c‖g‖² ≤ Q(g)` on all of them. -/
theorem weilQ_ge_mul {a c : ℝ} (ha : 0 < a)
    (h : ∀ g, Probe a g → normSq g = 1 → c ≤ weilQ a g) {g : ℝ → ℝ} (hp : Probe a g) :
    c * normSq g ≤ weilQ a g := by
  have hl : c ≤ lam a :=
    le_csInf ⟨_, box a, box_probe a, normSq_box ha, rfl⟩ fun q ⟨h', hp', hn', hq⟩ => hq ▸ h h' hp' hn'
  have := lam_mul_le hp
  nlinarith [normSq_nonneg g]

theorem OProbe.smul {a : ℝ} {g : ℝ → ℝ} (hp : OProbe a g) (c : ℝ) : OProbe a (fun t => c * g t) :=
  ⟨fun u => by rw [hp.odd]; ring, fun u hu => by rw [hp.supp u hu, mul_zero], hp.memL2.const_mul c,
    by
      have e : archIntegrand (fun t => c * g t) = fun u => c ^ 2 * archIntegrand g u :=
        funext fun u => archIntegrand_smul c g u
      rw [e]; exact hp.arch.const_mul (c ^ 2)⟩

theorem weilQg_smul (a c : ℝ) (g : ℝ → ℝ) :
    weilQg a (fun t => c * g t) = c ^ 2 * weilQg a g := by
  have hL : poleL (fun t => c * g t) a = c * poleL g a := by
    unfold poleL; rw [← intervalIntegral.integral_const_mul]; congr 1; funext u; ring
  have hA : archE (fun t => c * g t) = c ^ 2 * archE g := by
    unfold archE; simp only [archIntegrand_smul]; exact integral_const_mul _ _
  have hS : primeS (fun t => c * g t) = c ^ 2 * primeS g := by
    unfold primeS; simp only [autocorr_smul]; rw [← tsum_mul_left]; congr 1; funext n; ring
  unfold weilQg; rw [poleR_smul, hL, normSq_smul, hA, hS]; ring

/-- The odd-sector bound, unnormalised: `‖g‖²/20 ≤ Q(g)` for odd probes, `0 < a ≤ 1/4`. -/
theorem weilQodd_ge_mul {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 4) {g : ℝ → ℝ} (hp : OProbe a g) :
    (1 / 20) * normSq g ≤ weilQg a g := by
  rcases (normSq_nonneg g).lt_or_eq with hpos | h0
  · set c := 1 / Real.sqrt (normSq g)
    have hc2 : c ^ 2 * normSq g = 1 := by
      simp only [c]; rw [div_pow, Real.sq_sqrt hpos.le]; field_simp
    have h1 := weilQodd_ge ha ha1 (hp.smul c) (by rw [normSq_smul]; exact hc2)
    rw [weilQg_smul] at h1
    have hc0 : 0 < c ^ 2 := by positivity
    have : (1 / 20) * normSq g * c ^ 2 ≤ weilQg a g * c ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this hc0
  · -- `g = 0` a.e., so every term vanishes
    have hz := ae_zero_of_normSq hp.memL2 h0.symm
    have hf : ∀ u, autocorr g u = 0 := fun u => by
      rw [autocorr_congr_ae hz u]; simp [autocorr]
    have hA : archE g = 0 := by
      unfold archE archIntegrand; simp [hf]
    have hS : primeS g = 0 := by unfold primeS; simp [hf]
    have hR : poleR g a = 0 := by rw [poleR_congr_ae hz]; simp [poleR]
    unfold weilQg; rw [hA, hS, hR, ← h0]; norm_num

/-- **Weil positivity for every real `g`, pure Lean**: `Q(g) ≥ ‖g‖²/20` for `0 < a ≤ 1/12`. -/
theorem weilQg_ge_twentieth_all {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 12) {g : ℝ → ℝ} (hg : SProbe a g) :
    (1 / 20) * normSq g ≤ weilQg a g := by
  rw [weilQg_parity hg, normSq_parity hg.memL2]
  have he := weilQ_ge_mul ha (fun h hp hn => weilQ_ge_twentieth ha ha1 hp hn) (probe_evenPart hg)
  have ho := weilQodd_ge_mul ha (by linarith) (oprobe_oddPart hg)
  linarith

/-- **Weil positivity for every real `g`** on `(0, 1/4]`, granted the certificate `Cert14`:
`Q(g) ≥ ‖g‖²/1000`. -/
theorem weilQg_ge_all {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 4) (hc : Cert14) {g : ℝ → ℝ}
    (hg : SProbe a g) : (1 / 1000) * normSq g ≤ weilQg a g := by
  rw [weilQg_parity hg, normSq_parity hg.memL2]
  have he := weilQ_ge_mul ha (fun h hp hn => weilQ_ge_pole ha ha1 hc hp hn) (probe_evenPart hg)
  have ho := weilQodd_ge_mul ha ha1 (oprobe_oddPart hg)
  nlinarith [normSq_nonneg (oddPart g)]

end Pilot1ca

#print axioms Pilot1ca.autocorr_reflect
#print axioms Pilot1ca.autocorr_parity
#print axioms Pilot1ca.probe_evenPart
#print axioms Pilot1ca.oprobe_oddPart
#print axioms Pilot1ca.weilQg_parity
#print axioms Pilot1ca.weilQodd_ge_mul
#print axioms Pilot1ca.weilQg_ge_twentieth_all
#print axioms Pilot1ca.weilQg_ge_all
