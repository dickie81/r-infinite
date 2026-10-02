import Mathlib
import Mollify
import DigammaGauss
import ArchShift

/-! # The explicit-formula bridge: `weilQ` is the zero side of Weil's explicit formula (round 126)

Four places in the pilot assume "Weil's explicit formula" in four shapes: `T1bt`'s `h_explicit`,
Exterior.lean's `WeilExplicit`, and the `hQ` hypotheses of Saturation.lean and Unconditional.lean.
Nothing connected `WeilExplicit` (the classical Guinand–Weil statement, for a test function `h`) to
the pilot's own `weilQ` (the prime-side form of Theorem 1bn(i)). This file proves the connection:

  `WeilExplicit ρ ĝ² ĝ²|ℝ`  ⟹  `Σ_ρ ĝ(t_ρ)² = weilQ a g`   (`weilQ_eq_zero_sum`)

for every even probe `g`. So `WeilExplicit` is the one named input, and the other three shapes follow.

**Proved with no new input** (the Fourier half lives in FourierInv.lean, round 127, where
SwapRealize.lean also uses it).
* **The pole terms.** `h(±i/2) = ĝ(i/2)² = poleR²` (`ghatC_I_div_two`, evenness).
* **The convolution identity** (`fourier_autocorr`): `∫ f(x)e^{irx} dx = ĝ(r)²` with `f = autocorr g`.
* **`∫ĝ² < ∞`** (`integrable_hsq`), by Gaussian regularisation and monotone convergence.
* **Fourier inversion** (`gh_hsq`): `g_h = f`, i.e. `(1/2π)∫ĝ(r)² cos(ru) dr = f(u)`. So the
  constant and prime terms of `WeilExplicit` are `weilQ`'s.
* **The archimedean term**, from `DigammaDiff` (next item), by Tonelli and `t = 2u`:
  `(1/2π)∫ĝ² Re ψ(¼ + ir/2) = Re ψ(¼)‖g‖² + archE g`.

**`DigammaDiff`**: `ψ(z) − ψ(w) = ∫_0^∞ (e^{−wt} − e^{−zt})/(1 − e^{−t}) dt` for `Re z, Re w > 0`,
Gauss's integral representation of the digamma function, in difference form. Mathlib's `Digamma.lean`
lists it as a TODO. It entered in round 126 as a named input; round 154 proves it (`digammaDiff`,
from `DigammaGauss.lean`), so no theorem here assumes it.
-/

open Real Filter Topology Complex MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace Pilot1ca

variable {a : ℝ} {g : ℝ → ℝ}

/-! ## B1. The digamma difference as a positive-kernel integral -/

/-- **Gauss's digamma integral, in difference form** (proved below as `digammaDiff`). For `Re z, Re w > 0`,
`ψ(z) − ψ(w) = ∫_0^∞ (e^{−wt} − e^{−zt})/(1 − e^{−t}) dt`, with the integrand integrable.
(Mathlib's `Digamma.lean` lists the integral representation as a TODO.) -/
def DigammaDiff : Prop :=
  ∀ z w : ℂ, 0 < z.re → 0 < w.re →
    IntegrableOn (fun t : ℝ => (cexp (-(w * t)) - cexp (-(z * t))) / ((1 - Real.exp (-t) : ℝ) : ℂ))
        (Ioi 0) ∧
      Complex.digamma z - Complex.digamma w
        = ∫ t in Ioi (0 : ℝ), (cexp (-(w * t)) - cexp (-(z * t))) / ((1 - Real.exp (-t) : ℝ) : ℂ)

/-- **`DigammaDiff` is a theorem** (round 154, `DigammaGauss.lean`): proved from Mathlib's recurrence
`ψ(s + n) = ψ(s) + Σ 1/(s + k)` and the convexity of `log Γ`. -/
theorem digammaDiff : DigammaDiff := fun _ _ hz hw => PilotDigamma.digamma_sub_eq_integral hz hw

/-- The kernel `e^{−t/4}/(1 − e^{−t})`. -/
def kk (t : ℝ) : ℝ := Real.exp (-(t / 4)) / (1 - Real.exp (-t))

/-! B1 and B2 are the instance `q = ¼` of ArchShift.lean (round 226). -/

theorem kkQ_quarter : kkQ (1 / 4) = kk := by
  funext t; unfold kkQ kk; congr 2; ring

theorem psiReQ_quarter : psiReQ (1 / 4) = psiRe := by
  funext r; unfold psiReQ psiRe zQ zB; push_cast; rfl

theorem kk_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ kk t := kkQ_quarter ▸ kkQ_nonneg _ ht

/-- **B1**: `Re ψ(¼ + ir/2) − Re ψ(¼) = ∫_0^∞ k(t)(1 − cos(rt/2)) dt`, integrably. -/
theorem psiRe_sub (r : ℝ) :
    IntegrableOn (fun t => kk t * (1 - Real.cos (r * (t / 2)))) (Ioi 0) ∧
      psiRe r - psiRe 0 = ∫ t in Ioi (0 : ℝ), kk t * (1 - Real.cos (r * (t / 2))) := by
  have h := psiReQ_sub (q := 1 / 4) (by norm_num) r
  rwa [kkQ_quarter, psiReQ_quarter] at h

/-- **B2**: `∫ ĝ(r)² (Re ψ(¼ + ir/2) − Re ψ(¼)) dr = 2π·E(g)`, integrably. -/
theorem hsq_psi_sub (hp : Probe a g) (ha : 0 < a) :
    Integrable (fun r => hsq g a r * (psiRe r - psiRe 0)) ∧
      ∫ r, hsq g a r * (psiRe r - psiRe 0) = 2 * π * archE g := by
  have h := hsq_psiQ_sub hp ha (le_refl (1 / 4 : ℝ))
  rwa [psiReQ_quarter, archEQ_quarter] at h

/-- `(1/2π)∫ ĝ² Re ψ(¼ + ir/2) = Re ψ(¼)‖g‖² + E(g)`. -/
theorem arch_term (hp : Probe a g) (ha : 0 < a) :
    1 / (2 * π) * ∫ r, hsq g a r * psiRe r = psiRe 0 * normSq g + archE g := by
  have h := arch_termQ hp ha (le_refl (1 / 4 : ℝ))
  rwa [psiReQ_quarter, archEQ_quarter] at h

/-! ## B3. The bridge -/

/-- `WeilExplicit`'s first conjunct for `h = ĝ²`. -/
theorem hsq_ofReal (hp : Probe a g) (ha : 0 ≤ a) (r : ℝ) :
    ghatC g a r ^ 2 = ((hsq g a r : ℝ) : ℂ) := by
  rw [ghatC_real hp.toE ha, hsq]; push_cast; rfl

/-- **The explicit-formula bridge**: for an even probe `g`, Weil's explicit formula for `h = ĝ²`
gives `Σ_ρ ĝ(t_ρ)² = weilQ a g`. -/
theorem weilQ_eq_zero_sum {ι : Type*} {ρ : ι → ℂ} (hp : Probe a g) (ha : 0 < a)
    (hEF : WeilExplicit ρ (fun z => ghatC g a z ^ 2) (hsq g a)) :
    HasSum (fun i => ghatC g a ((ρ i - 1 / 2) / Complex.I) ^ 2) (weilQ a g : ℂ) := by
  obtain ⟨-, hS⟩ := hEF
  convert hS using 1
  have hpole1 : ghatC g a (Complex.I / 2) ^ 2 = ((poleR g a ^ 2 : ℝ) : ℂ) := by
    rw [ghatC_I_div_two]; push_cast; rfl
  have hpole2 : ghatC g a (-(Complex.I / 2)) ^ 2 = ((poleR g a ^ 2 : ℝ) : ℂ) := by
    rw [ghatC_even hp.even, hpole1]
  have hg0 : gh (hsq g a) 0 = normSq g := by rw [gh_hsq hp.toE ha, autocorr_zero]
  have hpr : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh (hsq g a) (Real.log n)
      = primeS g := by
    unfold primeS; congr 1; funext n; rw [gh_hsq hp.toE ha]
  have hz0 : psiRe 0 = (Complex.digamma (1 / 4)).re := by unfold psiRe zB; simp
  simp only
  rw [hpole1, hpole2, hg0, hpr, arch_term hp ha, hz0, weilQ_eq', weilConst]
  push_cast; ring

/-- The same, as the zero-sum identity `weilQ a g = Σ_ρ ĝ(t_ρ)²`. -/
theorem weilQ_eq_tsum {ι : Type*} {ρ : ι → ℂ} (hp : Probe a g) (ha : 0 < a)
    (hEF : WeilExplicit ρ (fun z => ghatC g a z ^ 2) (hsq g a)) :
    (weilQ a g : ℂ) = ∑' i, ghatC g a ((ρ i - 1 / 2) / Complex.I) ^ 2 :=
  (weilQ_eq_zero_sum hp ha hEF).tsum_eq.symm

/-! ## C. The symbol form and the jump form

With no `WeilExplicit` input, Weil's form is a rank-one pole term plus a Toeplitz
(truncated Wiener–Hopf) form with an explicit symbol:

  `Q(g) = 2ĝ(i/2)² + (1/2π)∫ ĝ(r)² σ_a(r) dr`,
  `σ_a(r) = Re ψ(¼ + ir/2) − log π − 2 Σ_{n ≤ e^{2a}} Λ(n) n^{−1/2} cos(r log n)`   (`weilQ_symbol`).

With no named input at all, the pole-free form is a jump-type Dirichlet form minus a constant:
`Q₀(g) = (c₀ − 2P(a))‖g‖² + E(g) + Σ_{n ≤ e^{2a}} Λ(n) n^{−1/2} ‖g − g(· + log n)‖²` (`weilQ0_jump`). The
archimedean kernel `e^{u/2}/sinh u = 2Σ_k e^{−(2k+½)u}` is completely monotone, and each prime power
is a jump of size `log n` at rate `Λ(n)/√n`: `Q₀ + (2P(a) − c₀)` is the energy of a symmetric Lévy
process killed outside `[−a, a]`, and `psiRe_sub` is its Lévy–Khintchine formula (`psiRe_ge`: the
exponent is `≥ 0`).
-/

/-- Weil's symbol at support `a`. -/
def sigmaW (a r : ℝ) : ℝ :=
  psiRe r - Real.log π - 2 * ∑ n ∈ Finset.range (primeCut a),
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (r * Real.log n)

/-- The Lévy–Khintchine exponent is nonnegative: `Re ψ(¼) ≤ Re ψ(¼ + ir/2)`. -/
theorem psiRe_ge (r : ℝ) : psiRe 0 ≤ psiRe r := by
  have h := psiReQ_ge (q := 1 / 4) (by norm_num) r
  rwa [psiReQ_quarter] at h

theorem integrable_hsq_psi (hp : Probe a g) (ha : 0 < a) :
    Integrable (fun r => hsq g a r * psiRe r) := by
  have h := integrable_hsq_psiQ hp ha (le_refl (1 / 4 : ℝ))
  rwa [psiReQ_quarter] at h

/-- **The symbol form**: `Q(g) = 2ĝ(i/2)² + (1/2π)∫ĝ(r)²σ_a(r) dr`. -/
theorem weilQ_symbol (hp : Probe a g) (ha : 0 < a) :
    weilQ a g = 2 * poleR g a ^ 2 + 1 / (2 * π) * ∫ r, hsq g a r * sigmaW a r := by
  set S := Finset.range (primeCut a)
  set c : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / Real.sqrt n with hc
  have hI : ∀ n ∈ S, Integrable (fun r => c n * (hsq g a r * Real.cos (r * Real.log n))) :=
    fun n _ => (integrable_hsq_cos hp.toE ha (Real.log n)).const_mul (c n)
  have e : (fun r => hsq g a r * sigmaW a r) = fun r => hsq g a r * psiRe r
      - Real.log π * hsq g a r - 2 * ∑ n ∈ S, c n * (hsq g a r * Real.cos (r * Real.log n)) := by
    funext r
    have h1 : hsq g a r * (2 * ∑ n ∈ S, c n * Real.cos (r * Real.log n))
        = 2 * ∑ n ∈ S, c n * (hsq g a r * Real.cos (r * Real.log n)) := by
      rw [mul_left_comm, Finset.mul_sum]
      congr 1; exact Finset.sum_congr rfl fun n _ => by ring
    unfold sigmaW; rw [mul_sub, mul_sub, h1]; ring
  have hsum := integrable_finsetSum S hI
  have i1 : Integrable (fun r => hsq g a r * psiRe r - Real.log π * hsq g a r) :=
    (integrable_hsq_psi hp ha).sub ((integrable_hsq hp.toE ha).const_mul _)
  have i2 : Integrable (fun r => 2 * ∑ n ∈ S, c n * (hsq g a r * Real.cos (r * Real.log n))) :=
    hsum.const_mul 2
  rw [e, integral_sub i1 i2,
    integral_sub (integrable_hsq_psi hp ha) ((integrable_hsq hp.toE ha).const_mul _),
    integral_const_mul, integral_const_mul, integral_finsetSum S hI]
  have hprime : ∑ n ∈ S, ∫ r, c n * (hsq g a r * Real.cos (r * Real.log n))
      = 2 * π * primeS g := by
    unfold primeS; rw [prime_sum_eq hp.supp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, integral_hsq_cos hp.toE ha]; ring
  have harch := arch_term hp ha
  have hz0 : psiRe 0 = (Complex.digamma (1 / 4)).re := by unfold psiRe zB; simp
  rw [hprime, integral_hsq hp.toE ha, weilQ_eq', weilConst, ← hz0]
  have hπ : (0 : ℝ) < 2 * π := by positivity
  field_simp at harch ⊢
  linarith

/-- **The jump form** (no named input): `Q₀(g) = (c₀ − 2P(a))‖g‖² + E(g)
+ Σ_{n ≤ e^{2a}} Λ(n) n^{−1/2} ‖g − g(· + log n)‖²`. -/
theorem weilQ0_jump (hp : Probe a g) :
    weilQ0 a g = (weilConst - 2 * primeWeight a) * normSq g + archE g
      + ∑ n ∈ Finset.range (primeCut a), ArithmeticFunction.vonMangoldt n / Real.sqrt n
          * normSq (fun t => g t - g (t + Real.log n)) := by
  rw [weilQ0_eq', primeS, prime_sum_eq hp.supp, primeWeight]
  simp only [normSq_sub_shift hp.memL2, autocorr_zero]
  have h : ∑ n ∈ Finset.range (primeCut a), ArithmeticFunction.vonMangoldt n / Real.sqrt n
        * (2 * (normSq g - autocorr g (Real.log n)))
      = 2 * (∑ n ∈ Finset.range (primeCut a), ArithmeticFunction.vonMangoldt n / Real.sqrt n)
          * normSq g
        - 2 * ∑ n ∈ Finset.range (primeCut a), ArithmeticFunction.vonMangoldt n / Real.sqrt n
          * autocorr g (Real.log n) := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h]; ring

/-! ## D. Negative directions of `Q` count off-line zeros

Given the explicit formula, `Q(g) = Σ_ρ ĝ(t_ρ)²`. A zero on the critical line has `t_ρ` real, so its
term is the square of a real number (`ĝ` is real on `ℝ` for even `g`). So:

* `weilQ_nonneg_of_zeros_on_line`: if every zero is on the line, `Q ≥ 0` at every support (the
  RH ⇒ positivity half of Weil's criterion);
* `finrank_le_quadruples`: if `Q` is negative definite on a finite-dimensional space `V` of probes,
  then `ζ` has at least `dim V` distinct off-line zero quadruples `{ρ, ρ̄, 1 − ρ, 1 − ρ̄}` (a multiple
  quadruple counts once). `finrank_le_offline` is the crude count by family members. Imposing `Im ĝ(t_i) = 0` at each
  off-line zero is one real linear condition per zero; on the intersection every term is a real
  square, so `Q ≥ 0` there, and that intersection meets `V` only in `0`.

This is the negative-squares form of Weil's criterion (Krein–Langer / Pontryagin index), in the easy
direction. The converse, that off-line zeros do produce negative directions at large support, is not
formalised. -/

section Index

variable {ι : Type*} {ρ : ι → ℂ}

theorem ordinate_im_zero {s : ℂ} (hs : s.re = 1 / 2) : ((s - 1 / 2) / Complex.I).im = 0 := by
  simp [Complex.div_I, hs]

theorem im_ghat_of_real (hp : Probe a g) (ha : 0 < a) {t : ℂ} (ht : t.im = 0) :
    (ghatC g a t).im = 0 := by
  have e : t = ((t.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [ht])
  rw [e]; exact ghatC_im_zero hp.even ha.le _

/-- If every term `ĝ(t_i)` of the zero sum is real, then `Q(g) ≥ 0`. -/
theorem weilQ_nonneg_of_terms_real (hp : Probe a g) (ha : 0 < a)
    (hEF : WeilExplicit ρ (fun z => ghatC g a z ^ 2) (hsq g a))
    (hreal : ∀ i, (ghatC g a ((ρ i - 1 / 2) / Complex.I)).im = 0) : 0 ≤ weilQ a g := by
  have h := Complex.hasSum_re (weilQ_eq_zero_sum hp ha hEF)
  rw [Complex.ofReal_re] at h
  refine HasSum.nonneg (fun i => ?_) h
  have hi := hreal i
  rw [sq, Complex.mul_re, hi]
  nlinarith [mul_self_nonneg (ghatC g a ((ρ i - 1 / 2) / Complex.I)).re]

/-- **RH ⇒ Weil positivity**: if every zero of the family is on the critical line, `Q(g) ≥ 0` for
every even probe at every support. -/
theorem weilQ_nonneg_of_zeros_on_line (hp : Probe a g) (ha : 0 < a)
    (hEF : WeilExplicit ρ (fun z => ghatC g a z ^ 2) (hsq g a))
    (hline : ∀ i, (ρ i).re = 1 / 2) : 0 ≤ weilQ a g :=
  weilQ_nonneg_of_terms_real hp ha hEF fun i => im_ghat_of_real hp ha (ordinate_im_zero (hline i))

/-- **A negative value of `Q` exhibits an off-line zero.** -/
theorem exists_offline_of_neg (hp : Probe a g) (ha : 0 < a)
    (hEF : WeilExplicit ρ (fun z => ghatC g a z ^ 2) (hsq g a))
    (hneg : weilQ a g < 0) : ∃ i, (ρ i).re ≠ 1 / 2 := by
  by_contra h
  push Not at h
  exact absurd (weilQ_nonneg_of_zeros_on_line hp ha hEF h) (not_le.2 hneg)

/-- On the orbit `{w, −w, w̄, −w̄}` the transform of an even real function is real as soon as it is
real at `w`. -/
theorem im_ghat_of_orbit (hp : Probe a g) (ha : 0 < a) {z w : ℂ} (hw : (ghatC g a w).im = 0)
    (h : z = w ∨ z = -w ∨ z = (starRingEnd ℂ) w ∨ z = -(starRingEnd ℂ) w) :
    (ghatC g a z).im = 0 := by
  have hc : (ghatC g a ((starRingEnd ℂ) w)).im = 0 := by
    rw [ghatC_conj hp.even ha.le, Complex.conj_im, hw, neg_zero]
  rcases h with rfl | rfl | rfl | rfl
  · exact hw
  · rw [ghatC_even hp.even]; exact hw
  · exact hc
  · rw [ghatC_even hp.even]; exact hc

/-- **The sharp count: negative directions are at most the off-line quadruples.** Let `R` index one
representative per off-line quadruple: every zero of the family is either on the line or has its
ordinate in the orbit `{t_r, −t_r, t̄_r, −t̄_r}` of some `r ∈ R`. If `Q` is negative definite on a
finite-dimensional space `V` of probes, then `dim V ≤ |R|`. Repeated zeros share their
representative, so a multiple quadruple still counts once: it contributes `m·4 Re ĝ(t)²`, one negative
direction. -/
theorem finrank_le_quadruples (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V] (ha : 0 < a)
    (hV : ∀ v ∈ V, Probe a v) (hneg : ∀ v ∈ V, v ≠ 0 → weilQ a v < 0)
    (hEF : ∀ v ∈ V, WeilExplicit ρ (fun z => ghatC v a z ^ 2) (hsq v a))
    (R : Finset ι)
    (hR : ∀ i, (ρ i).re = 1 / 2 ∨ ∃ r ∈ R,
      let t := (ρ i - 1 / 2) / Complex.I
      let w := (ρ r - 1 / 2) / Complex.I
      t = w ∨ t = -w ∨ t = (starRingEnd ℂ) w ∨ t = -(starRingEnd ℂ) w) :
    Module.finrank ℝ V ≤ R.card := by
  let L : V →ₗ[ℝ] (R → ℝ) :=
    { toFun := fun v r => (ghatC (v : ℝ → ℝ) a ((ρ r - 1 / 2) / Complex.I)).im
      map_add' := fun x y => by
        funext r
        simp only [Submodule.coe_add, Pi.add_apply]
        rw [ghatC_add (hV x x.2).memL2 (hV y y.2).memL2, Complex.add_im]
      map_smul' := fun c x => by
        funext r
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        show (ghatC (fun t => c * (x : ℝ → ℝ) t) a _).im = _
        rw [ghatC_smul]; simp }
  by_contra hlt
  push Not at hlt
  have hker : LinearMap.ker L ≠ ⊥ := by
    intro hb
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    rw [hb, finrank_bot, add_zero] at h1
    have h2 := Submodule.finrank_le (LinearMap.range L)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h2
    omega
  obtain ⟨v, hvk, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hv0' : (v : ℝ → ℝ) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hq := hneg v v.2 hv0'
  have hnn : 0 ≤ weilQ a v := weilQ_nonneg_of_terms_real (hV v v.2) ha (hEF v v.2) fun i => by
    rcases hR i with hi | ⟨r, hr, horb⟩
    · exact im_ghat_of_real (hV v v.2) ha (ordinate_im_zero hi)
    · have hw := congrFun (LinearMap.mem_ker.1 hvk) ⟨r, hr⟩
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hw
      exact im_ghat_of_orbit (hV v v.2) ha hw horb
  linarith

/-- **Negative directions count off-line zeros** (the crude count, each off-line member of the family
its own representative). If `Q` is negative definite on a finite-dimensional space `V` of probes at
support `a`, and every zero outside the finite set `F` is on the line, then `dim V ≤ |F|`. -/
theorem finrank_le_offline (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V] (ha : 0 < a)
    (hV : ∀ v ∈ V, Probe a v) (hneg : ∀ v ∈ V, v ≠ 0 → weilQ a v < 0)
    (hEF : ∀ v ∈ V, WeilExplicit ρ (fun z => ghatC v a z ^ 2) (hsq v a))
    (F : Finset ι) (hF : ∀ i ∉ F, (ρ i).re = 1 / 2) :
    Module.finrank ℝ V ≤ F.card :=
  finrank_le_quadruples V ha hV hneg hEF F fun i => by
    by_cases hi : i ∈ F
    · exact Or.inr ⟨i, hi, Or.inl rfl⟩
    · exact Or.inl (hF i hi)

end Index

end Pilot1ca

#print axioms Pilot1ca.digammaDiff
#print axioms Pilot1ca.psiRe_sub
#print axioms Pilot1ca.hsq_psi_sub
#print axioms Pilot1ca.arch_term
#print axioms Pilot1ca.hsq_ofReal
#print axioms Pilot1ca.weilQ_eq_zero_sum
#print axioms Pilot1ca.weilQ_eq_tsum
#print axioms Pilot1ca.psiRe_ge
#print axioms Pilot1ca.weilQ_symbol
#print axioms Pilot1ca.weilQ0_jump
#print axioms Pilot1ca.weilQ_nonneg_of_zeros_on_line
#print axioms Pilot1ca.exists_offline_of_neg
#print axioms Pilot1ca.finrank_le_offline
#print axioms Pilot1ca.finrank_le_quadruples
