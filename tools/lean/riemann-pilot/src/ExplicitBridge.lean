import Mathlib
import Mollify

/-! # The explicit-formula bridge: `weilQ` is the zero side of Weil's explicit formula (round 126)

Four places in the pilot assume "Weil's explicit formula" in four shapes: `T1bt`'s `h_explicit`,
Exterior.lean's `WeilExplicit`, and the `hQ` hypotheses of Saturation.lean and Unconditional.lean.
Nothing connected `WeilExplicit` (the classical Guinand–Weil statement, for a test function `h`) to
the pilot's own `weilQ` (the prime-side form of Theorem 1bn(i)). This file proves the connection:

  `WeilExplicit ρ ĝ² ĝ²|ℝ` and `DigammaDiff`  ⟹  `Σ_ρ ĝ(t_ρ)² = weilQ a g`   (`weilQ_eq_zero_sum`)

for every even probe `g`. So `WeilExplicit` is the one named input, and the other three shapes follow.

**Proved with no new input** (the Fourier half lives in FourierInv.lean, round 127, where
SwapRealize.lean also uses it).
* **The pole terms.** `h(±i/2) = ĝ(i/2)² = poleR²` (`ghatC_I_div_two`, evenness).
* **The convolution identity** (`fourier_autocorr`): `∫ f(x)e^{irx} dx = ĝ(r)²` with `f = autocorr g`.
* **`∫ĝ² < ∞`** (`integrable_hsq`), by Gaussian regularisation and monotone convergence.
* **Fourier inversion** (`gh_hsq`): `g_h = f`, i.e. `(1/2π)∫ĝ(r)² cos(ru) dr = f(u)`. So the
  constant and prime terms of `WeilExplicit` are `weilQ`'s.
* **The archimedean term**, given `DigammaDiff` (next item), by Tonelli and `t = 2u`:
  `(1/2π)∫ĝ² Re ψ(¼ + ir/2) = Re ψ(¼)‖g‖² + archE g`.

**The new named input `DigammaDiff`**: `ψ(z) − ψ(w) = ∫_0^∞ (e^{−wt} − e^{−zt})/(1 − e^{−t}) dt` for
`Re z, Re w > 0`. This is Gauss's integral representation of the digamma function, in difference form.
Mathlib's `Digamma.lean` lists it as a TODO, so it enters as a hypothesis, like `BinetFormula`
(Exterior.lean) does.
-/

open Real Filter Topology Complex MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace Pilot1ca

variable {a : ℝ} {g : ℝ → ℝ}

/-! ## B1. The digamma difference as a positive-kernel integral -/

/-- **Named input: Gauss's digamma integral, in difference form.** For `Re z, Re w > 0`,
`ψ(z) − ψ(w) = ∫_0^∞ (e^{−wt} − e^{−zt})/(1 − e^{−t}) dt`, with the integrand integrable.
(Mathlib's `Digamma.lean` lists the integral representation as a TODO.) -/
def DigammaDiff : Prop :=
  ∀ z w : ℂ, 0 < z.re → 0 < w.re →
    IntegrableOn (fun t : ℝ => (cexp (-(w * t)) - cexp (-(z * t))) / ((1 - Real.exp (-t) : ℝ) : ℂ))
        (Ioi 0) ∧
      Complex.digamma z - Complex.digamma w
        = ∫ t in Ioi (0 : ℝ), (cexp (-(w * t)) - cexp (-(z * t))) / ((1 - Real.exp (-t) : ℝ) : ℂ)

/-- The kernel `e^{−t/4}/(1 − e^{−t})`. -/
def kk (t : ℝ) : ℝ := Real.exp (-(t / 4)) / (1 - Real.exp (-t))

theorem kk_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ kk t := by
  unfold kk
  have : Real.exp (-t) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  exact div_nonneg (Real.exp_pos _).le (by linarith)

theorem measurable_kk : Measurable kk := by unfold kk; fun_prop

theorem kk_re (r t : ℝ) :
    ((cexp (-(zB 0 * t)) - cexp (-(zB r * t))) / ((1 - Real.exp (-t) : ℝ) : ℂ)).re
      = kk t * (1 - Real.cos (r * (t / 2))) := by
  rw [Complex.div_ofReal_re, Complex.sub_re, Complex.exp_re, Complex.exp_re]
  unfold kk zB
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.div_re, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
  norm_num
  rw [show r * 2 / 4 * t = r * (t / 2) by ring, show (1 : ℝ) / 4 * t = t / 4 by ring]
  ring

/-- **B1**: `Re ψ(¼ + ir/2) − Re ψ(¼) = ∫_0^∞ k(t)(1 − cos(rt/2)) dt`, integrably. -/
theorem psiRe_sub (hD : DigammaDiff) (r : ℝ) :
    IntegrableOn (fun t => kk t * (1 - Real.cos (r * (t / 2)))) (Ioi 0) ∧
      psiRe r - psiRe 0 = ∫ t in Ioi (0 : ℝ), kk t * (1 - Real.cos (r * (t / 2))) := by
  have hz : ∀ s : ℝ, 0 < (zB s).re := fun s => by unfold zB; simp
  obtain ⟨hI, hE⟩ := hD (zB r) (zB 0) (hz r) (hz 0)
  have hI' := hI.re
  simp only [RCLike.re_to_complex, kk_re] at hI'
  refine ⟨hI', ?_⟩
  unfold psiRe
  have h2 := integral_re hI
  simp only [RCLike.re_to_complex, kk_re] at h2
  rw [← Complex.sub_re, hE, ← h2]

/-! ## B2. The archimedean term, by Tonelli and `t = 2u` -/

/-- The `t`-integrand after the `r`-integral: `k(t)(f(0) − f(t/2))`. -/
def phiA (g : ℝ → ℝ) (t : ℝ) : ℝ := kk t * (autocorr g 0 - autocorr g (t / 2))

theorem phiA_two_mul (g : ℝ → ℝ) {u : ℝ} (hu : 0 < u) : 2 * phiA g (2 * u) = archIntegrand g u := by
  unfold phiA kk archIntegrand
  rw [show 2 * u / 2 = u by ring, Real.sinh_eq]
  have e1 : Real.exp (-(2 * u / 4)) = Real.exp (-(u / 2)) := by congr 1; ring
  have e2 : Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (u / 2) = Real.exp u * Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : Real.exp (-u) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-u) := Real.exp_pos _
  have h4 : 1 - Real.exp (-u) * Real.exp (-u) ≠ 0 := by nlinarith
  have h5 : Real.exp u - Real.exp (-u) ≠ 0 := by
    have : Real.exp (-u) < Real.exp u := Real.exp_lt_exp.2 (by linarith)
    linarith
  rw [e1, e2, e3]
  field_simp
  have : Real.exp u = (Real.exp (-u))⁻¹ := by rw [← Real.exp_neg, neg_neg]
  rw [this]
  have hx4 : 1 - Real.exp (-u) ^ 2 ≠ 0 := by nlinarith
  have hx5 : (Real.exp (-u))⁻¹ - Real.exp (-u) ≠ 0 := by rw [← this]; exact h5
  field_simp

theorem phiA_integrable (hp : Probe a g) : IntegrableOn (phiA g) (Ioi 0) := by
  have h : IntegrableOn (fun u => phiA g (2 * u)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hp.arch.div_const 2) (fun u hu => ?_) measurableSet_Ioi
    rw [← phiA_two_mul g hu]; ring
  simpa using (integrableOn_Ioi_comp_mul_left_iff (phiA g) 0 (by norm_num : (0 : ℝ) < 2)).1 h

theorem phiA_integral (g : ℝ → ℝ) : ∫ t in Ioi (0 : ℝ), phiA g t = archE g := by
  have e := integral_comp_mul_left_Ioi (phiA g) 0 (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero, smul_eq_mul] at e
  have e2 : ∫ x in Ioi (0 : ℝ), phiA g (2 * x) = (∫ u in Ioi (0 : ℝ), archIntegrand g u) / 2 := by
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [← phiA_two_mul g hu]; ring
  rw [archE]
  linarith

/-- **B2**: `∫ ĝ(r)² (Re ψ(¼ + ir/2) − Re ψ(¼)) dr = 2π·E(g)`, integrably. -/
theorem hsq_psi_sub (hp : Probe a g) (ha : 0 < a) (hD : DigammaDiff) :
    Integrable (fun r => hsq g a r * (psiRe r - psiRe 0)) ∧
      ∫ r, hsq g a r * (psiRe r - psiRe 0) = 2 * π * archE g := by
  set ν := volume.restrict (Ioi (0 : ℝ))
  set F : ℝ × ℝ → ℝ := fun p => hsq g a p.1 * (kk p.2 * (1 - Real.cos (p.1 * (p.2 / 2)))) with hFd
  have hFm : AEStronglyMeasurable F (volume.prod ν) := by
    refine Measurable.aestronglyMeasurable ?_
    refine ((continuous_hsq hp.toE).measurable.comp measurable_fst).mul
      ((measurable_kk.comp measurable_snd).mul ?_)
    exact (Continuous.measurable (by fun_prop))
  have hinner : ∀ t, ∫ r, F (r, t) = 2 * π * phiA g t := by
    intro t
    have e : (fun r => F (r, t))
        = fun r => kk t * (hsq g a r - hsq g a r * Real.cos (r * (t / 2))) := by
      funext r; simp only [hFd]; ring
    rw [e, integral_const_mul, integral_sub (integrable_hsq hp.toE ha) (integrable_hsq_cos hp.toE ha _),
      integral_hsq hp.toE ha, integral_hsq_cos hp.toE ha, ← autocorr_zero, phiA]
    ring
  have hFint : ∀ t, Integrable (fun r => F (r, t)) := by
    intro t
    have e : (fun r => F (r, t))
        = fun r => kk t * (hsq g a r - hsq g a r * Real.cos (r * (t / 2))) := by
      funext r; simp only [hFd]; ring
    rw [e]; exact ((integrable_hsq hp.toE ha).sub (integrable_hsq_cos hp.toE ha _)).const_mul _
  have hFnn : ∀ r, ∀ t, 0 < t → 0 ≤ F (r, t) := fun r t ht =>
    mul_nonneg (hsq_nonneg r) (mul_nonneg (kk_nonneg ht) (by linarith [Real.cos_le_one (r * (t / 2))]))
  have hF : Integrable F (volume.prod ν) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨Eventually.of_forall hFint, ?_⟩
    refine ((phiA_integrable hp).const_mul (2 * π)).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    show 2 * π * phiA g t = ∫ r, ‖F (r, t)‖
    rw [← hinner t]
    congr 1; funext r
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn r t ht)]
  have hG : ∀ r, ∫ t, F (r, t) ∂ν = hsq g a r * (psiRe r - psiRe 0) := by
    intro r
    simp only [hFd, ν]
    rw [integral_const_mul, (psiRe_sub hD r).2]
  have hGi := hF.integral_prod_left
  simp only [hG] at hGi
  refine ⟨hGi, ?_⟩
  calc ∫ r, hsq g a r * (psiRe r - psiRe 0) = ∫ r, ∫ t, F (r, t) ∂ν := by simp only [hG]
    _ = ∫ t, (∫ r, F (r, t)) ∂ν := integral_integral_swap (f := fun r t => F (r, t)) hF
    _ = ∫ t in Ioi (0 : ℝ), 2 * π * phiA g t := by simp only [hinner, ν]
    _ = 2 * π * archE g := by rw [integral_const_mul, phiA_integral g]

/-- `(1/2π)∫ ĝ² Re ψ(¼ + ir/2) = Re ψ(¼)‖g‖² + E(g)`. -/
theorem arch_term (hp : Probe a g) (ha : 0 < a) (hD : DigammaDiff) :
    1 / (2 * π) * ∫ r, hsq g a r * psiRe r = psiRe 0 * normSq g + archE g := by
  obtain ⟨hi, he⟩ := hsq_psi_sub hp ha hD
  have e : (fun r => hsq g a r * psiRe r)
      = fun r => hsq g a r * (psiRe r - psiRe 0) + psiRe 0 * hsq g a r := by
    funext r; ring
  rw [e, integral_add hi ((integrable_hsq hp.toE ha).const_mul _), he, integral_const_mul,
    integral_hsq hp.toE ha]
  field_simp
  ring

/-! ## B3. The bridge -/

/-- `WeilExplicit`'s first conjunct for `h = ĝ²`. -/
theorem hsq_ofReal (hp : Probe a g) (ha : 0 ≤ a) (r : ℝ) :
    ghatC g a r ^ 2 = ((hsq g a r : ℝ) : ℂ) := by
  rw [ghatC_real hp.toE ha, hsq]; push_cast; rfl

/-- **The explicit-formula bridge**: for an even probe `g`, Weil's explicit formula for `h = ĝ²`
(and Gauss's digamma integral) gives `Σ_ρ ĝ(t_ρ)² = weilQ a g`. -/
theorem weilQ_eq_zero_sum {ι : Type*} {ρ : ι → ℂ} (hp : Probe a g) (ha : 0 < a)
    (hEF : WeilExplicit ρ (fun z => ghatC g a z ^ 2) (hsq g a)) (hD : DigammaDiff) :
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
  rw [hpole1, hpole2, hg0, hpr, arch_term hp ha hD, hz0, weilQ_eq', weilConst]
  push_cast; ring

/-- The same, as the zero-sum identity `weilQ a g = Σ_ρ ĝ(t_ρ)²`. -/
theorem weilQ_eq_tsum {ι : Type*} {ρ : ι → ℂ} (hp : Probe a g) (ha : 0 < a)
    (hEF : WeilExplicit ρ (fun z => ghatC g a z ^ 2) (hsq g a)) (hD : DigammaDiff) :
    (weilQ a g : ℂ) = ∑' i, ghatC g a ((ρ i - 1 / 2) / Complex.I) ^ 2 :=
  (weilQ_eq_zero_sum hp ha hEF hD).tsum_eq.symm

/-! ## C. The symbol form and the jump form

With `DigammaDiff` alone (no `WeilExplicit`), Weil's form is a rank-one pole term plus a Toeplitz
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
theorem psiRe_ge (hD : DigammaDiff) (r : ℝ) : psiRe 0 ≤ psiRe r := by
  obtain ⟨-, he⟩ := psiRe_sub hD r
  have : 0 ≤ ∫ t in Ioi (0 : ℝ), kk t * (1 - Real.cos (r * (t / 2))) :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (kk_nonneg ht) (by linarith [Real.cos_le_one (r * (t / 2))])
  linarith

theorem integrable_hsq_psi (hp : Probe a g) (ha : 0 < a) (hD : DigammaDiff) :
    Integrable (fun r => hsq g a r * psiRe r) := by
  obtain ⟨hi, -⟩ := hsq_psi_sub hp ha hD
  refine (hi.add ((integrable_hsq hp.toE ha).const_mul (psiRe 0))).congr
    (Eventually.of_forall fun r => ?_)
  simp only [Pi.add_apply]; ring

/-- **The symbol form**: `Q(g) = 2ĝ(i/2)² + (1/2π)∫ĝ(r)²σ_a(r) dr`, given `DigammaDiff`. -/
theorem weilQ_symbol (hp : Probe a g) (ha : 0 < a) (hD : DigammaDiff) :
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
    (integrable_hsq_psi hp ha hD).sub ((integrable_hsq hp.toE ha).const_mul _)
  have i2 : Integrable (fun r => 2 * ∑ n ∈ S, c n * (hsq g a r * Real.cos (r * Real.log n))) :=
    hsum.const_mul 2
  rw [e, integral_sub i1 i2,
    integral_sub (integrable_hsq_psi hp ha hD) ((integrable_hsq hp.toE ha).const_mul _),
    integral_const_mul, integral_const_mul, integral_finsetSum S hI]
  have hprime : ∑ n ∈ S, ∫ r, c n * (hsq g a r * Real.cos (r * Real.log n))
      = 2 * π * primeS g := by
    unfold primeS; rw [prime_sum_eq hp.supp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, integral_hsq_cos hp.toE ha]; ring
  have harch := arch_term hp ha hD
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

end Pilot1ca

#print axioms Pilot1ca.psiRe_sub
#print axioms Pilot1ca.hsq_psi_sub
#print axioms Pilot1ca.arch_term
#print axioms Pilot1ca.hsq_ofReal
#print axioms Pilot1ca.weilQ_eq_zero_sum
#print axioms Pilot1ca.weilQ_eq_tsum
#print axioms Pilot1ca.psiRe_ge
#print axioms Pilot1ca.weilQ_symbol
#print axioms Pilot1ca.weilQ0_jump
