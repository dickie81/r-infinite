import Mathlib
import UniquenessQ

/-! # The zero-swap lemma: a simple ground state has zeros only on `ℝ ∪ iℝ`

Let `g` be a ground state of Weil's form at half-support `a`, **simple**: every element of the
ground-state space is an a.e. multiple of `g`. Let `w` be a zero of `ĝ` with `σ = w²` non-real. The
swap `F₂(z) = ĝ(z)·(z² − σ̄)/(z² − σ)` keeps `|F₂| = |ĝ|` on `ℝ` (there `z²` is real) and at the pole
point `i/2` (there `z² = −¼` is real). If `F₂ = û + iv̂` for probes `u, v` whose autocorrelations add
up to `g`'s (**`SwapRealization`**), then `Q(u) + Q(v) = Q(g)` and `‖u‖² + ‖v‖² = ‖g‖²`. Since
`Q ≥ λ₁‖·‖²` on each, both `u` and `v` lie in the ground-state space, so by simplicity they are
multiples `αg`, `βg`. Then `(z² − σ̄)/(z² − σ) = α + iβ` at every real `t` with `ĝ(t) ≠ 0`. Two such
`t` with different squares exist (Parseval and continuity), and that forces `σ = σ̄`.

`zero_swap_false` proves this with no further assumption. `zeros_real_or_imag` packages it: under
simplicity, and given the realisation for each off-cross zero, every zero `w` of `ĝ` has
`w.re = 0 ∨ w.im = 0`.

**Named input.** `SwapRealization` is the analytic step. `F₂` is entire of exponential type `a` and
square-integrable on `ℝ`, so by Paley–Wiener it is the transform of a complex `f₂ ∈ L²[−a, a]`, even
because `F₂` is. `u = Re f₂` and `v = Im f₂` are the probes. The autocorrelation identity is Fourier
uniqueness: `|F₂|² = |ĝ|²` on `ℝ` is the transform of `f₂ ⋆ f̃₂* = autocorr u + autocorr v`, whose odd
imaginary part vanishes. Neither Paley–Wiener nor this form of Fourier uniqueness is in Mathlib; both
are standard. The admissibility of `u, v` (the archimedean integral) is part of the input.

This is an even-sector variant of Carathéodory–Fejér's argument. Connes–van Suijlekom (arXiv
2511.23257) prove the stronger conclusion (all zeros real) under global simplicity with an even
eigenfunction.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## Small lemmas -/

theorem normSq_eq_autocorr (g : ℝ → ℝ) : normSq g = autocorr g 0 := by
  unfold normSq autocorr
  congr 1; funext t; rw [add_zero]; ring

theorem ghatC_smul (c : ℝ) (g : ℝ → ℝ) (a : ℝ) (z : ℂ) :
    ghatC (fun t => c * g t) a z = c * ghatC g a z := by
  unfold ghatC
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext u; push_cast; ring

theorem ghatC_congr_ae {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') (a : ℝ) (z : ℂ) :
    ghatC g a z = ghatC g' a z := by
  unfold ghatC
  apply intervalIntegral.integral_congr_ae
  filter_upwards [h] with u hu
  intro _
  rw [hu]

/-- For a probe, `ĝ(z)` is the integral over the whole line. -/
theorem ghatC_eq_integral {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hsupp : ∀ u, a < |u| → g u = 0)
    (z : ℂ) : ghatC g a z = ∫ u, ((g u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u) := by
  unfold ghatC
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro u hu
  have h : a < |u| := by
    by_contra h'
    push Not at h'
    exact hu ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  rw [hsupp u h]; simp

/-- **`ĝ` is not identically zero on `ℝ`** for a normalised probe: otherwise every Fourier
coefficient on `[−2a, 2a]` vanishes, and Parseval gives `‖g‖² = 0`. -/
theorem exists_real_ghatC_ne {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) : ∃ t : ℝ, ghatC g a t ≠ 0 := by
  by_contra H
  push Not at H
  have hcf : ∀ n : ℤ, cf a g n = 0 := by
    intro n
    have hs : ∀ u, a < |u| →
        Complex.exp (-(2 * π * I * n * u / (4 * a))) * ((g u : ℝ) : ℂ) = 0 :=
      fun u hu => by rw [hp.supp u hu]; simp
    unfold cf
    rw [integral_eq_of_supp hs (by linarith) (by linarith)]
    have h0 := H (-(2 * π * n / (4 * a)))
    rw [ghatC_eq_integral ha hp.supp] at h0
    have : (∫ u : ℝ, Complex.exp (-(2 * π * I * n * u / (4 * a))) * ((g u : ℝ) : ℂ))
        = ∫ u : ℝ, ((g u : ℝ) : ℂ) * Complex.exp (Complex.I * (((-(2 * π * n / (4 * a)) : ℝ)) : ℂ) * u) := by
      congr 1; funext u; rw [mul_comm]; congr 2; push_cast; ring
    rw [this, h0, mul_zero]
  have hsum := hasSum_cf_sq ha (by linarith : a < 2 * a) hp.memL2 hp.supp
  have h0 : HasSum (fun n : ℤ => ‖cf a g n‖ ^ 2) 0 := by
    simp only [hcf, norm_zero]; norm_num
  have := hsum.unique h0
  rw [hn, mul_one] at this
  have : (0 : ℝ) < (4 * a)⁻¹ := by positivity
  linarith

/-! ## The swap -/

/-- A ground state is **simple** when the ground-state space is spanned by it (up to a.e.). -/
def SimpleGround (a : ℝ) (g : ℝ → ℝ) : Prop :=
  IsGroundState a g ∧ ∀ h ∈ groundSpace a, ∃ c : ℝ, h =ᵐ[volume] fun t => c * g t

/-- **Named analytic input.** The swapped transform `ĝ(z)(z² − σ̄)/(z² − σ)` is `û + iv̂` for probes
`u, v`, and their autocorrelations add up to `g`'s (Paley–Wiener and Fourier uniqueness). -/
def SwapRealization (a : ℝ) (g : ℝ → ℝ) (σ : ℂ) : Prop :=
  ∃ u v : ℝ → ℝ, Probe a u ∧ Probe a v ∧
    (∀ z : ℂ, z ^ 2 ≠ σ →
      ghatC u a z + Complex.I * ghatC v a z
        = ghatC g a z * ((z ^ 2 - (starRingEnd ℂ) σ) / (z ^ 2 - σ))) ∧
    (∀ x, autocorr u x + autocorr v x = autocorr g x)

theorem sq_ne_of_im {σ : ℂ} (hσ : σ.im ≠ 0) (t : ℝ) : ((t : ℂ)) ^ 2 ≠ σ := by
  intro h; apply hσ; rw [← h, ← ofReal_pow, ofReal_im]

/-- The pole value is preserved: `ĝ(i/2)` changes by a unimodular factor. -/
theorem poleR_swap {a : ℝ} {g u v : ℝ → ℝ} {σ : ℂ} (hσ : σ.im ≠ 0)
    (hB : ∀ z : ℂ, z ^ 2 ≠ σ →
      ghatC u a z + Complex.I * ghatC v a z
        = ghatC g a z * ((z ^ 2 - (starRingEnd ℂ) σ) / (z ^ 2 - σ))) :
    poleR u a ^ 2 + poleR v a ^ 2 = poleR g a ^ 2 := by
  have hq : (Complex.I / 2) ^ 2 = (((-1 / 4 : ℝ)) : ℂ) := by
    rw [div_pow, I_sq]; push_cast; ring
  have hz : (Complex.I / 2) ^ 2 ≠ σ := by rw [hq]; exact fun e => hσ (by rw [← e, ofReal_im])
  have h := hB _ hz
  rw [ghatC_I_div_two, ghatC_I_div_two, ghatC_I_div_two, hq] at h
  set r : ℂ := (((-1 / 4 : ℝ)) : ℂ)
  have hden : r - σ ≠ 0 := sub_ne_zero.2 fun e => hσ (by rw [← e]; simp only [r, ofReal_im])
  have hconj : r - (starRingEnd ℂ) σ = (starRingEnd ℂ) (r - σ) := by
    simp only [r, map_sub, Complex.conj_ofReal]
  have hn := congrArg Complex.normSq h
  rw [mul_comm Complex.I, Complex.normSq_add_mul_I, Complex.normSq_mul, Complex.normSq_div,
    hconj, Complex.normSq_conj, div_self (by rwa [Ne, Complex.normSq_eq_zero]),
    Complex.normSq_ofReal, mul_one] at hn
  rw [hn]; ring

/-- **The zero-swap lemma, core.** A simple ground state admits no realised swap of a zero with
non-real square. -/
theorem zero_swap_false {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hs : SimpleGround a g) {σ : ℂ}
    (hσ : σ.im ≠ 0) (hR : SwapRealization a g σ) : False := by
  obtain ⟨hgs, hsimp⟩ := hs
  obtain ⟨u, v, hu, hv, hB, hac⟩ := hR
  have hgq : weilQ a g = lam a * normSq g := ((isGroundState_iff ha).1 hgs).1.2
  -- the three pieces of `Q` add up
  have hN : normSq u + normSq v = normSq g := by
    rw [normSq_eq_autocorr, normSq_eq_autocorr, normSq_eq_autocorr]; exact hac 0
  have hP := poleR_swap hσ hB
  have hA : archE u + archE v = archE g := by
    unfold archE
    rw [← integral_add hu.arch hv.arch]
    congr 1; funext x
    unfold archIntegrand
    linear_combination (Real.exp (x / 2) / Real.sinh x) * (hac 0 - hac x)
  have hS : primeS u + primeS v = primeS g := by
    unfold primeS
    rw [prime_sum_eq hu.supp, prime_sum_eq hv.supp, prime_sum_eq hgs.1.supp,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    linear_combination (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * hac (Real.log n)
  have hQ : weilQ a u + weilQ a v = weilQ a g := by
    simp only [weilQ_eq']
    linear_combination 2 * hP + weilConst * hN + hA - 2 * hS
  -- so `u` and `v` are ground-state directions
  have ru := lam_mul_le hu
  have rv := lam_mul_le hv
  have hsplit : lam a * normSq g = lam a * normSq u + lam a * normSq v := by rw [← hN]; ring
  have eu : weilQ a u = lam a * normSq u := by linarith
  have ev : weilQ a v = lam a * normSq v := by linarith
  obtain ⟨α, hα⟩ := hsimp u ⟨hu, eu⟩
  obtain ⟨β, hβ⟩ := hsimp v ⟨hv, ev⟩
  -- the multiplier is the constant `α + iβ` wherever `ĝ ≠ 0` on `ℝ`
  set c : ℂ := (α : ℂ) + Complex.I * β
  set B : ℂ → ℂ := fun z => (z ^ 2 - (starRingEnd ℂ) σ) / (z ^ 2 - σ)
  have key : ∀ t : ℝ, ghatC g a t ≠ 0 → c = B t := by
    intro t ht
    have h := hB t (sq_ne_of_im hσ t)
    rw [ghatC_congr_ae hα, ghatC_smul, ghatC_congr_ae hβ, ghatC_smul] at h
    apply mul_left_cancel₀ ht
    rw [← h]; simp only [c]; ring
  -- two real points with `ĝ ≠ 0` and different squares
  obtain ⟨t₁, h₁⟩ := exists_real_ghatC_ne ha hgs.1 hgs.2.1
  have hcont : Continuous fun t : ℝ => ghatC g a t :=
    (ghatC_differentiable (probe_integrable hgs.1).intervalIntegrable).continuous.comp
      continuous_ofReal
  have hopen : IsOpen {t : ℝ | ghatC g a t ≠ 0} := hcont.isOpen_preimage _ isOpen_compl_singleton
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen t₁ h₁
  obtain ⟨t₂, ht₂, hsq⟩ : ∃ t₂ : ℝ, ghatC g a t₂ ≠ 0 ∧ t₁ ^ 2 < t₂ ^ 2 := by
    by_cases h0 : 0 ≤ t₁
    · refine ⟨t₁ + ε / 2, hball ?_, by nlinarith⟩
      rw [Metric.mem_ball, Real.dist_eq, show t₁ + ε / 2 - t₁ = ε / 2 by ring,
        abs_of_pos (by linarith)]
      linarith
    · have h0' : t₁ < 0 := not_le.mp h0
      refine ⟨t₁ - ε / 2, hball ?_, by nlinarith⟩
      rw [Metric.mem_ball, Real.dist_eq, show t₁ - ε / 2 - t₁ = -(ε / 2) by ring, abs_neg,
        abs_of_pos (by linarith)]
      linarith
  have c1 := key t₁ h₁
  have c2 := key t₂ ht₂
  have hd1 : ((t₁ : ℂ)) ^ 2 - σ ≠ 0 := sub_ne_zero.2 (sq_ne_of_im hσ t₁)
  have hd2 : ((t₂ : ℂ)) ^ 2 - σ ≠ 0 := sub_ne_zero.2 (sq_ne_of_im hσ t₂)
  have heq : B t₁ = B t₂ := c1.symm.trans c2
  simp only [B] at heq
  rw [div_eq_div_iff hd1 hd2] at heq
  have hprod : (((t₂ ^ 2 - t₁ ^ 2 : ℝ)) : ℂ) * (σ - (starRingEnd ℂ) σ) = 0 := by
    push_cast; linear_combination heq
  rcases mul_eq_zero.1 hprod with h | h
  · rw [ofReal_eq_zero] at h; linarith
  · rw [Complex.sub_conj] at h
    apply hσ
    have := congrArg Complex.im h
    simp at this
    exact this

/-- **Zeros of a simple ground state lie on `ℝ ∪ iℝ`**, given the swap realisation (Paley–Wiener)
for every zero off that cross. -/
theorem zeros_real_or_imag {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hs : SimpleGround a g)
    (hPW : ∀ w : ℂ, ghatC g a w = 0 → (w ^ 2).im ≠ 0 → SwapRealization a g (w ^ 2)) :
    ∀ w : ℂ, ghatC g a w = 0 → w.re = 0 ∨ w.im = 0 := by
  intro w hw
  by_contra hne
  push Not at hne
  have him : (w ^ 2).im ≠ 0 := by
    rw [sq, Complex.mul_im]
    have := mul_ne_zero hne.1 hne.2
    intro h; apply this; linarith
  exact zero_swap_false ha hs him (hPW w hw him)

end Pilot1ca

#print axioms Pilot1ca.exists_real_ghatC_ne
#print axioms Pilot1ca.poleR_swap
#print axioms Pilot1ca.zero_swap_false
#print axioms Pilot1ca.zeros_real_or_imag
