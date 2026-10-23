/-
# Round 684: their `Σ_II` expanded, and their `Σ₂` by Poisson summation (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li continue the proof of their Lemma 8.2: "We write out f̂_b as an integral, expand out the square and bring
the summation over n and integration over τ on the inside to get" (lines 3522–3523; spaces restored, the hat and
subscript transcribed) `Σ_II = ∫∫Σ_{m₂,m₂′}Σ_{b,b′}m₂m₂′f_b(u)f_{b′}(u′)Σ₁Σ₂ du′ du` (transcribed), with
`Σ₂ = Σ_{n∈ℤ}ψ₂(M₂n/(qT))e_q((m₂′u′ − m₂u + b′m₂′ − bm₂)n)`, and "By Poisson summation and the rapid decay of the
Fourier transform ψ̂₂, we have" (lines 3563–3564; spaces restored, the hat and subscript transcribed). This file proves
that expansion for round 683's `Φ(n, τ)` under the weight `ψ̃₀(n/N₀)`, and that Poisson step.

The stack's form.
* Their weight `ψ₂(M₂n/(qT))` is `ψ̃₀(n/N₀)` (round 656's bump `psi0`), and the sum over `n` runs over round 680's
  `P3 N₀`, off which, for `N₀ > 0`, the weight vanishes.
* Their `Σ₁ ⪅ 1` is not used: the factor `e((τ/L)(m₂′u′ − m₂u))` has absolute value `1`.
* The expansion is an inequality, `Σ_nψ̃₀(n/N₀)|Φ(n, τ)|² ≤ Σ_{p,p′}|Σ_nψ̃₀(n/N₀)z_{n,p}conj(z_{n,p′})|`
  (`sum_mul_norm_sq_le`), and each pair is bounded through the iterated integral `∫f_b(u)∫f_{b′}(u′)… du′ du` against
  a majorant `H` of the inner integral (`norm_sum_fourier_pair_le`), so no integral of an integral needs to be
  measurable.
* Their `Σ₂` is `S₂(k₀, x) = Σ_{n∈P3 N₀}ψ̃₀(n/N₀)e_q(−nk₀)e(nx)` (`S2`), with `k₀ = bm₂ − b′m₂′ ∈ ℤ/qℤ` and
  `x = (m₂′u′ − m₂u)/q`; Poisson summation is round 680's `poisson_residue` with modulus `1`.
* Their "rapid decay" of `ψ̂₂` is `(1 + |y|)^K|ψ̂₀(y)| ≤ C_K` (`norm_fourier_psiC_le_CK`).

Plain statements, with `q ≥ 1` (`[NeZero q]`), `e(x) = e^{2πix}`, `e_q` Mathlib's `ZMod.stdAddChar` and `Φ(n, τ)`
round 683's `LinnikCGLCov.Phi`.
* `sum_mul_norm_sq_le`: for real weights `w_n`,
  `Σ_{n∈N}w_n|Σ_{p∈Q}z_{n,p}|² ≤ Σ_{p,p′∈Q}|Σ_{n∈N}w_nz_{n,p}conj(z_{n,p′})|`.
* `norm_sum_fourier_pair_le`: for integrable `f, g ≥ 0` and `H` with `fH` integrable and
  `∫g(u′)|Σ_nc_ne(y_nu′ − x_nu)| du′ ≤ H(u)` wherever `f(u) ≠ 0`, `|Σ_nc_nf̂(x_n)conj(ĝ(y_n))| ≤ ∫f(u)H(u) du`.
* `S2`, `sum_psi_norm_Phi_sq_le`: for smooth `f_b ≥ 0` that are `0` for `|u| > A`, and `H` with, for
  `m₂, m₂′ ∈ P2 M₂`, `f_bH` integrable and `∫f_{b′}(u′)|S₂(bm₂ − b′m₂′, (m₂′u′ − m₂u)/q)| du′ ≤ H(b, m₂, b′, m₂′, u)`
  wherever `f_b(u) ≠ 0`,
  `Σ_{n∈P3 N₀}ψ̃₀(n/N₀)|Φ(n, τ)|² ≤ Σ_{b,m₂,b′,m₂′}m₂m₂′∫f_b(u)H(b, m₂, b′, m₂′, u) du` for every `τ`.
* `S2_eq_tsum`, `norm_S2_le`: for `N₀ > 0`, `S₂(k₀, x) = Σ_{k∈ℤ}N₀ψ̂₀(N₀(k − x + k₀/q))` with `k₀` read as its value in
  `{0, …, q − 1}`, so `|S₂(k₀, x)| ≤ N₀Σ_k|ψ̂₀(N₀(k − x + k₀/q))|`.
* `CK`, `norm_fourier_psiC_le_CK`: `(1 + |y|)^K|ψ̂₀(y)| ≤ C_K = 2^K(∫ψ̃₀ + D_K/(2π)^K)`.

The file imports `LinnikCGLCov.lean`.
-/

import LinnikCGLCov

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLSig2

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLSep LinnikCGLRFact LinnikCGLRam LinnikCGLJ LinnikCGLG
  LinnikCGLPois8 LinnikCGLCount LinnikCGLAsum LinnikCGLNsum LinnikCGLN0 LinnikCGLCov

/-! ### Expanding the square -/

/-- **Expanding a weighted square**: for real weights `w_n`,
`Σ_{n∈N}w_n|Σ_{p∈Q}z_{n,p}|² ≤ Σ_{p,p′∈Q}|Σ_{n∈N}w_nz_{n,p}conj(z_{n,p′})|`. -/
lemma sum_mul_norm_sq_le {ι κ : Type*} (N : Finset ι) (Q : Finset κ) (w : ι → ℝ) (z : ι → κ → ℂ) :
    ∑ n ∈ N, w n * ‖∑ p ∈ Q, z n p‖ ^ 2 ≤
      ∑ p ∈ Q, ∑ p' ∈ Q, ‖∑ n ∈ N, (w n : ℂ) * z n p * conj (z n p')‖ := by
  have hsq : ∀ v : ℂ, (‖v‖ ^ 2 : ℝ) = (v * conj v).re := by
    intro v; rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hexp : ∀ n, (w n : ℂ) * ((∑ p ∈ Q, z n p) * conj (∑ p ∈ Q, z n p)) =
      ∑ p ∈ Q, ∑ p' ∈ Q, (w n : ℂ) * z n p * conj (z n p') := by
    intro n
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p' _ => ?_
    ring
  calc ∑ n ∈ N, w n * ‖∑ p ∈ Q, z n p‖ ^ 2
      = (∑ n ∈ N, (w n : ℂ) * ((∑ p ∈ Q, z n p) * conj (∑ p ∈ Q, z n p))).re := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.re_ofReal_mul, hsq]
    _ = (∑ p ∈ Q, ∑ p' ∈ Q, ∑ n ∈ N, (w n : ℂ) * z n p * conj (z n p')).re := by
        simp_rw [hexp]
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ‖∑ p ∈ Q, ∑ p' ∈ Q, ∑ n ∈ N, (w n : ℂ) * z n p * conj (z n p')‖ := Complex.re_le_norm _
    _ ≤ ∑ p ∈ Q, ∑ p' ∈ Q, ‖∑ n ∈ N, (w n : ℂ) * z n p * conj (z n p')‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => norm_sum_le _ _)

/-! ### A pair of Fourier transforms -/

/-- **A pair of Fourier transforms as an iterated integral**: for integrable `f, g ≥ 0`, coefficients `c_n`, points
`x_n, y_n`, and `H` with `fH` integrable and `∫g(u′)|Σ_nc_ne(y_nu′ − x_nu)| du′ ≤ H(u)` wherever `f(u) ≠ 0`,
`|Σ_nc_nf̂(x_n)conj(ĝ(y_n))| ≤ ∫f(u)H(u) du`. -/
lemma norm_sum_fourier_pair_le {N : Finset ℤ} (c : ℤ → ℂ) (x y : ℤ → ℝ) {f g H : ℝ → ℝ}
    (hfi : Integrable f) (hgi : Integrable g) (hf0 : ∀ u, 0 ≤ f u) (hg0 : ∀ u, 0 ≤ g u)
    (hH : Integrable fun u => f u * H u)
    (hb : ∀ u, f u ≠ 0 →
      ∫ u', g u' * ‖∑ n ∈ N, c n * cexp (2 * π * I * ((y n * u' - x n * u : ℝ) : ℂ))‖ ≤ H u) :
    ‖∑ n ∈ N, c n * 𝓕 (fun u => (f u : ℂ)) (x n) * conj (𝓕 (fun u => (g u : ℂ)) (y n))‖ ≤
      ∫ u, f u * H u := by
  have hfC : Integrable fun u => (f u : ℂ) := hfi.ofReal
  have hgC : Integrable fun u => (g u : ℂ) := hgi.ofReal
  have hF : ∀ w : ℝ, 𝓕 (fun u => (f u : ℂ)) w = ∫ u : ℝ, cexp (↑(-2 * π * u * w) * I) * (f u : ℂ) := by
    intro w; rw [Real.fourier_real_eq_integral_exp_smul]; simp only [smul_eq_mul]
  -- `conj(ĝ(y)) = ∫g(v)e(vy) dv`
  have hG : ∀ w : ℝ, conj (𝓕 (fun u => (g u : ℂ)) w) =
      ∫ v : ℝ, cexp (2 * π * I * ((v : ℂ) * w)) * (g v : ℂ) := by
    intro w
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
    congr 1; funext v
    rw [smul_eq_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    congr 2
    push_cast; ring
  have hphase : ∀ (n : ℤ) (u v : ℝ), ‖cexp (2 * π * I * ((y n * v - x n * u : ℝ) : ℂ))‖ = 1 := by
    intro n u v
    rw [show (2 * π * I * ((y n * v - x n * u : ℝ) : ℂ)) = ↑(2 * π * (y n * v - x n * u)) * I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  -- the inner integral, for each `u`
  have hinner : ∀ u : ℝ, ∑ n ∈ N, c n * cexp (↑(-2 * π * u * x n) * I) * conj (𝓕 (fun u => (g u : ℂ)) (y n)) =
      ∫ v : ℝ, (g v : ℂ) * ∑ n ∈ N, c n * cexp (2 * π * I * ((y n * v - x n * u : ℝ) : ℂ)) := by
    intro u
    have hint : ∀ n ∈ N, Integrable fun v : ℝ =>
        (g v : ℂ) * (c n * cexp (2 * π * I * ((y n * v - x n * u : ℝ) : ℂ))) := by
      intro n _
      refine hgC.mul_bdd (c := ‖c n‖) (Continuous.aestronglyMeasurable (by fun_prop))
        (Eventually.of_forall fun v => le_of_eq ?_)
      rw [norm_mul, hphase, mul_one]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hG, ← integral_const_mul]
    congr 1; funext v
    rw [show (2 * π * I * ((y n * v - x n * u : ℝ) : ℂ)) =
      ↑(-2 * π * u * x n) * I + 2 * π * I * ((v : ℂ) * y n) by push_cast; ring, Complex.exp_add]
    ring
  -- the outer integral
  have houter : ∑ n ∈ N, c n * 𝓕 (fun u => (f u : ℂ)) (x n) * conj (𝓕 (fun u => (g u : ℂ)) (y n)) =
      ∫ u : ℝ, (f u : ℂ) * ∫ v : ℝ, (g v : ℂ) * ∑ n ∈ N, c n * cexp (2 * π * I * ((y n * v - x n * u : ℝ) : ℂ)) := by
    have hint : ∀ n ∈ N, Integrable fun u : ℝ =>
        (f u : ℂ) * (c n * cexp (↑(-2 * π * u * x n) * I) * conj (𝓕 (fun u => (g u : ℂ)) (y n))) := by
      intro n _
      refine hfC.mul_bdd (c := ‖c n‖ * ‖conj (𝓕 (fun u => (g u : ℂ)) (y n))‖)
        (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun u => le_of_eq ?_)
      rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have e1 : ∀ n, c n * 𝓕 (fun u => (f u : ℂ)) (x n) * conj (𝓕 (fun u => (g u : ℂ)) (y n)) =
        ∫ u : ℝ, (f u : ℂ) * (c n * cexp (↑(-2 * π * u * x n) * I) * conj (𝓕 (fun u => (g u : ℂ)) (y n))) := by
      intro n
      rw [hF, ← integral_const_mul, ← integral_mul_const]
      congr 1; funext u; ring
    simp_rw [e1]
    rw [← integral_finsetSum _ hint]
    congr 1; funext u
    rw [← Finset.mul_sum, hinner u]
  rw [houter]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) hH
    (Eventually.of_forall fun u => ?_)
  beta_reduce
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 u)]
  by_cases hfu : f u = 0
  · rw [hfu, zero_mul, zero_mul]
  refine mul_le_mul_of_nonneg_left ?_ (hf0 u)
  have hint2 : Integrable fun v : ℝ => g v * ‖∑ n ∈ N, c n * cexp (2 * π * I * ((y n * v - x n * u : ℝ) : ℂ))‖ := by
    refine hgi.mul_bdd (c := ∑ n ∈ N, ‖c n‖)
      (continuous_finsetSum _ fun n _ => by fun_prop).norm.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_norm]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => le_of_eq ?_)
    rw [norm_mul, hphase, mul_one]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono_of_nonneg
    (Eventually.of_forall fun v => norm_nonneg _) hint2 (Eventually.of_forall fun v => le_of_eq ?_)).trans (hb u hfu))
  beta_reduce
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 v)]

/-! ### Their `Σ_II`, expanded -/

/-- Their `Σ₂` before Poisson summation: `S₂(k₀, x) = Σ_{n∈P3 N₀}ψ̃₀(n/N₀)e_q(−nk₀)e(nx)`. -/
def S2 (q : ℕ) [NeZero q] (N₀ : ℝ) (k₀ : ZMod q) (x : ℝ) : ℂ :=
  ∑ n ∈ P3 N₀, ((psi0 (n / N₀) : ℝ) : ℂ) * ZMod.stdAddChar (-((n : ZMod q) * k₀)) * cexp (2 * π * I * (n * x))

/-- **Their `Σ_II`, expanded**: for `q ≥ 1`, smooth `f_b ≥ 0` that are `0` for `|u| > A`, and `H` with, for
`m₂, m₂′ ∈ P2 M₂`, `f_bH` integrable and `∫f_{b′}(u′)|S₂(bm₂ − b′m₂′, (m₂′u′ − m₂u)/q)| du′ ≤ H(b, m₂, b′, m₂′, u)`
wherever `f_b(u) ≠ 0`, `Σ_{n∈P3 N₀}ψ̃₀(n/N₀)|Φ(n, τ)|² ≤ Σ_{b,m₂,b′,m₂′}m₂m₂′∫f_b(u)H(b, m₂, b′, m₂′, u) du` for
every `τ`. -/
theorem sum_psi_norm_Phi_sq_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) (hf : ∀ b u, 0 ≤ f b u) (M₂ L N₀ τ : ℝ)
    (H : (ZMod q)ˣ → ℤ → (ZMod q)ˣ → ℤ → ℝ → ℝ)
    (hH : ∀ (b : (ZMod q)ˣ), ∀ m₂ ∈ P2 M₂, ∀ (b' : (ZMod q)ˣ), ∀ m₂' ∈ P2 M₂,
      Integrable fun u => f b u * H b m₂ b' m₂' u)
    (hb : ∀ (b : (ZMod q)ˣ), ∀ m₂ ∈ P2 M₂, ∀ (b' : (ZMod q)ˣ), ∀ m₂' ∈ P2 M₂, ∀ u : ℝ, f b u ≠ 0 → ∫ u', f b' u' *
      ‖S2 q N₀ ((b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q)) (((m₂' : ℝ) * u' - m₂ * u) / q)‖ ≤
        H b m₂ b' m₂' u) :
    ∑ n ∈ P3 N₀, psi0 (n / N₀) * ‖Phi f M₂ L n τ‖ ^ 2 ≤
      ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂,
        (m₂ : ℝ) * m₂' * ∫ u, f b u * H b m₂ b' m₂' u := by
  have hfi : ∀ b, Integrable (f b) := fun b => (hfs b).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -|A|) (b := |A|)) fun u hu => hA b u
      (lt_of_le_of_lt (le_abs_self A) (not_le.mp fun h => hu (abs_le.mp h))))
  set z : ℤ → (ZMod q)ˣ × ℤ → ℂ := fun n p => ((p.2 : ℝ) : ℂ) * 𝓕 (fC f p.1) ((p.2 : ℝ) * (n / q + τ / L)) *
    ZMod.stdAddChar (-((n : ZMod q) * ((p.1 : ZMod q) * (p.2 : ZMod q)))) with hz
  have hPhi : ∀ n : ℤ, Phi f M₂ L n τ = ∑ p ∈ (Finset.univ : Finset (ZMod q)ˣ) ×ˢ P2 M₂, z n p := by
    intro n; rw [Phi, Finset.sum_product]
  simp_rw [hPhi]
  refine (sum_mul_norm_sq_le (P3 N₀) _ (fun n : ℤ => psi0 (n / N₀)) z).trans ?_
  rw [Finset.sum_product]
  refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun m₂ hm₂ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_le_sum fun b' _ => Finset.sum_le_sum fun m₂' hm₂' => ?_
  have hm₂p : (0 : ℝ) < m₂ := by have := (mem_P2 m₂).1 hm₂; linarith [this.1, this.2]
  have hm₂p' : (0 : ℝ) < m₂' := by have := (mem_P2 m₂').1 hm₂'; linarith [this.1, this.2]
  set k₀ : ZMod q := (b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q) with hk₀
  -- the pair as `m₂m₂′` times a sum of products of Fourier transforms
  have e1 : ∑ n ∈ P3 N₀, ((psi0 (n / N₀) : ℝ) : ℂ) * z n (b, m₂) * conj (z n (b', m₂')) =
      (((m₂ : ℝ) * m₂' : ℝ) : ℂ) * ∑ n ∈ P3 N₀,
        (((psi0 (n / N₀) : ℝ) : ℂ) * ZMod.stdAddChar (-((n : ZMod q) * k₀))) *
          𝓕 (fC f b) ((m₂ : ℝ) * (n / q + τ / L)) * conj (𝓕 (fC f b') ((m₂' : ℝ) * (n / q + τ / L))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hz, map_mul, Complex.conj_ofReal, conj_stdAddChar]
    have hχ : ZMod.stdAddChar (-((n : ZMod q) * ((b : ZMod q) * (m₂ : ZMod q)))) *
        ZMod.stdAddChar (-(-((n : ZMod q) * ((b' : ZMod q) * (m₂' : ZMod q))))) =
        ZMod.stdAddChar (-((n : ZMod q) * k₀)) := by
      rw [← AddChar.map_add_eq_mul, hk₀]; congr 1; ring
    rw [← hχ]
    push_cast
    ring
  rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hm₂p hm₂p')]
  refine mul_le_mul_of_nonneg_left ?_ (mul_pos hm₂p hm₂p').le
  refine norm_sum_fourier_pair_le _ _ _ (hfi b) (hfi b') (hf b) (hf b') (hH b m₂ hm₂ b' m₂' hm₂') fun u hu => ?_
  refine le_trans (le_of_eq ?_) (hb b m₂ hm₂ b' m₂' hm₂' u hu)
  congr 1; funext u'
  congr 1
  -- the factor `e((τ/L)(m₂′u′ − m₂u))` has absolute value `1`
  have hθ : ∀ n : ℤ, cexp (2 * π * I * (((m₂' : ℝ) * (n / q + τ / L) * u' - (m₂ : ℝ) * (n / q + τ / L) * u : ℝ) : ℂ)) =
      cexp (2 * π * I * ((τ / L * ((m₂' : ℝ) * u' - m₂ * u) : ℝ) : ℂ)) *
        cexp (2 * π * I * (n * ((((m₂' : ℝ) * u' - m₂ * u) / q : ℝ) : ℂ))) := by
    intro n
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : ∑ n ∈ P3 N₀, ((psi0 (n / N₀) : ℝ) : ℂ) * ZMod.stdAddChar (-((n : ZMod q) * k₀)) *
      cexp (2 * π * I * (((m₂' : ℝ) * (n / q + τ / L) * u' - (m₂ : ℝ) * (n / q + τ / L) * u : ℝ) : ℂ)) =
      cexp (2 * π * I * ((τ / L * ((m₂' : ℝ) * u' - m₂ * u) : ℝ) : ℂ)) *
        S2 q N₀ k₀ (((m₂' : ℝ) * u' - m₂ * u) / q) := by
    rw [S2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hθ n]
    ring
  rw [e2, norm_mul, show (2 * π * I * ((τ / L * ((m₂' : ℝ) * u' - m₂ * u) : ℝ) : ℂ)) =
    ↑(2 * π * (τ / L * ((m₂' : ℝ) * u' - m₂ * u))) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I,
    one_mul]

/-! ### Their `Σ₂` by Poisson summation -/

/-- **Their `Σ₂` by Poisson summation**: for `q ≥ 1` and `N₀ > 0`, `S₂(k₀, x) = Σ_{k∈ℤ}N₀ψ̂₀(N₀(k − x + k₀/q))`,
with `k₀` read as its value in `{0, …, q − 1}`. -/
theorem S2_eq_tsum {q : ℕ} [NeZero q] {N₀ : ℝ} (hN₀ : 0 < N₀) (k₀ : ZMod q) (x : ℝ) :
    S2 q N₀ k₀ x = ∑' k : ℤ, ((N₀ : ℝ) : ℂ) * 𝓕 psiC (N₀ * (k - (x - (k₀.val : ℝ) / q))) := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have h := poisson_residue hN₀ one_pos (0 : ℝ) (x - (k₀.val : ℝ) / q)
  simp only [Nat.cast_one, one_mul, Complex.ofReal_zero, zero_add, div_one, mul_zero, Complex.exp_zero,
    mul_one] at h
  rw [← h, S2]
  symm
  refine (tsum_eq_sum fun k hk => ?_).trans (Finset.sum_congr rfl fun k _ => ?_)
  · rw [psiC, psi0_div_eq_zero hN₀ hk, Complex.ofReal_zero, zero_mul]
  · have e : -((k : ZMod q) * k₀) = ((-(k * (k₀.val : ℤ)) : ℤ) : ZMod q) := by
      push_cast; rw [ZMod.natCast_zmod_val]
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
    have hx : cexp (2 * π * I * ((k : ℂ) * ((x - (k₀.val : ℝ) / q : ℝ) : ℂ))) =
        cexp (2 * π * I * ((-(k * (k₀.val : ℤ)) : ℤ) : ℂ) / q) * cexp (2 * π * I * ((k : ℂ) * (x : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    rw [e, ZMod.stdAddChar_coe, psiC, hx]
    ring

/-- For `q ≥ 1` and `N₀ > 0`, `|S₂(k₀, x)| ≤ N₀Σ_k|ψ̂₀(N₀(k − x + k₀/q))|`, a convergent series. -/
theorem norm_S2_le {q : ℕ} [NeZero q] {N₀ : ℝ} (hN₀ : 0 < N₀) (k₀ : ZMod q) (x : ℝ) :
    Summable (fun k : ℤ => ‖𝓕 psiC (N₀ * (k - (x - (k₀.val : ℝ) / q)))‖) ∧
      ‖S2 q N₀ k₀ x‖ ≤ N₀ * ∑' k : ℤ, ‖𝓕 psiC (N₀ * (k - (x - (k₀.val : ℝ) / q)))‖ := by
  have hs : Summable fun k : ℤ => ‖𝓕 psiC (N₀ * (k - (x - (k₀.val : ℝ) / q)))‖ := by
    refine summable_norm_iff.mpr ((summable_psiC_lattice hN₀ one_pos (x - (k₀.val : ℝ) / q) (fun _ => 1)
      (B := 1) fun _ => by simp).congr fun k => ?_)
    simp
  refine ⟨hs, ?_⟩
  rw [S2_eq_tsum hN₀, ← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · refine (hs.mul_left N₀).congr fun k => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN₀]
  · congr 1; funext k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN₀]

/-! ### The decay of `ψ̂₀` -/

/-- `C_K = 2^K(∫ψ̃₀ + D_K/(2π)^K)`. -/
def CK (K : ℕ) : ℝ := 2 ^ K * ((∫ y, psi0 y) + Dpsi K / (2 * π) ^ K)

/-- **The decay of `ψ̂₀`**: `(1 + |y|)^K|ψ̂₀(y)| ≤ C_K`. -/
lemma norm_fourier_psiC_le_CK (K : ℕ) (y : ℝ) : (1 + |y|) ^ K * ‖𝓕 psiC y‖ ≤ CK K := by
  have h1 := fourier_psiC_decay K y
  have h2 := norm_fourier_psiC_le y
  have hpi : 0 < (2 * π) ^ K := by positivity
  have hn := norm_nonneg (𝓕 psiC y)
  have h1' : |y| ^ K * ‖𝓕 psiC y‖ ≤ Dpsi K / (2 * π) ^ K := by
    rw [le_div_iff₀ hpi]
    calc |y| ^ K * ‖𝓕 psiC y‖ * (2 * π) ^ K = (2 * π * |y|) ^ K * ‖𝓕 psiC y‖ := by ring
      _ ≤ Dpsi K := h1
  have hmax : (1 + |y|) ^ K ≤ 2 ^ K * (1 + |y| ^ K) := by
    rcases le_total 1 |y| with h | h
    · calc (1 + |y|) ^ K ≤ (2 * |y|) ^ K := pow_le_pow_left₀ (by positivity) (by linarith) K
        _ = 2 ^ K * |y| ^ K := by rw [mul_pow]
        _ ≤ 2 ^ K * (1 + |y| ^ K) := by gcongr; linarith
    · calc (1 + |y|) ^ K ≤ 2 ^ K := pow_le_pow_left₀ (by positivity) (by linarith) K
        _ ≤ 2 ^ K * (1 + |y| ^ K) := by
          have : 0 ≤ |y| ^ K := by positivity
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) K]
  calc (1 + |y|) ^ K * ‖𝓕 psiC y‖ ≤ 2 ^ K * (1 + |y| ^ K) * ‖𝓕 psiC y‖ := mul_le_mul_of_nonneg_right hmax hn
    _ = 2 ^ K * (‖𝓕 psiC y‖ + |y| ^ K * ‖𝓕 psiC y‖) := by ring
    _ ≤ CK K := by unfold CK; gcongr

end LinnikCGLSig2

#print axioms LinnikCGLSig2.sum_mul_norm_sq_le
#print axioms LinnikCGLSig2.norm_sum_fourier_pair_le
#print axioms LinnikCGLSig2.sum_psi_norm_Phi_sq_le
#print axioms LinnikCGLSig2.S2_eq_tsum
#print axioms LinnikCGLSig2.norm_S2_le
#print axioms LinnikCGLSig2.norm_fourier_psiC_le_CK
