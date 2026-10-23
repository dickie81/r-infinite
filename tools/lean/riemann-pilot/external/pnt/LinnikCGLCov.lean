/-
# Round 683: the terms `n ≠ 0` of `ĝ_a` over `|ξ| ≤ X`, by the change of variables to their `Σ_II` (the CGL plan's
stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li continue the proof of their Lemma 8.2 from (8.7): "By making a change of variables
ξ = m₁n/q + (m₁/M₃)τ, the only m₁ dependence in the inner double sum is a 1/m₁ term." (lines 3428–3432; spaces
restored, the fractions written inline and the subscripts transcribed). This file integrates round 682's bound for the
terms `n ≠ 0` over `|ξ| ≤ X` and makes that change of variables in each term.

The stack's form.
* Their `M₃` is round 680's `L`, and their `ψ̂₁` is `ψ̂₀` (round 659's `𝓕 psiC`): with `ξ = (m₁/L)τ + m₁n/q`,
  `L(n/q − ξ/m₁) = −τ` and `F(m₁, n) = Φ(n, τ)/|m₁|` (`Fb_affine`), with
  `Φ(n, τ) = Σ_bΣ_{m₂∈P2 M₂}m₂f̂_b(m₂(n/q + τ/L))e_q(−nbm₂)` (`Phi`).
* Their restriction `|τ| ⪅ 1` is not made: every `τ` is kept, with the weight `|ψ̂₀(−τ)|`.
* The integral of the series over `n` is taken in `ℝ≥0∞` (`setIntegral_le_of_tsum`), so only finite sums over `n`
  need bounds.

Plain statements, with `q ≥ 1` (`[NeZero q]`), `Ψ(m₁, n) = ψ̂₀(L(n/q − ξ/m₁))`, `F(m₁, n)` and `tg` round 682's
`LinnikCGLNsum.Fb` and `LinnikCGLNsum.tg`, `(h, q)` round 681's `gw`, `C_δ` round 525's `Cdiv` and `B₄` round 681's
`B4`.
* `integrable_fC`, `continuous_fourier_fC`, `continuous_Fb`: for smooth `f_b` that are `0` for `|u| > A`, `f_b` is
  integrable, `f̂_b` is continuous, and so is `ξ ↦ F(m₁, n)`.
* `norm_Fb_le_unif`: `|F(m₁, n)| ≤ Σ_bΣ_{m₂}|m₂/|m₁||∫|f_b|`, a bound independent of `ξ` and `n`.
* `Phi`, `Fb_affine`: `Φ(n, τ)` as above, and for `L ≠ 0` and `m₁ ≠ 0`, `F(m₁, n)` at `ξ = (m₁/L)τ + m₁n/q` is
  `Φ(n, τ)/|m₁|`.
* `integral_eq_abs_mul_integral_affine`: for `c ≠ 0`, `∫h(ξ) dξ = |c|∫h(cτ + d) dτ`.
* `integral_r_eq`: their change of variables. For `L > 0` and `m₁ ≠ 0`,
  `∫|Ψ(m₁, n)||F(m₁, n)|² dξ = (1/(|m₁|L))∫|ψ̂₀(−τ)||Φ(n, τ)|² dτ`.
* `setIntegral_le_of_tsum`: for a measurable set `S`, `F ≥ 0` with `F ≤ KΣ_{m∈P}Σ_nr(m, n, ·)` on `S`, `K ≥ 0`, and
  continuous `r(m, n, ·) ≥ 0` whose series over `n` converge, that are integrable for `m ∈ P` and have
  `Σ_{n∈T}∫r(m, n, ·) ≤ B_m` for every `m ∈ P` and finite set `T`, `∫_SF ≤ KΣ_{m∈P}B_m`.
* `summable_r`: for `L > 0` and `F(n)` bounded, the series `Σ_{n≠0}|ψ̂₀(L(n/q − ξ/m))||F(n)|²` converges.
* `integral_gstar_le`: for smooth `f_b` that are `0` for `|u| > A`, `M₁ > 0`, `L > 0`, `0 < δ ≤ 1`, real `X` and a
  bound `B_II` of `Σ_{n∈T, n≠0}∫|ψ̂₀(−τ)||Φ(n, τ)|² dτ` for every finite set `T`,
  `∫_{|ξ|≤X}Σ_a|ĝ_a(ξ) − Σ_{m₁}tg(a, m₁, 0)|² dξ ≤ K_XΣ_{m₁∈P1 M₁}B_II/(|m₁|L)`, with
  `K_X = d(q)(L/q)²(Σ_h(h, q))²·4C_δB₄(1 + q|X|)^δ(1 + 2qM₁/L)^δ(Σ_h(h, q))(2π + 8πM₁/L)`.

The file imports `LinnikCGLN0.lean`.
-/

import LinnikCGLN0

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate ENNReal

noncomputable section

namespace LinnikCGLCov

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLSep LinnikCGLRFact LinnikCGLRam LinnikCGLJ LinnikCGLG
  LinnikCGLPois8 LinnikCGLCount LinnikCGLAsum LinnikCGLNsum LinnikCGLN0 LinnikCGLLoc

/-! ### Continuity -/

/-- For smooth `f_b` that are `0` for `|u| > A`, `f_b` is integrable. -/
lemma integrable_fC {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) (b : (ZMod q)ˣ) : Integrable (fC f b) :=
  (integrable_term hfs hA b (c := 1) (d := 0) (e := 1) one_ne_zero one_pos).congr
    (Eventually.of_forall fun u => by simp)

/-- For smooth `f_b` that are `0` for `|u| > A`, `f̂_b` is continuous. -/
lemma continuous_fourier_fC {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) (b : (ZMod q)ˣ) : Continuous (𝓕 (fC f b)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
    (integrable_fC hfs hA b)

/-- For `q ≥ 1` and smooth `f_b` that are `0` for `|u| > A`, `ξ ↦ F(m₁, n)` is continuous. -/
lemma continuous_Fb {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) (M₂ : ℝ) (m₁ n : ℤ) : Continuous fun ξ => Fb f M₂ ξ m₁ n := by
  unfold Fb
  refine continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun m₂ _ => ?_
  exact (continuous_const.mul ((continuous_fourier_fC hfs hA b).comp (by fun_prop))).mul continuous_const

/-- For `q ≥ 1`, `|F(m₁, n)| ≤ Σ_bΣ_{m₂}|m₂/|m₁||∫|f_b|`, a bound independent of `ξ` and `n`. -/
lemma norm_Fb_le_unif {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (M₂ ξ : ℝ) (m₁ n : ℤ) :
    ‖Fb f M₂ ξ m₁ n‖ ≤ ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, abs ((m₂ : ℝ) / |(m₁ : ℝ)|) * ∫ u, ‖fC f b u‖ := by
  refine (norm_Fb_le f M₂ ξ m₁ n).trans (Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun m₂ _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _) (abs_nonneg _)

/-! ### The change of variables -/

/-- Their inner sums after the change of variables: `Φ(n, τ) = Σ_bΣ_{m₂∈P2 M₂}m₂f̂_b(m₂(n/q + τ/L))e_q(−nbm₂)`. -/
def Phi {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (M₂ L : ℝ) (n : ℤ) (τ : ℝ) : ℂ :=
  ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, ((m₂ : ℝ) : ℂ) * 𝓕 (fC f b) ((m₂ : ℝ) * (n / q + τ / L)) *
    ZMod.stdAddChar (-((n : ZMod q) * ((b : ZMod q) * (m₂ : ZMod q))))

/-- For `q ≥ 1`, `L ≠ 0` and `m₁ ≠ 0`, `F(m₁, n)` at `ξ = (m₁/L)τ + m₁n/q` is `Φ(n, τ)/|m₁|`. -/
lemma Fb_affine {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (M₂ : ℝ) {L : ℝ} (hL : L ≠ 0) {m₁ : ℤ}
    (hm₁ : (m₁ : ℝ) ≠ 0) (n : ℤ) (τ : ℝ) :
    Fb f M₂ ((m₁ : ℝ) / L * τ + (m₁ : ℝ) * n / q) m₁ n = ((1 / |(m₁ : ℝ)| : ℝ) : ℂ) * Phi f M₂ L n τ := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  unfold Fb Phi
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  have e : (m₂ : ℝ) * ((m₁ : ℝ) / L * τ + (m₁ : ℝ) * n / q) / m₁ = (m₂ : ℝ) * (n / q + τ / L) := by
    field_simp
    ring
  rw [e]
  push_cast
  ring

/-- For `c ≠ 0`, `∫h(ξ) dξ = |c|∫h(cτ + d) dτ`. -/
lemma integral_eq_abs_mul_integral_affine (h : ℝ → ℝ) {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    ∫ ξ, h ξ = |c| * ∫ τ, h (c * τ + d) := by
  have h1 := Measure.integral_comp_mul_left (fun y => h (y + d)) c
  have h2 := integral_add_right_eq_self (μ := volume) h d
  rw [h1, h2, smul_eq_mul, abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul]

/-- **Their change of variables**: for `q ≥ 1`, `L > 0` and `m₁ ≠ 0`,
`∫|Ψ(m₁, n)||F(m₁, n)|² dξ = (1/(|m₁|L))∫|ψ̂₀(−τ)||Φ(n, τ)|² dτ`. -/
theorem integral_r_eq {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (M₂ : ℝ) {L : ℝ} (hL : 0 < L) {m₁ : ℤ}
    (hm₁ : m₁ ≠ 0) (n : ℤ) :
    ∫ ξ, ‖𝓕 psiC (L * (n / q - ξ / m₁))‖ * ‖Fb f M₂ ξ m₁ n‖ ^ 2 =
      1 / (|(m₁ : ℝ)| * L) * ∫ τ, ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hm : (m₁ : ℝ) ≠ 0 := by exact_mod_cast hm₁
  have hma : |(m₁ : ℝ)| ≠ 0 := abs_ne_zero.mpr hm
  have hL0 : L ≠ 0 := hL.ne'
  have hc : (m₁ : ℝ) / L ≠ 0 := div_ne_zero hm hL.ne'
  rw [integral_eq_abs_mul_integral_affine (fun ξ => ‖𝓕 psiC (L * (n / q - ξ / m₁))‖ * ‖Fb f M₂ ξ m₁ n‖ ^ 2) hc
    ((m₁ : ℝ) * n / q)]
  have e : ∀ τ : ℝ, ‖𝓕 psiC (L * (n / q - ((m₁ : ℝ) / L * τ + (m₁ : ℝ) * n / q) / m₁))‖ *
      ‖Fb f M₂ ((m₁ : ℝ) / L * τ + (m₁ : ℝ) * n / q) m₁ n‖ ^ 2 =
      (1 / |(m₁ : ℝ)|) ^ 2 * (‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2) := by
    intro τ
    have e1 : L * (n / q - ((m₁ : ℝ) / L * τ + (m₁ : ℝ) * n / q) / m₁) = -τ := by
      field_simp
      ring
    rw [e1, Fb_affine f M₂ hL.ne' hm n τ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    ring
  simp_rw [e]
  rw [integral_const_mul, abs_div, abs_of_pos hL, ← mul_assoc]
  congr 1
  field_simp

/-! ### Tonelli for a finite sum of series -/

/-- **Tonelli for a finite sum of series**: for a measurable set `S`, `F ≥ 0` with `F ≤ KΣ_{m∈P}Σ_nr(m, n, ·)` on
`S`, `K ≥ 0`, and continuous `r(m, n, ·) ≥ 0` whose series over `n` converge, that are integrable for `m ∈ P` and have
`Σ_{n∈T}∫r(m, n, ·) ≤ B_m` for every `m ∈ P` and finite set `T`, `∫_SF ≤ KΣ_{m∈P}B_m`. -/
lemma setIntegral_le_of_tsum {F : ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S) {K : ℝ} {P : Finset ℤ}
    {r : ℤ → ℤ → ℝ → ℝ} {B : ℤ → ℝ} (hF0 : ∀ x, 0 ≤ F x) (hK : 0 ≤ K) (hr0 : ∀ m n x, 0 ≤ r m n x)
    (hrs : ∀ m x, Summable fun n => r m n x) (hrc : ∀ m n, Continuous (r m n))
    (hri : ∀ m ∈ P, ∀ n, Integrable (r m n)) (hFr : ∀ x ∈ S, F x ≤ K * ∑ m ∈ P, ∑' n, r m n x)
    (hB : ∀ m ∈ P, ∀ T : Finset ℤ, ∑ n ∈ T, ∫ x, r m n x ≤ B m) :
    ∫ x in S, F x ≤ K * ∑ m ∈ P, B m := by
  have hB0 : ∀ m ∈ P, 0 ≤ B m := fun m hm => by simpa using hB m hm ∅
  have hKB : 0 ≤ K * ∑ m ∈ P, B m := mul_nonneg hK (Finset.sum_nonneg hB0)
  by_cases hI : IntegrableOn F S
  swap
  · rw [integral_undef hI]; exact hKB
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => hF0 x) hI.aestronglyMeasurable]
  have hmeas : ∀ m n, Measurable fun x => ENNReal.ofReal (r m n x) := fun m n =>
    (hrc m n).measurable.ennreal_ofReal
  have hlin : ∫⁻ x in S, ENNReal.ofReal (F x) ≤ ENNReal.ofReal (K * ∑ m ∈ P, B m) := by
    calc ∫⁻ x in S, ENNReal.ofReal (F x)
        ≤ ∫⁻ x in S, ENNReal.ofReal K * ∑ m ∈ P, ∑' n, ENNReal.ofReal (r m n x) := by
          refine setLIntegral_mono' hS fun x hx => ?_
          refine (ENNReal.ofReal_le_ofReal (hFr x hx)).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_sum_of_nonneg fun m _ => tsum_nonneg fun n => hr0 m n x]
          congr 1
          exact Finset.sum_congr rfl fun m _ => ENNReal.ofReal_tsum_of_nonneg (fun n => hr0 m n x) (hrs m x)
      _ = ENNReal.ofReal K * ∑ m ∈ P, ∑' n, ∫⁻ x in S, ENNReal.ofReal (r m n x) := by
          rw [lintegral_const_mul'' _ (Finset.measurable_sum P fun m _ =>
            Measurable.tsum fun n => hmeas m n).aemeasurable,
            lintegral_finsetSum' _ fun m _ => (Measurable.tsum fun n => hmeas m n).aemeasurable]
          congr 1
          exact Finset.sum_congr rfl fun m _ => lintegral_tsum fun n => (hmeas m n).aemeasurable
      _ ≤ ENNReal.ofReal K * ∑ m ∈ P, ENNReal.ofReal (B m) := by
          gcongr with m hm
          refine ENNReal.summable.tsum_le_of_sum_le fun T => ?_
          calc ∑ n ∈ T, ∫⁻ x in S, ENNReal.ofReal (r m n x) ≤ ∑ n ∈ T, ENNReal.ofReal (∫ x, r m n x) := by
                gcongr with n hn
                rw [ofReal_integral_eq_lintegral_ofReal (hri m hm n) (Eventually.of_forall fun x => hr0 m n x)]
                exact setLIntegral_le_lintegral _ _
            _ = ENNReal.ofReal (∑ n ∈ T, ∫ x, r m n x) :=
                (ENNReal.ofReal_sum_of_nonneg fun n _ => integral_nonneg fun x => hr0 m n x).symm
            _ ≤ ENNReal.ofReal (B m) := ENNReal.ofReal_le_ofReal (hB m hm T)
      _ = ENNReal.ofReal (K * ∑ m ∈ P, B m) := by
          rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_sum_of_nonneg hB0]
  calc (∫⁻ x in S, ENNReal.ofReal (F x)).toReal ≤ (ENNReal.ofReal (K * ∑ m ∈ P, B m)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    _ = K * ∑ m ∈ P, B m := ENNReal.toReal_ofReal hKB

/-! ### The terms `n ≠ 0` over `|ξ| ≤ X` -/

/-- For `q ≥ 1`, `L > 0` and `F(n)` bounded, the series `Σ_{n≠0}|ψ̂₀(L(n/q − ξ/m))||F(n)|²` converges. -/
lemma summable_r {q : ℕ} [NeZero q] {L : ℝ} (hL : 0 < L) (ξ : ℝ) (m : ℤ) (F : ℤ → ℂ) {B : ℝ}
    (hB : ∀ n, ‖F n‖ ≤ B) :
    Summable fun n : ℤ => if n = 0 then 0 else ‖𝓕 psiC (L * (n / q - ξ / m))‖ * ‖F n‖ ^ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hΨ : Summable fun n : ℤ => ‖𝓕 psiC (L * (n / q - ξ / m))‖ :=
    summable_norm_iff.mpr ((summable_psiC_lattice hL hq (ξ / m) (fun _ => 1) (B := 1) fun _ => by simp).congr
      fun n => one_mul _)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hΨ.mul_left (B ^ 2))
  · split_ifs
    · exact le_refl 0
    · positivity
  · split_ifs
    · have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
      positivity
    · calc ‖𝓕 psiC (L * (n / q - ξ / m))‖ * ‖F n‖ ^ 2 ≤ ‖𝓕 psiC (L * (n / q - ξ / m))‖ * B ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hB n) 2) (norm_nonneg _)
        _ = B ^ 2 * ‖𝓕 psiC (L * (n / q - ξ / m))‖ := by ring

/-- **The terms `n ≠ 0` over `|ξ| ≤ X`**: for `q ≥ 1`, smooth `f_b` that are `0` for `|u| > A`, `M₁ > 0`, `L > 0`,
`0 < δ ≤ 1`, real `X` and a bound `B_II` of `Σ_{n∈T, n≠0}∫|ψ̂₀(−τ)||Φ(n, τ)|² dτ` for every finite set `T`,
`∫_{|ξ|≤X}Σ_a|ĝ_a(ξ) − Σ_{m₁}tg(a, m₁, 0)|² dξ ≤ K_XΣ_{m₁∈P1 M₁}B_II/(|m₁|L)`, with
`K_X = d(q)(L/q)²(Σ_h(h, q))²·4C_δB₄(1 + q|X|)^δ(1 + 2qM₁/L)^δ(Σ_h(h, q))(2π + 8πM₁/L)`. -/
theorem integral_gstar_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ L δ : ℝ} (hM₁ : 0 < M₁) (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (X : ℝ) {BII : ℝ}
    (hBII : ∀ T : Finset ℤ, ∑ n ∈ T.filter (· ≠ 0), ∫ τ, ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2 ≤ BII) :
    ∫ ξ in Icc (-X) X, ∑ a : (ZMod q)ˣ,
        ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ - ∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 ≤
      (q.divisors.card : ℝ) * (L / q) ^ 2 * (∑ h : ZMod q, gw h) ^ 2 *
        (4 * LinnikPower.Cdiv δ * B4 * (1 + q * |X|) ^ δ * (1 + 2 * q * M₁ / L) ^ δ * (∑ h : ZMod q, gw h) *
          (2 * π + 8 * π * M₁ / L)) *
        ∑ m₁ ∈ P1 M₁, BII / (|(m₁ : ℝ)| * L) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hG : 0 ≤ ∑ h : ZMod q, gw h := Finset.sum_nonneg fun h _ => gw_nonneg h
  have hC : 0 ≤ LinnikPower.Cdiv δ := le_trans zero_le_one (LinnikPower.one_le_Cdiv hδ hδ1)
  have hB4 := B4_nonneg
  have hq0 : (q : ℝ) ≠ 0 := hq.ne'
  refine setIntegral_le_of_tsum measurableSet_Icc (fun ξ => Finset.sum_nonneg fun a _ => sq_nonneg _)
    (by positivity) (r := fun m n ξ => if n = 0 then 0 else ‖𝓕 psiC (L * (n / q - ξ / m))‖ * ‖Fb f M₂ ξ m n‖ ^ 2)
    (fun m n ξ => by split_ifs <;> positivity) (fun m ξ => ?_) (fun m n => ?_) (fun m hm n => ?_)
    (fun ξ hξ => ?_) (fun m hm T => ?_)
  · exact summable_r hL ξ m _ (norm_Fb_le f M₂ ξ m)
  · rcases eq_or_ne n 0 with hn | hn
    · simp only [hn, ↓reduceIte]; exact continuous_const
    · simp only [hn, ↓reduceIte]
      exact (continuous_kloc.comp (by fun_prop)).norm.mul ((continuous_Fb hfs hA M₂ m n).norm.pow 2)
  · rcases eq_or_ne n 0 with hn | hn
    · simp only [hn, ↓reduceIte]; exact integrable_zero _ _ _
    · simp only [hn, ↓reduceIte]
      have hm0 : (m : ℝ) ≠ 0 := by
        have := (mem_P1 m).1 hm
        intro h; rw [h, abs_zero] at this; linarith [this.1]
      have hk : Integrable fun ξ : ℝ => ‖𝓕 psiC (L * (n / q - ξ / m))‖ := by
        have h1 := (integrable_kloc.norm.comp_add_right (L * n / q)).comp_mul_left' (R := -(L / m))
          (neg_ne_zero.mpr (div_ne_zero hL.ne' hm0))
        have e : ∀ ξ : ℝ, -(L / m) * ξ + L * n / q = L * (n / q - ξ / m) := fun ξ => by ring
        refine h1.congr (Eventually.of_forall fun ξ => ?_)
        simp only [kloc, e]
      refine hk.mul_bdd (c := (∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, abs ((m₂ : ℝ) / |(m : ℝ)|) * ∫ u, ‖fC f b u‖) ^ 2)
        ((continuous_Fb hfs hA M₂ m n).norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_Fb_le_unif f M₂ ξ m n) 2
  · have h1 := sum_a_fourier_ga_le (q := q) hfs hA (M₂ := M₂) hM₁ hL hδ hδ1 ξ
    refine h1.trans ?_
    have hξX : |ξ| ≤ |X| := (abs_le.mpr ⟨hξ.1, hξ.2⟩).trans (le_abs_self X)
    have hR : 0 ≤ ∑ m₁ ∈ P1 M₁, ∑' n : ℤ,
        (if n = 0 then 0 else ‖𝓕 psiC (L * (n / q - ξ / m₁))‖ * ‖Fb f M₂ ξ m₁ n‖ ^ 2) :=
      Finset.sum_nonneg fun m _ => tsum_nonneg fun n => by split_ifs <;> positivity
    have hpow : (1 + q * |ξ|) ^ δ ≤ (1 + q * |X|) ^ δ :=
      Real.rpow_le_rpow (by positivity) (by gcongr) hδ.le
    refine mul_le_mul_of_nonneg_right ?_ hR
    gcongr
  · have hm0 : m ≠ 0 := by
      have := (mem_P1 m).1 hm
      intro h; rw [h, Int.cast_zero, abs_zero] at this; linarith [this.1]
    have hma : 0 < |(m : ℝ)| := abs_pos.mpr (by exact_mod_cast hm0)
    have key : ∀ n : ℤ, ∫ ξ, (if n = 0 then 0 else ‖𝓕 psiC (L * (n / q - ξ / m))‖ * ‖Fb f M₂ ξ m n‖ ^ 2) =
        if n = 0 then 0 else 1 / (|(m : ℝ)| * L) * ∫ τ, ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2 := by
      intro n
      rcases eq_or_ne n 0 with hn | hn
      · simp only [hn, ↓reduceIte, integral_zero]
      · simp only [hn, ↓reduceIte]
        exact integral_r_eq f M₂ hL hm0 n
    rw [Finset.sum_congr rfl fun n _ => key n, sum_ite_zero, ← Finset.mul_sum]
    calc 1 / (|(m : ℝ)| * L) * ∑ n ∈ T.filter (· ≠ 0), ∫ τ, ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2
        ≤ 1 / (|(m : ℝ)| * L) * BII := mul_le_mul_of_nonneg_left (hBII T) (by positivity)
      _ = BII / (|(m : ℝ)| * L) := by ring

end LinnikCGLCov

#print axioms LinnikCGLCov.Fb_affine
#print axioms LinnikCGLCov.integral_r_eq
#print axioms LinnikCGLCov.setIntegral_le_of_tsum
#print axioms LinnikCGLCov.integral_gstar_le
