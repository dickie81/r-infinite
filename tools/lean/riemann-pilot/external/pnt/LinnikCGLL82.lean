/-
# Round 688: their Lemma 8.2 with explicit constants (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li's Lemma 8.2: "Let f⃗ = {f_b} be as in Proposition 8.1. Then there is a bump function ψ(x) supported on
|x| ≪ 1 such that" (lines 2495–2496; spaces restored, the arrow and the subscript transcribed)
`J(f⃗) ⪅ φ(q)M⁶(∫_ℝΣ_bf_b(u) du)² + φ(q)(M⁴∫_ℝΣ_bf_b(u)² du)^{1/2}J(f̃⃗)^{1/2}` (lines 2497–2516, transcribed). This
file assembles rounds 680 to 687 into that bound with explicit constants, before any choice of parameters.

The stack's form.
* Their `ψ` is round 656's bump `ψ̃₀`, and `f̃_b` is round 685's `ftil`.
* Their `J(f⃗)` is a supremum over `M₁, M₂, M₃` of round 662's `Jint`; the bound here is for one `(M₁, M₂, M₃, κ)`,
  with `κM₃ ≤ L` for round 680's majorant. Their `J(f̃⃗)` appears as `Jint` for `f̃` at `(M₂, M₂, M₂, 4|A| + 2)`, inside
  round 686's `B_J`.
* The decay premise enters at one exponent `j`, as in round 687.
* Their "⪅" is not taken: the bound keeps every constant, and the choice of `L`, `X`, `N₀`, `δ`, `j` and `K` is left
  to the next round.
* The steps: round 680's `J ≤ Σ_a∫|ĝ_a|²`, split at `|ξ| = X`. On `|ξ| ≤ X`, `|ĝ_a|² ≤ 2|g₀,a|² + 2|ĝ_a − g₀,a|²`,
  with `g₀,a` the term `n = 0` (round 682) and the rest by round 683, with `B_II` from rounds 686 and 687. On
  `|ξ| > X`, round 687's tail.

Plain statements, with `q ≥ 1` (`[NeZero q]`), `ĝ_a` the Fourier transform of round 680's `ga`,
`g₀,a = Σ_{m₁∈P1 M₁}tg(a, m₁, 0)` round 682's term `n = 0`, `W₀` round 682's `W0`, `I₀ = ∫|ψ̂₀(−τ)| dτ`, and the
constants below.
* `fourier_ga_props`: for smooth `f_b` that are `0` for `|u| > A` and `M₁ > 0`, `ĝ_a` is continuous and `|ĝ_a|²` is
  integrable.
* `continuous_g0`, `integrable_g0`: for smooth `f_b` that are `0` for `|u| > A`, `g₀,a` is continuous; if also
  `f_b ≥ 0`, `M₁ > 0` and `L > 0`, `|g₀,a|²` is integrable.
* `norm_sq_le_two`, `norm_sub_sq_le_two`: `|x|² ≤ 2|y|² + 2|x − y|²` and `|x − y|² ≤ 2|x|² + 2|y|²`.
* `KX`, `BJ`, `Btail`, `G1`: round 683's `K_X`, round 686's `B_J`, round 687's bound of the terms `|n| > N₀` (`B_tail`),
  and round 687's `G₁`.
* `lemma82_explicit`: for smooth `f_b ≥ 0` that are `0` for `|u| > A`, `M₁, M₂, L > 0` with `κM₃ ≤ L`, `0 < δ ≤ 1`,
  `X ≥ 1`, `T ≥ 1`, `N₀ > 0`, `K ≥ 4`, `j ≥ 1`, `D, Λ ≥ 0` and the decay `Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)^jΛ` for `ξ ≠ 0`,
  `Jint(f, M₁, M₂, M₃, κ) ≤ 2φ(q)W₀²(2πM₁/L) + 2K_XΣ_{m₁∈P1 M₁}(I₀B_J + B_tail)/(|m₁|L) + 2πφ(q)G₁²X^{−(2j−2)}`.

The file imports `LinnikCGLTail.lean`.
-/

import LinnikCGLTail

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLL82

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLSep LinnikCGLRFact LinnikCGLRam LinnikCGLJ LinnikCGLG
  LinnikCGLPois8 LinnikCGLCount LinnikCGLAsum LinnikCGLNsum LinnikCGLN0 LinnikCGLCov LinnikCGLSig2 LinnikCGLFtil
  LinnikCGLLoc LinnikCGLJtil LinnikCGLTail

/-! ### `ĝ_a` and the term `n = 0` as functions of `ξ` -/

/-- For smooth `f_b` that are `0` for `|u| > A` and `M₁ > 0`, `ĝ_a` is continuous and `|ĝ_a|²` is integrable (the
Fourier transform of a Schwartz function is one). -/
lemma fourier_ga_props {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) {M₁ : ℝ} (hM₁ : 0 < M₁) (M₂ L : ℝ) (a : (ZMod q)ˣ) :
    Continuous (𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ))) ∧
      Integrable fun ξ => ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 := by
  have hsm : ContDiff ℝ ∞ (fun u => (ga f M₁ M₂ L a u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_ga hfs M₁ M₂ L a)
  set G : SchwartzMap ℝ ℂ := (hasCompactSupport_ga hA hM₁ a).toSchwartzMap hsm with hG
  set H : SchwartzMap ℝ ℂ := 𝓕 G with hH
  have e : ⇑H = 𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) := by
    rw [hH, SchwartzMap.fourier_coe]; rfl
  refine ⟨e ▸ H.continuous, ?_⟩
  have h := (memLp_two_iff_integrable_sq_norm H.continuous.aestronglyMeasurable).1 (H.memLp 2)
  rw [e] at h
  exact h

/-- For smooth `f_b` that are `0` for `|u| > A`, the term `n = 0`, `ξ ↦ Σ_{m₁∈P1 M₁}tg(a, m₁, 0)`, is continuous. -/
lemma continuous_g0 {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) (M₁ M₂ L : ℝ) (a : (ZMod q)ˣ) :
    Continuous fun ξ => ∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0 := by
  refine continuous_finsetSum _ fun m₁ _ => ?_
  unfold tg
  exact (((continuous_const.mul (continuous_kloc.comp (by fun_prop))).mul continuous_const).mul
    (continuous_Fb hfs hA M₂ m₁ 0)).mul continuous_const

/-- For smooth `f_b ≥ 0` that are `0` for `|u| > A`, `M₁ > 0` and `L > 0`, `|Σ_{m₁∈P1 M₁}tg(a, m₁, 0)|²` is
integrable. -/
lemma integrable_g0 {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) (hf : ∀ b u, 0 ≤ f b u) {M₁ L : ℝ} (hM₁ : 0 < M₁) (hL : 0 < L) (M₂ : ℝ)
    (a : (ZMod q)ˣ) : Integrable fun ξ => ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 := by
  have hc : 0 < L / (2 * M₁) := by positivity
  have hint : Integrable fun ξ : ℝ => W0 f M₁ M₂ L ^ 2 * lor (L / (2 * M₁)) ξ :=
    ((integrable_lor hc 0).congr (Eventually.of_forall fun ξ => by simp only [zero_sub, lor_neg])).const_mul _
  refine hint.mono' ((continuous_g0 hfs hA M₁ M₂ L a).norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 := norm_g0_le (M₂ := M₂) hf hM₁ hL ξ a
  have hl0 : 0 ≤ lor (L / (2 * M₁)) ξ := (lor_pos' _ _).le
  have hl1 : lor (L / (2 * M₁)) ξ ^ 4 ≤ lor (L / (2 * M₁)) ξ :=
    pow_le_of_le_one hl0 (lor_le_one _ _) (by norm_num)
  calc ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 ≤ (W0 f M₁ M₂ L * lor (L / (2 * M₁)) ξ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = W0 f M₁ M₂ L ^ 2 * lor (L / (2 * M₁)) ξ ^ 4 := by ring
    _ ≤ W0 f M₁ M₂ L ^ 2 * lor (L / (2 * M₁)) ξ := mul_le_mul_of_nonneg_left hl1 (sq_nonneg _)

/-- `‖x‖² ≤ 2‖y‖² + 2‖x − y‖²`. -/
lemma norm_sq_le_two {x y : ℂ} : ‖x‖ ^ 2 ≤ 2 * ‖y‖ ^ 2 + 2 * ‖x - y‖ ^ 2 := by
  have h : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    calc ‖x‖ = ‖y + (x - y)‖ := by rw [add_sub_cancel]
      _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y), sq_nonneg (‖y‖ - ‖x - y‖)]

/-- `‖x − y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
lemma norm_sub_sq_le_two {x y : ℂ} : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y), sq_nonneg (‖x‖ - ‖y‖)]

/-! ### Their Lemma 8.2 -/

/-- Round 683's factor `K_X = d(q)(L/q)²G²·4C_δB₄(1 + q|X|)^δ(1 + 2qM₁/L)^δG(2π + 8πM₁/L)`, with
`G = Σ_{h mod q}(h, q)` (round 681's `gw`). -/
def KX (q : ℕ) [NeZero q] (L M₁ X δ : ℝ) : ℝ :=
  (q.divisors.card : ℝ) * (L / q) ^ 2 * (∑ h : ZMod q, gw h) ^ 2 *
    (4 * LinnikPower.Cdiv δ * B4 * (1 + q * |X|) ^ δ * (1 + 2 * q * M₁ / L) ^ δ * (∑ h : ZMod q, gw h) *
      (2 * π + 8 * π * M₁ / L))

/-- Round 686's bound `B_J = N₀C_K((4M₂²/(qT))√𝔖√J̃ + EP²F²)`, with `𝔖 = ∫Σ_bf_b²`,
`J̃ = Jint(f̃, M₂, M₂, M₂, 4|A| + 2)`, `E = (1 + N₀M₂/(qT))^{−(K−2)}(2π + 4π/N₀)`, `P = Σ_{m₂∈P2 M₂}m₂` and
`F = Σ_b∫f_b`. -/
def BJ {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (A M₂ T N₀ : ℝ) (K : ℕ) : ℝ :=
  N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * √(∫ u, ∑ b, f b u ^ 2) * √(Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2)) +
    ((1 + N₀ * M₂ / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) * (∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) ^ 2 *
      (∑ b, ∫ u, f b u) ^ 2)

/-- Round 687's bound of the terms `|n| > N₀`:
`12π(I₀(PDΛ)²(2qT/M₂)^{2j}N₀^{−(2j−2)} + πC_K(PF)²(2q/L)^{K−2}N₀^{−(K−4)})`, with `I₀ = ∫|ψ̂₀(−τ)| dτ`. -/
def Btail {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (M₂ L N₀ T D Λ : ℝ) (j K : ℕ) : ℝ :=
  12 * π * ((∫ τ, ‖𝓕 psiC (-τ)‖) * ((∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) * D * Λ) ^ 2 * (2 * q * T / M₂) ^ (2 * j) *
      (N₀ ^ (2 * j - 2))⁻¹ +
    π * CK K * ((∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) * ∑ b, ∫ u, f b u) ^ 2 * (2 * q / L) ^ (K - 2) * (N₀ ^ (K - 4))⁻¹)

/-- Round 687's constant `G₁ = #P1·#P2·(2M₂/M₁)·q#P3·D(2M₁T/M₂)^jΛ`. -/
def G1 (q : ℕ) (M₁ M₂ L T D Λ : ℝ) (j : ℕ) : ℝ :=
  (P1 M₁).card * (P2 M₂).card * (2 * M₂ / M₁) * (q * (P3 L).card) * (D * (2 * M₁ * T / M₂) ^ j * Λ)

/-- **Their Lemma 8.2, with explicit constants**: for `q ≥ 1`, smooth `f_b ≥ 0` that are `0` for `|u| > A`,
`M₁, M₂, L > 0` with `κM₃ ≤ L`, `0 < δ ≤ 1`, `X ≥ 1`, `T ≥ 1`, `N₀ > 0`, `K ≥ 4`, `j ≥ 1`, `D, Λ ≥ 0` and the decay
`Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)^jΛ` for `ξ ≠ 0`,
`Jint(f, M₁, M₂, M₃, κ) ≤ 2φ(q)W₀²(2πM₁/L) + 2K_XΣ_{m₁∈P1 M₁}(I₀B_J + B_tail)/(|m₁|L) + 2πφ(q)G₁²X^{−(2j−2)}`, with
`W₀` round 682's `W0` and `I₀ = ∫|ψ̂₀(−τ)| dτ`. -/
theorem lemma82_explicit {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    (hf : ∀ b u, 0 ≤ f b u) {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ M₃ κ L δ X T N₀ D Λ : ℝ}
    {j K : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hL : 0 < L) (hκL : κ * M₃ ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hX : 1 ≤ X) (hT : 1 ≤ T) (hN₀ : 0 < N₀) (hK : 4 ≤ K) (hj : 1 ≤ j) (hD : 0 ≤ D) (hΛ : 0 ≤ Λ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D * (T / |ξ|) ^ j * Λ) :
    Jint f M₁ M₂ M₃ κ ≤ 2 * (q.totient * W0 f M₁ M₂ L ^ 2 * (2 * π * M₁ / L)) +
      2 * (KX q L M₁ X δ * ∑ m₁ ∈ P1 M₁,
        ((∫ τ, ‖𝓕 psiC (-τ)‖) * BJ f A M₂ T N₀ K + Btail f M₂ L N₀ T D Λ j K) / (|(m₁ : ℝ)| * L)) +
      2 * π * q.totient * G1 q M₁ M₂ L T D Λ j ^ 2 * (X ^ (2 * j - 2))⁻¹ := by
  classical
  have hT0 : 0 ≤ T := by linarith
  -- `B_II`, from rounds 686 and 687
  have hBII : ∀ W : Finset ℤ, ∑ n ∈ W.filter (· ≠ 0), ∫ τ, ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2 ≤
      (∫ τ, ‖𝓕 psiC (-τ)‖) * BJ f A M₂ T N₀ K + Btail f M₂ L N₀ T D Λ j K := by
    intro W
    rw [← Finset.sum_filter_add_sum_filter_not (W.filter (· ≠ 0)) (fun n : ℤ => |(n : ℝ)| ≤ N₀)]
    refine add_le_add (sum_integral_Phi_le hfs hA hf hT hN₀ hM₂ (by omega) L _) ?_
    have e : (W.filter (· ≠ 0)).filter (fun n : ℤ => ¬|(n : ℝ)| ≤ N₀) =
        (W.filter (· ≠ 0)).filter (fun n : ℤ => N₀ < |(n : ℝ)|) := Finset.filter_congr fun n _ => not_le
    rw [e]
    exact sum_integral_Phi_tail_le hfs hA hf hM₂ hL hN₀ hT0 hD hΛ hj hK hdec _
  have h683 := integral_gstar_le (M₂ := M₂) hfs hA hM₁ hL hδ hδ1 X hBII
  have h682 := sum_integral_g0_le (M₂ := M₂) hf hM₁ hL
  have h687 := setIntegral_ga_tail_le (q := q) (L := L) hfs hA hM₁ hM₂ hX hT0 hD hΛ hj hdec
  -- the functions of `ξ`
  have hP : ∀ a : (ZMod q)ˣ, Continuous (𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ))) ∧
      Integrable fun ξ => ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 := fun a => fourier_ga_props hfs hA hM₁ M₂ L a
  have hI0 : ∀ a : (ZMod q)ˣ, Integrable fun ξ => ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 :=
    fun a => integrable_g0 hfs hA hf hM₁ hL M₂ a
  have hI3 : ∀ a : (ZMod q)ˣ, Integrable fun ξ =>
      ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ - ∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 := by
    intro a
    have hmaj : Integrable fun ξ => 2 * ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 +
        2 * ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 := ((hP a).2.const_mul 2).add ((hI0 a).const_mul 2)
    refine hmaj.mono' ((((hP a).1.sub (continuous_g0 hfs hA M₁ M₂ L a)).norm.pow 2).aestronglyMeasurable)
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_sub_sq_le_two
  have hsum : Integrable fun ξ => ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 :=
    integrable_finsetSum _ fun a _ => (hP a).2
  have hsum0 : Integrable fun ξ => ∑ a : (ZMod q)ˣ, ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 :=
    integrable_finsetSum _ fun a _ => hI0 a
  have hsum3 : Integrable fun ξ => ∑ a : (ZMod q)ˣ,
      ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ - ∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 :=
    integrable_finsetSum _ fun a _ => hI3 a
  -- `|ξ| ≤ X`
  have hpt : ∀ ξ, ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 ≤
      2 * ∑ a : (ZMod q)ˣ, ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 +
        2 * ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ - ∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 := by
    intro ξ
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ => norm_sq_le_two
  have hmain : ∫ ξ in Icc (-X) X, ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 ≤
      2 * (q.totient * W0 f M₁ M₂ L ^ 2 * (2 * π * M₁ / L)) +
        2 * (KX q L M₁ X δ * ∑ m₁ ∈ P1 M₁,
          ((∫ τ, ‖𝓕 psiC (-τ)‖) * BJ f A M₂ T N₀ K + Btail f M₂ L N₀ T D Λ j K) / (|(m₁ : ℝ)| * L)) := by
    calc ∫ ξ in Icc (-X) X, ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2
        ≤ ∫ ξ in Icc (-X) X, (2 * ∑ a : (ZMod q)ˣ, ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 +
            2 * ∑ a : (ZMod q)ˣ,
              ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ - ∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun ξ => Finset.sum_nonneg fun a _ => sq_nonneg _)
            ((hsum0.const_mul 2).add (hsum3.const_mul 2)).integrableOn (Eventually.of_forall hpt)
      _ = 2 * (∫ ξ in Icc (-X) X, ∑ a : (ZMod q)ˣ, ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2) +
            2 * ∫ ξ in Icc (-X) X, ∑ a : (ZMod q)ˣ,
              ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ - ∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 := by
          rw [integral_add (hsum0.const_mul 2).integrableOn (hsum3.const_mul 2).integrableOn, integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * (q.totient * W0 f M₁ M₂ L ^ 2 * (2 * π * M₁ / L)) +
            2 * (KX q L M₁ X δ * ∑ m₁ ∈ P1 M₁,
              ((∫ τ, ‖𝓕 psiC (-τ)‖) * BJ f A M₂ T N₀ K + Btail f M₂ L N₀ T D Λ j K) / (|(m₁ : ℝ)| * L)) := by
          have h2 : (0 : ℝ) ≤ 2 := by norm_num
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ h2) (mul_le_mul_of_nonneg_left h683 h2)
          refine (setIntegral_le_integral hsum0 (Eventually.of_forall fun ξ =>
            Finset.sum_nonneg fun a _ => sq_nonneg _)).trans ?_
          rw [integral_finsetSum _ fun a _ => hI0 a]
          exact h682
  calc Jint f M₁ M₂ M₃ κ ≤ ∑ a : (ZMod q)ˣ, ∫ u, ga f M₁ M₂ L a u ^ 2 := Jint_le_ga hfs hf hA hM₁ hκL
    _ = ∑ a : (ZMod q)ˣ, ∫ ξ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => integral_sq_ga hfs hA hM₁ a
    _ = ∫ ξ, ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 :=
        (integral_finsetSum _ fun a _ => (hP a).2).symm
    _ = (∫ ξ in Icc (-X) X, ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2) +
          ∫ ξ in (Icc (-X) X)ᶜ, ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 :=
        (integral_add_compl measurableSet_Icc hsum).symm
    _ ≤ _ := add_le_add hmain h687

end LinnikCGLL82

#print axioms LinnikCGLL82.fourier_ga_props
#print axioms LinnikCGLL82.integrable_g0
#print axioms LinnikCGLL82.lemma82_explicit
