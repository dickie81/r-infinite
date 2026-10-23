/-
# Round 686: their Cauchy–Schwarz back to `J(f̃⃗)`, for the terms `|n| ≤ N₀` of their `Σ_II` (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li finish their bound for `Σ_II` "combining the bounds M₁, M₂, M₃ ≤ M with the Cauchy-Schwarz inequality"
(lines 3658–3659; spaces restored, the subscripts transcribed). On the residue class they write "We also absorb a factor
of q to bring in the gcd factor since given this modular constraint on m₃, we have q = (−bm₂ + b′m₂′ + m₃, q)." (lines
3730–3733; likewise), and "Continuing, since f̃_b is supported on |u| ≪ 1, we have that |m₃| ≪ M₂." (lines 3733–3734;
likewise, the tilde transcribed). Their bound is `⪅ φ(q)(M⁴∫_ℝΣ_bf_b(u)² du)^{1/2}J(f̃⃗)^{1/2}` (lines 3765–3776,
transcribed). This file proves that step for round 685's majorant, and bounds the terms `|n| ≤ N₀` of round 683's
`B_II`.

The stack's form.
* Their factor `q` is `gJw(−b, b′, (m₂, m₂′, m₃)) = q` on the class `m₃ ≡ bm₂ − b′m₂′ (mod q)` (`gJw_neg_eq`). Their
  range `|m₃| ≪ M₂` is round 685's window `R`, which lies in round 662's `setJ M₂ M₂ M₂ (4|A| + 2)` (`mem_setJ_of`).
* Their `J(f̃⃗)` is round 662's `Jint` for `f̃` at `(M₂, M₂, M₂, 4|A| + 2)`, after the sum over `b` is reindexed by
  `b ↦ −b`. `f̃_b` vanishes for `|u| > |A| + 2/T` (`ftil_eq_zero`), so that integrand is integrable.
* The bound keeps `M₂`: their `M₁, M₂, M₃ ≤ M` is not applied here.
* The error term of round 685's majorant keeps its explicit factor, bounded by its value at `m₂′ = M₂`, since every
  `m₂′ ∈ P2 M₂` exceeds `M₂`: `E = (1 + N₀M₂/(qT))^{−(K−2)}(2π + 4π/N₀)`.
* "Trivially we have Σ₁ ⪅ 1." (line 3563; spaces restored, the subscript transcribed.) Here the bound of round 684's
  expansion holds for every `τ`, and the weight `|ψ̂₀(−τ)|` is integrated. Round 684's weight `ψ̃₀(n/N₀)` is `1` for
  `|n| ≤ N₀`, so the terms `|n| ≤ N₀` of `B_II` are at most `∫|ψ̂₀(−τ)| dτ` times the bound.

Plain statements, with `q ≥ 1` (`[NeZero q]`), `R` round 685's `R3`, `C_K` round 684's `CK`, `Φ(n, τ)` round 683's
`Phi`, `[·]` the indicator, `𝔖 = ∫Σ_bf_b(u)² du`, `J̃ = Jint(f̃, M₂, M₂, M₂, 4|A| + 2)`, `P = Σ_{m₂∈P2 M₂}m₂` and
`F = Σ_b∫f_b`.
* `gJw_neg_eq`: if `m₃ ≡ bm₂ − b′m₂′ (mod q)`, then `gJw(−b, b′, (m₂, m₂′, m₃)) = q`.
* `mem_setJ_of`: for `m₂, m₂′ ∈ P2 M₂` and `m₃ ∈ R`, `(m₂, m₂′, m₃) ∈ setJ M₂ M₂ M₂ (4|A| + 2)`.
* `sum_res_le_gJ`: for `g_b ≥ 0`, every unit `b` and every real `u`,
  `Σ_{m₂,b′,m₂′}m₂m₂′Σ_{m₃∈R}[m₃ ≡ bm₂ − b′m₂′]g_{b′}((m₂u + m₃)/m₂′) ≤ (4M₂²/q)gJ(g, setJ M₂ M₂ M₂ (4|A| + 2), −b, u)`.
* `ftil_eq_zero`: for `T > 0` and `f_b` that are `0` for `|u| > A`, `f̃_b(x) = 0` for `|x| > |A| + 2/T`.
* `integrable_of_vanish`, `continuous_gJ_ftil`, `continuous_Hmaj`: a continuous function that is `0` for `|u| > A` is
  integrable; for `T > 0` and integrable `f_b`, `u ↦ gJ(f̃, S, a, u)` and `u ↦ Hmaj(b, m₂, b′, m₂′, u)` are continuous.
* `integral_sum_mul_le`: for continuous `F_i, G_i ≥ 0` (finitely many `i`) with `Σ_iF_i²` and `Σ_iG_i²` integrable,
  `∫Σ_iF_iG_i ≤ √(∫Σ_iF_i²)√(∫Σ_iG_i²)`.
* `sum_Hmaj_le`: for `f_b ≥ 0`, `T > 0` and `N₀ > 0`, every unit `b` and every real `u`,
  `Σ_{m₂,b′,m₂′}m₂m₂′Hmaj(b, m₂, b′, m₂′, u) ≤ N₀C_K((4M₂²/(qT))gJ(f̃, setJ M₂ M₂ M₂ (4|A| + 2), −b, u) + EP²F)`.
* `sum_psi_norm_Phi_sq_le_J`: for smooth `f_b ≥ 0` that are `0` for `|u| > A`, `T ≥ 1`, `N₀ > 0`, `M₂ > 0` and `K ≥ 2`,
  `Σ_{n∈P3 N₀}ψ̃₀(n/N₀)|Φ(n, τ)|² ≤ B_J = N₀C_K((4M₂²/(qT))√𝔖√J̃ + EP²F²)` for every `L` and `τ`.
* `norm_Phi_le`, `continuous_Phi`, `integrable_norm_fourier_psiC_neg`: for `f_b ≥ 0`,
  `|Φ(n, τ)| ≤ Σ_bΣ_{m₂∈P2 M₂}|m₂|∫f_b`; for smooth `f_b` that are `0` for `|u| > A`, `τ ↦ Φ(n, τ)` is continuous; and
  `τ ↦ |ψ̂₀(−τ)|` is integrable.
* `sum_integral_Phi_le`: with the hypotheses of `sum_psi_norm_Phi_sq_le_J`,
  `Σ_{n∈W, |n|≤N₀}∫|ψ̂₀(−τ)||Φ(n, τ)|² dτ ≤ (∫|ψ̂₀(−τ)| dτ)B_J` for every `L` and every finite set `W` of integers.

The file imports `LinnikCGLFtil.lean`.
-/

import LinnikCGLFtil

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate Convolution

noncomputable section

namespace LinnikCGLJtil

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLSep LinnikCGLRFact LinnikCGLRam LinnikCGLJ LinnikCGLG
  LinnikCGLPois8 LinnikCGLCount LinnikCGLAsum LinnikCGLNsum LinnikCGLN0 LinnikCGLCov LinnikCGLSig2 LinnikCGLFtil
  LinnikCGLLoc

/-! ### Their gcd factor -/

/-- If `m₃ ≡ bm₂ − b′m₂′ (mod q)`, their gcd `(−bm₂ + b′m₂′ + m₃, q)` is `q`. -/
lemma gJw_neg_eq {q : ℕ} (b b' : (ZMod q)ˣ) {m₂ m₂' m : ℤ}
    (h : (m : ZMod q) = (b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q)) :
    gJw (-b) b' (m₂, m₂', m) = q := by
  have e : ((-b : (ZMod q)ˣ) : ZMod q) * (m₂ : ZMod q) + (b' : ZMod q) * (m₂' : ZMod q) + (m : ZMod q) = 0 := by
    rw [h, Units.val_neg]; ring
  show (Nat.gcd (((-b : (ZMod q)ˣ) : ZMod q) * (m₂ : ZMod q) + (b' : ZMod q) * (m₂' : ZMod q) +
    (m : ZMod q)).val q : ℝ) = q
  rw [e, ZMod.val_zero, Nat.gcd_zero_left]

/-- For `m₂, m₂′ ∈ P2 M₂` and `m₃ ∈ R`, `(m₂, m₂′, m₃) ∈ setJ M₂ M₂ M₂ (4|A| + 2)`. -/
lemma mem_setJ_of {A M₂ : ℝ} {m₂ m₂' m : ℤ} (hm₂ : m₂ ∈ P2 M₂) (hm₂' : m₂' ∈ P2 M₂) (hm : m ∈ R3 A M₂) :
    (m₂, m₂', m) ∈ setJ M₂ M₂ M₂ (4 * |A| + 2) := by
  have h2 := (mem_P2 m₂).1 hm₂
  have h2' := (mem_P2 m₂').1 hm₂'
  have hp : (0 : ℝ) < m₂ := by linarith [h2.1, h2.2]
  refine (mem_setJ _).2 ⟨?_, ?_, h2'.1, h2'.2, mem_R3.1 hm⟩
  · show M₂ < |(m₂ : ℝ)|
    rw [abs_of_pos hp]; exact h2.1
  · show |(m₂ : ℝ)| ≤ 2 * M₂
    rw [abs_of_pos hp]; exact h2.2

/-- **Their gcd factor**: for `q ≥ 1` and `g_b ≥ 0`, for every unit `b` and real `u`,
`Σ_{m₂,b′,m₂′}m₂m₂′Σ_{m₃∈R}[m₃ ≡ bm₂ − b′m₂′]g_{b′}((m₂u + m₃)/m₂′) ≤ (4M₂²/q)gJ(g, setJ M₂ M₂ M₂ (4|A| + 2), −b, u)`,
with `R = {m₃ : |m₃| ≤ (4|A| + 2)M₂}`. -/
lemma sum_res_le_gJ {q : ℕ} [NeZero q] {g : (ZMod q)ˣ → ℝ → ℝ} (hg : ∀ b u, 0 ≤ g b u) (A M₂ : ℝ)
    (b : (ZMod q)ˣ) (u : ℝ) :
    ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂, (m₂ : ℝ) * m₂' *
      ∑ m ∈ R3 A M₂, (if (m : ZMod q) = (b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q) then
        g b' ((m₂ * u + m) / m₂') else 0) ≤
      4 * M₂ ^ 2 / q * gJ g (setJ M₂ M₂ M₂ (4 * |A| + 2)) (-b) u := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set W : (ZMod q)ˣ → ℤ × ℤ × ℤ → ℝ := fun b' m => g b' ((m.1 * u + m.2.2) / m.2.1) * gJw (-b) b' m with hW
  have hW0 : ∀ b' m, 0 ≤ W b' m := fun b' m => mul_nonneg (hg _ _) (gJw_nonneg _ _ _)
  have hterm : ∀ m₂ ∈ P2 M₂, ∀ b' : (ZMod q)ˣ, ∀ m₂' ∈ P2 M₂, ∀ m ∈ R3 A M₂,
      (m₂ : ℝ) * m₂' * (if (m : ZMod q) = (b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q) then
        g b' ((m₂ * u + m) / m₂') else 0) ≤ 4 * M₂ ^ 2 / q * W b' (m₂, m₂', m) := by
    intro m₂ hm₂ b' m₂' hm₂' m _
    have h2 := (mem_P2 m₂).1 hm₂
    have h2' := (mem_P2 m₂').1 hm₂'
    split_ifs with hc
    · have hw : W b' (m₂, m₂', m) = g b' ((m₂ * u + m) / m₂') * q := by
        show g b' ((m₂ * u + m) / m₂') * gJw (-b) b' (m₂, m₂', m) = _
        rw [gJw_neg_eq b b' hc]
      rw [hw]
      have hmm : (m₂ : ℝ) * m₂' ≤ 4 * M₂ ^ 2 := by nlinarith [h2.1, h2.2, h2'.1, h2'.2]
      have hg0 := hg b' ((m₂ * u + m) / m₂')
      calc (m₂ : ℝ) * m₂' * g b' ((m₂ * u + m) / m₂') ≤ 4 * M₂ ^ 2 * g b' ((m₂ * u + m) / m₂') :=
            mul_le_mul_of_nonneg_right hmm hg0
        _ = 4 * M₂ ^ 2 / q * (g b' ((m₂ * u + m) / m₂') * q) := by field_simp
    · rw [mul_zero]
      exact mul_nonneg (by positivity) (hW0 _ _)
  calc _ = ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂, ∑ m ∈ R3 A M₂, (m₂ : ℝ) * m₂' *
        (if (m : ZMod q) = (b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q) then
          g b' ((m₂ * u + m) / m₂') else 0) := by simp only [Finset.mul_sum]
    _ ≤ ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂, ∑ m ∈ R3 A M₂, 4 * M₂ ^ 2 / q * W b' (m₂, m₂', m) :=
        Finset.sum_le_sum fun m₂ hm₂ => Finset.sum_le_sum fun b' _ => Finset.sum_le_sum fun m₂' hm₂' =>
          Finset.sum_le_sum fun m hm => hterm m₂ hm₂ b' m₂' hm₂' m hm
    _ = 4 * M₂ ^ 2 / q * ∑ b' : (ZMod q)ˣ, ∑ x ∈ P2 M₂ ×ˢ P2 M₂ ×ˢ R3 A M₂, W b' x := by
        simp only [Finset.sum_product, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ 4 * M₂ ^ 2 / q * ∑ b' : (ZMod q)ˣ, ∑ x ∈ setJ M₂ M₂ M₂ (4 * |A| + 2), W b' x := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b' _ => ?_) (by positivity)
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun x _ _ => hW0 b' x
        simp only [Finset.mem_product] at hx
        exact mem_setJ_of hx.1 hx.2.1 hx.2.2
    _ = _ := rfl

/-! ### Support, continuity and integrability -/

/-- For `T > 0` and `f_b` that are `0` for `|u| > A`, `f̃_b(x) = 0` for `|x| > |A| + 2/T`. -/
lemma ftil_eq_zero {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) {T : ℝ}
    (hT : 0 < T) (b : (ZMod q)ˣ) {x : ℝ} (hx : |A| + 2 / T < |x|) : ftil f T b x = 0 := by
  rw [ftil_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  show T * psi0 (T * t) * f b (x - t) = 0
  by_cases ht : 2 ≤ |T * t|
  · rw [psi0_eq_zero ht, mul_zero, zero_mul]
  · have ht' : |t| < 2 / T := by
      rw [lt_div_iff₀ hT]
      have := not_le.mp ht
      rw [abs_mul, abs_of_pos hT] at this
      linarith
    have h1 := abs_sub_abs_le_abs_sub x t
    rw [hA b (x - t) (by linarith [le_abs_self A]), mul_zero]

/-- A continuous `g` that is `0` for `|u| > A` is integrable. -/
lemma integrable_of_vanish {A : ℝ} {g : ℝ → ℝ} (hc : Continuous g) (h0 : ∀ u, A < |u| → g u = 0) :
    Integrable g :=
  hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_Icc (a := -|A|) (b := |A|)) fun u hu =>
    h0 u (lt_of_le_of_lt (le_abs_self A) (not_le.mp fun h => hu (abs_le.mp h))))

/-- For `T > 0` and integrable `f_b`, `u ↦ gJ(f̃, S, a, u)` is continuous. -/
lemma continuous_gJ_ftil {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfi : ∀ b, Integrable (f b)) {T : ℝ}
    (hT : 0 < T) (S : Finset (ℤ × ℤ × ℤ)) (a : (ZMod q)ˣ) : Continuous fun u => gJ (ftil f T) S a u := by
  unfold gJ
  refine continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun m _ => ?_
  exact ((continuous_ftil hT b (hfi b)).comp (by fun_prop)).mul continuous_const

/-- For `T > 0` and integrable `f_b`, `u ↦ Hmaj(b, m₂, b′, m₂′, u)` is continuous. -/
lemma continuous_Hmaj {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfi : ∀ b, Integrable (f b)) {T : ℝ}
    (hT : 0 < T) (A M₂ N₀ : ℝ) (K : ℕ) (b : (ZMod q)ˣ) (m₂ : ℤ) (b' : (ZMod q)ˣ) (m₂' : ℤ) :
    Continuous fun u => Hmaj f A M₂ T N₀ K b m₂ b' m₂' u := by
  unfold Hmaj
  refine continuous_const.mul (Continuous.add (continuous_finsetSum _ fun m _ => ?_) continuous_const)
  split_ifs
  · exact ((continuous_ftil hT b' (hfi b')).comp (by fun_prop)).div_const _
  · exact continuous_const

/-! ### Cauchy–Schwarz -/

/-- **Cauchy–Schwarz over `ℝ` and a finite index**: for continuous `F_i, G_i ≥ 0` with `Σ_iF_i²` and `Σ_iG_i²`
integrable, `∫Σ_iF_iG_i ≤ √(∫Σ_iF_i²)√(∫Σ_iG_i²)`. -/
lemma integral_sum_mul_le {ι : Type*} [Fintype ι] {F G : ι → ℝ → ℝ} (hF : ∀ i, Continuous (F i))
    (hG : ∀ i, Continuous (G i)) (hF0 : ∀ i u, 0 ≤ F i u) (hG0 : ∀ i u, 0 ≤ G i u)
    (hF2 : Integrable fun u => ∑ i, F i u ^ 2) (hG2 : Integrable fun u => ∑ i, G i u ^ 2) :
    ∫ u, ∑ i, F i u * G i u ≤ √(∫ u, ∑ i, F i u ^ 2) * √(∫ u, ∑ i, G i u ^ 2) := by
  set P : ℝ → ℝ := fun u => √(∑ i, F i u ^ 2) with hP
  set Q : ℝ → ℝ := fun u => √(∑ i, G i u ^ 2) with hQ
  have hPc : Continuous P := (continuous_finsetSum _ fun i _ => (hF i).pow 2).sqrt
  have hQc : Continuous Q := (continuous_finsetSum _ fun i _ => (hG i).pow 2).sqrt
  have hP2 : ∀ u, P u ^ 2 = ∑ i, F i u ^ 2 := fun u => Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hQ2 : ∀ u, Q u ^ 2 = ∑ i, G i u ^ 2 := fun u => Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hPm : MemLp P (ENNReal.ofReal 2) := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hPc.aestronglyMeasurable).2
      (hF2.congr (Eventually.of_forall fun u => (hP2 u).symm))
  have hQm : MemLp Q (ENNReal.ofReal 2) := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hQc.aestronglyMeasurable).2
      (hG2.congr (Eventually.of_forall fun u => (hQ2 u).symm))
  have hPn : ∀ u, 0 ≤ P u := fun u => Real.sqrt_nonneg _
  have hQn : ∀ u, 0 ≤ Q u := fun u => Real.sqrt_nonneg _
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall hPn) (Eventually.of_forall hQn) hPm hQm
  have e1 : ∫ u, P u ^ (2 : ℝ) = ∫ u, ∑ i, F i u ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun u => by
      show P u ^ (2 : ℝ) = _; rw [Real.rpow_two]; exact hP2 u)
  have e2 : ∫ u, Q u ^ (2 : ℝ) = ∫ u, ∑ i, G i u ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun u => by
      show Q u ^ (2 : ℝ) = _; rw [Real.rpow_two]; exact hQ2 u)
  rw [e1, e2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  have hPQ : Integrable fun u => P u * Q u := by
    have hint : Integrable fun u => (∑ i, F i u ^ 2 + ∑ i, G i u ^ 2) / 2 := (hF2.add hG2).div_const 2
    refine hint.mono' (hPc.mul hQc).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hPn u) (hQn u)), ← hP2, ← hQ2]
    nlinarith [sq_nonneg (P u - Q u)]
  have hpt : ∀ u, ∑ i, F i u * G i u ≤ P u * Q u := fun u =>
    Real.sum_mul_le_sqrt_mul_sqrt _ (fun i => F i u) (fun i => G i u)
  exact (integral_mono_of_nonneg (Eventually.of_forall fun u => Finset.sum_nonneg fun i _ =>
    mul_nonneg (hF0 i u) (hG0 i u)) hPQ (Eventually.of_forall hpt)).trans hcs

/-! ### Their `Σ_II` against `J(f̃⃗)` -/

/-- **The majorant summed**: for `q ≥ 1`, `f_b ≥ 0`, `T > 0` and `N₀ > 0`, for every unit `b` and real `u`,
`Σ_{m₂,b′,m₂′}m₂m₂′Hmaj(b, m₂, b′, m₂′, u) ≤ N₀C_K((4M₂²/(qT))gJ(f̃, setJ M₂ M₂ M₂ (4|A| + 2), −b, u) +
EP²Σ_{b′}∫f_{b′})`, with `E = (1 + N₀M₂/(qT))^{−(K−2)}(2π + 4π/N₀)` and `P = Σ_{m₂∈P2 M₂}m₂`. -/
lemma sum_Hmaj_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) {A T N₀ M₂ : ℝ}
    (hT : 0 < T) (hN₀ : 0 < N₀) (K : ℕ) (b : (ZMod q)ˣ) (u : ℝ) :
    ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂, (m₂ : ℝ) * m₂' * Hmaj f A M₂ T N₀ K b m₂ b' m₂' u ≤
      N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * gJ (ftil f T) (setJ M₂ M₂ M₂ (4 * |A| + 2)) (-b) u +
        ((1 + N₀ * M₂ / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) * (∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) ^ 2 *
          ∑ b' : (ZMod q)ˣ, ∫ v, f b' v) := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hCK : 0 ≤ CK K := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (norm_fourier_psiC_le_CK K 0)
  set E : ℝ := ((1 + N₀ * M₂ / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) with hE
  set Rs : ℤ → (ZMod q)ˣ → ℤ → ℝ := fun m₂ b' m₂' => ∑ m ∈ R3 A M₂,
    (if (m : ZMod q) = (b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q) then
      ftil f T b' ((m₂ * u + m) / m₂') else 0) with hRs
  have hterm : ∀ m₂ ∈ P2 M₂, ∀ b' : (ZMod q)ˣ, ∀ m₂' ∈ P2 M₂,
      (m₂ : ℝ) * m₂' * Hmaj f A M₂ T N₀ K b m₂ b' m₂' u ≤
        N₀ * CK K / T * ((m₂ : ℝ) * m₂' * Rs m₂ b' m₂') + N₀ * CK K * E * ((m₂ : ℝ) * (m₂' * ∫ v, f b' v)) := by
    intro m₂ hm₂ b' m₂' hm₂'
    have h2 := (mem_P2 m₂).1 hm₂
    have h2' := (mem_P2 m₂').1 hm₂'
    have hM : 0 < M₂ := by linarith [h2.1, h2.2]
    have hp2 : (0 : ℝ) < m₂ := by linarith [h2.1]
    have hp2' : (0 : ℝ) < m₂' := by linarith [h2'.1]
    have hI : 0 ≤ ∫ v, f b' v := integral_nonneg fun v => hf b' v
    have hEle : ((1 + N₀ * m₂' / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) ≤ E := by
      have h1 : N₀ * M₂ / (q * T) ≤ N₀ * m₂' / (q * T) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2'.1.le hN₀.le) (by positivity)
      exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) _))
        (by positivity)
    have hsum : (∑ m ∈ R3 A M₂, (if (m : ZMod q) = (b : ZMod q) * (m₂ : ZMod q) - (b' : ZMod q) * (m₂' : ZMod q)
        then ftil f T b' ((m₂ * u + m) / m₂') / T else 0)) = Rs m₂ b' m₂' / T := by
      simp only [hRs, Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> simp
    unfold Hmaj
    rw [hsum]
    have key : (m₂ : ℝ) * m₂' * (((1 + N₀ * m₂' / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) * ∫ v, f b' v) ≤
        (m₂ : ℝ) * m₂' * (E * ∫ v, f b' v) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hEle hI) (by positivity)
    calc (m₂ : ℝ) * m₂' * (N₀ * CK K * (Rs m₂ b' m₂' / T +
          ((1 + N₀ * m₂' / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) * ∫ v, f b' v))
        = N₀ * CK K / T * ((m₂ : ℝ) * m₂' * Rs m₂ b' m₂') + N₀ * CK K *
          ((m₂ : ℝ) * m₂' * (((1 + N₀ * m₂' / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) * ∫ v, f b' v)) := by
          ring
      _ ≤ N₀ * CK K / T * ((m₂ : ℝ) * m₂' * Rs m₂ b' m₂') + N₀ * CK K * ((m₂ : ℝ) * m₂' * (E * ∫ v, f b' v)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left key (mul_nonneg hN₀.le hCK))
      _ = _ := by ring
  have hR : ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂, N₀ * CK K / T * ((m₂ : ℝ) * m₂' * Rs m₂ b' m₂') ≤
      N₀ * CK K / T * (4 * M₂ ^ 2 / q * gJ (ftil f T) (setJ M₂ M₂ M₂ (4 * |A| + 2)) (-b) u) := by
    simp only [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_res_le_gJ (fun b' x => ftil_nonneg hT.le hf b' x) A M₂ b u)
      (div_nonneg (mul_nonneg hN₀.le hCK) hT.le)
  have hE' : ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂, N₀ * CK K * E * ((m₂ : ℝ) * (m₂' * ∫ v, f b' v)) =
      N₀ * CK K * E * ((∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) ^ 2 * ∑ b' : (ZMod q)ˣ, ∫ v, f b' v) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  calc _ ≤ ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂, (N₀ * CK K / T * ((m₂ : ℝ) * m₂' * Rs m₂ b' m₂') +
        N₀ * CK K * E * ((m₂ : ℝ) * (m₂' * ∫ v, f b' v))) :=
        Finset.sum_le_sum fun m₂ hm₂ => Finset.sum_le_sum fun b' _ => Finset.sum_le_sum fun m₂' hm₂' =>
          hterm m₂ hm₂ b' m₂' hm₂'
    _ = ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂, N₀ * CK K / T * ((m₂ : ℝ) * m₂' * Rs m₂ b' m₂') +
        ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂, N₀ * CK K * E * ((m₂ : ℝ) * (m₂' * ∫ v, f b' v)) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ N₀ * CK K / T * (4 * M₂ ^ 2 / q * gJ (ftil f T) (setJ M₂ M₂ M₂ (4 * |A| + 2)) (-b) u) +
        N₀ * CK K * E * ((∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) ^ 2 * ∑ b' : (ZMod q)ˣ, ∫ v, f b' v) := by
        rw [hE']; exact add_le_add hR le_rfl
    _ = _ := by ring

/-- **Their `Σ_II` against `J(f̃⃗)`**: for `q ≥ 1`, smooth `f_b ≥ 0` that are `0` for `|u| > A`, `T ≥ 1`, `N₀ > 0`,
`M₂ > 0` and `K ≥ 2`, `Σ_{n∈P3 N₀}ψ̃₀(n/N₀)|Φ(n, τ)|² ≤ N₀C_K((4M₂²/(qT))√𝔖√J̃ + EP²F²)` for every `L` and `τ`, with
`𝔖 = ∫Σ_bf_b²`, `J̃ = Jint(f̃, M₂, M₂, M₂, 4|A| + 2)`, `E = (1 + N₀M₂/(qT))^{−(K−2)}(2π + 4π/N₀)`,
`P = Σ_{m₂∈P2 M₂}m₂` and `F = Σ_b∫f_b`. -/
theorem sum_psi_norm_Phi_sq_le_J {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) (hf : ∀ b u, 0 ≤ f b u) {T N₀ M₂ : ℝ} (hT : 1 ≤ T) (hN₀ : 0 < N₀)
    (hM₂ : 0 < M₂) {K : ℕ} (hK : 2 ≤ K) (L τ : ℝ) :
    ∑ n ∈ P3 N₀, psi0 (n / N₀) * ‖Phi f M₂ L n τ‖ ^ 2 ≤
      N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * √(∫ u, ∑ b, f b u ^ 2) * √(Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2)) +
        ((1 + N₀ * M₂ / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) * (∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) ^ 2 *
          (∑ b, ∫ u, f b u) ^ 2) := by
  classical
  have hT0 : 0 < T := by linarith
  have hCK : 0 ≤ CK K := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (norm_fourier_psiC_le_CK K 0)
  have hfc : ∀ b, Continuous (f b) := fun b => (hfs b).continuous
  have hfi : ∀ b, Integrable (f b) := fun b => integrable_of_vanish (hfc b) (hA b)
  have h0 := sum_psi_norm_Phi_sq_le_ftil (q := q) hfs hA hf hT hN₀ hK M₂ L τ
  set S := setJ M₂ M₂ M₂ (4 * |A| + 2) with hS
  set E : ℝ := ((1 + N₀ * M₂ / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) with hE
  set P : ℝ := ∑ m₂ ∈ P2 M₂, (m₂ : ℝ) with hP
  set F : ℝ := ∑ b, ∫ u, f b u with hF
  set G : (ZMod q)ˣ → ℝ → ℝ := fun b u => gJ (ftil f T) S (-b) u with hG
  set H : (ZMod q)ˣ → ℝ → ℝ := fun b u => ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂,
    (m₂ : ℝ) * m₂' * Hmaj f A M₂ T N₀ K b m₂ b' m₂' u with hH
  have hB : ∀ b u, H b u ≤ N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * G b u + E * P ^ 2 * F) := fun b u =>
    sum_Hmaj_le hf hT0 hN₀ K b u
  clear_value E P F
  have hGc : ∀ b, Continuous (G b) := fun b => continuous_gJ_ftil hfi hT0 S (-b)
  have hG0 : ∀ b u, 0 ≤ G b u := fun b u => Finset.sum_nonneg fun b' _ => Finset.sum_nonneg fun m _ =>
    mul_nonneg (ftil_nonneg hT0.le hf b' _) (gJw_nonneg _ _ _)
  have hHc : ∀ b, Continuous (H b) := fun b => continuous_finsetSum _ fun m₂ _ => continuous_finsetSum _
    fun b' _ => continuous_finsetSum _ fun m₂' _ =>
      continuous_const.mul (continuous_Hmaj hfi hT0 A M₂ N₀ K b m₂ b' m₂')
  have hI : ∀ b m₂ b' m₂', Integrable fun u => f b u * Hmaj f A M₂ T N₀ K b m₂ b' m₂' u := fun b m₂ b' m₂' =>
    integrable_of_vanish ((hfc b).mul (continuous_Hmaj hfi hT0 A M₂ N₀ K b m₂ b' m₂'))
      fun u hu => by rw [hA b u hu, zero_mul]
  -- the sums into the integral
  have hex : ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂,
      (m₂ : ℝ) * m₂' * ∫ u, f b u * Hmaj f A M₂ T N₀ K b m₂ b' m₂' u = ∫ u, ∑ b, f b u * H b u := by
    have hpt : ∀ u, ∑ b, f b u * H b u = ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂,
        (m₂ : ℝ) * m₂' * (f b u * Hmaj f A M₂ T N₀ K b m₂ b' m₂' u) := fun u => by
      simp only [hH, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m₂ _ => Finset.sum_congr rfl fun b' _ =>
        Finset.sum_congr rfl fun m₂' _ => by ring
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum _ fun b _ => ?_]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_finsetSum _ fun m₂ _ => ?_]
      · refine Finset.sum_congr rfl fun m₂ _ => ?_
        rw [integral_finsetSum _ fun b' _ => ?_]
        · refine Finset.sum_congr rfl fun b' _ => ?_
          rw [integral_finsetSum _ fun m₂' _ => ?_]
          · exact Finset.sum_congr rfl fun m₂' _ => (integral_const_mul _ _).symm
          · exact (hI b m₂ b' m₂').const_mul _
        · exact integrable_finsetSum _ fun m₂' _ => (hI b m₂ b' m₂').const_mul _
      · exact integrable_finsetSum _ fun b' _ => integrable_finsetSum _ fun m₂' _ => (hI b m₂ b' m₂').const_mul _
    · exact integrable_finsetSum _ fun m₂ _ => integrable_finsetSum _ fun b' _ =>
        integrable_finsetSum _ fun m₂' _ => (hI b m₂ b' m₂').const_mul _
  -- the majorant summed, under the integral
  have hLi : Integrable fun u => ∑ b, f b u * H b u :=
    integrable_of_vanish (continuous_finsetSum _ fun b _ => (hfc b).mul (hHc b))
      fun u hu => Finset.sum_eq_zero fun b _ => by rw [hA b u hu, zero_mul]
  have hRi : Integrable fun u => ∑ b, f b u * (N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * G b u + E * P ^ 2 * F)) :=
    integrable_of_vanish (continuous_finsetSum _ fun b _ => (hfc b).mul (continuous_const.mul
      ((continuous_const.mul (hGc b)).add continuous_const)))
      fun u hu => Finset.sum_eq_zero fun b _ => by rw [hA b u hu, zero_mul]
  have h3 : ∫ u, ∑ b, f b u * H b u ≤
      ∫ u, ∑ b, f b u * (N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * G b u + E * P ^ 2 * F)) :=
    integral_mono hLi hRi fun u => Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hB b u) (hf b u)
  -- linearity
  have hFG : Integrable fun u => ∑ b, f b u * G b u :=
    integrable_of_vanish (continuous_finsetSum _ fun b _ => (hfc b).mul (hGc b))
      fun u hu => Finset.sum_eq_zero fun b _ => by rw [hA b u hu, zero_mul]
  have h4 : ∫ u, ∑ b, f b u * (N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * G b u + E * P ^ 2 * F)) =
      N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * (∫ u, ∑ b, f b u * G b u) + E * P ^ 2 * F * F) := by
    have e : ∀ u, ∑ b, f b u * (N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * G b u + E * P ^ 2 * F)) =
        N₀ * CK K * (4 * M₂ ^ 2 / (q * T)) * ∑ b, f b u * G b u + N₀ * CK K * (E * P ^ 2 * F) * ∑ b, f b u :=
      fun u => by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring
    rw [integral_congr_ae (Eventually.of_forall e), integral_add (hFG.const_mul _)
      ((integrable_finsetSum _ fun b _ => hfi b).const_mul _), integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun b _ => hfi b, ← hF]
    ring
  -- Cauchy–Schwarz
  have hF2 : Integrable fun u => ∑ b, f b u ^ 2 := integrable_finsetSum _ fun b _ =>
    integrable_of_vanish ((hfc b).pow 2) fun u hu => by rw [hA b u hu]; ring
  have hre : ∀ u, ∑ b, G b u ^ 2 = ∑ a, gJ (ftil f T) S a u ^ 2 := fun u =>
    Equiv.sum_comp (Equiv.neg (ZMod q)ˣ) (fun a => gJ (ftil f T) S a u ^ 2)
  have hG2 : Integrable fun u => ∑ b, G b u ^ 2 :=
    (integrable_Jsum (fun b => continuous_ftil hT0 b (hfi b)) (fun b u hu => ftil_eq_zero hA hT0 b hu)
      hM₂.le hM₂ (M₃ := M₂) (κ := 4 * |A| + 2)).congr (Eventually.of_forall fun u => (hre u).symm)
  have hcs := integral_sum_mul_le hfc hGc hf hG0 hF2 hG2
  have hJ : ∫ u, ∑ b, G b u ^ 2 = Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2) :=
    integral_congr_ae (Eventually.of_forall hre)
  rw [hJ] at hcs
  have hk : (0 : ℝ) ≤ 4 * M₂ ^ 2 / (q * T) := by positivity
  calc ∑ n ∈ P3 N₀, psi0 (n / N₀) * ‖Phi f M₂ L n τ‖ ^ 2
      ≤ ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, ∑ b' : (ZMod q)ˣ, ∑ m₂' ∈ P2 M₂,
          (m₂ : ℝ) * m₂' * ∫ u, f b u * Hmaj f A M₂ T N₀ K b m₂ b' m₂' u := h0
    _ = ∫ u, ∑ b, f b u * H b u := hex
    _ ≤ _ := h3
    _ = N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * (∫ u, ∑ b, f b u * G b u) + E * P ^ 2 * F * F) := h4
    _ ≤ N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * (√(∫ u, ∑ b, f b u ^ 2) * √(Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2))) +
          E * P ^ 2 * F * F) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hcs hk) le_rfl)
          (mul_nonneg hN₀.le hCK)
    _ = _ := by ring

/-! ### The terms `|n| ≤ N₀` of `B_II` -/

/-- For `f_b ≥ 0`, `|Φ(n, τ)| ≤ Σ_bΣ_{m₂∈P2 M₂}|m₂|∫f_b`. -/
lemma norm_Phi_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) (M₂ L : ℝ) (n : ℤ)
    (τ : ℝ) : ‖Phi f M₂ L n τ‖ ≤ ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, |(m₂ : ℝ)| * ∫ u, f b u := by
  unfold Phi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun m₂ _ => ?_))
  rw [norm_mul, norm_stdAddChar, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_fourier_fC_le hf b _) (abs_nonneg _)

/-- For smooth `f_b` that are `0` for `|u| > A`, `τ ↦ Φ(n, τ)` is continuous. -/
lemma continuous_Phi {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) (M₂ L : ℝ) (n : ℤ) : Continuous fun τ => Phi f M₂ L n τ := by
  unfold Phi
  refine continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun m₂ _ => ?_
  exact (continuous_const.mul ((continuous_fourier_fC hfs hA b).comp (by fun_prop))).mul continuous_const

/-- `τ ↦ |ψ̂₀(−τ)|` is integrable. -/
lemma integrable_norm_fourier_psiC_neg : Integrable fun τ : ℝ => ‖𝓕 psiC (-τ)‖ :=
  (integrable_kloc.norm.comp_mul_left' (R := -1) (by norm_num)).congr
    (Eventually.of_forall fun τ => by simp only [kloc, neg_one_mul])

/-- **The terms `|n| ≤ N₀` of `B_II`**: for `q ≥ 1`, smooth `f_b ≥ 0` that are `0` for `|u| > A`, `T ≥ 1`,
`N₀ > 0`, `M₂ > 0` and `K ≥ 2`, `Σ_{n∈W, |n|≤N₀}∫|ψ̂₀(−τ)||Φ(n, τ)|² dτ ≤ (∫|ψ̂₀(−τ)| dτ)B_J` for every `L` and every
finite set `W` of integers, with `B_J` the bound of `sum_psi_norm_Phi_sq_le_J`. -/
theorem sum_integral_Phi_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) (hf : ∀ b u, 0 ≤ f b u) {T N₀ M₂ : ℝ} (hT : 1 ≤ T) (hN₀ : 0 < N₀)
    (hM₂ : 0 < M₂) {K : ℕ} (hK : 2 ≤ K) (L : ℝ) (W : Finset ℤ) :
    ∑ n ∈ W.filter (fun n : ℤ => |(n : ℝ)| ≤ N₀), ∫ τ, ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2 ≤
      (∫ τ, ‖𝓕 psiC (-τ)‖) *
        (N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * √(∫ u, ∑ b, f b u ^ 2) * √(Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2)) +
          ((1 + N₀ * M₂ / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) * (∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) ^ 2 *
            (∑ b, ∫ u, f b u) ^ 2)) := by
  classical
  set B := N₀ * CK K * (4 * M₂ ^ 2 / (q * T) * √(∫ u, ∑ b, f b u ^ 2) *
    √(Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2)) + ((1 + N₀ * M₂ / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) *
      (∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) ^ 2 * (∑ b, ∫ u, f b u) ^ 2) with hB
  have hw := integrable_norm_fourier_psiC_neg
  have hΦi : ∀ n : ℤ, Integrable fun τ => ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2 := fun n =>
    hw.mul_bdd (c := (∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, |(m₂ : ℝ)| * ∫ u, f b u) ^ 2)
      ((continuous_Phi hfs hA M₂ L n).norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_Phi_le hf M₂ L n τ) 2)
  have hsub : W.filter (fun n : ℤ => |(n : ℝ)| ≤ N₀) ⊆ P3 N₀ := fun n hn => by
    have h := (Finset.mem_filter.1 hn).2
    have c := Int.le_ceil (2 * N₀)
    have a := abs_le.mp h
    unfold P3
    rw [Finset.mem_Icc]
    constructor
    · have : -((⌈2 * N₀⌉ : ℤ) : ℝ) ≤ (n : ℝ) := by linarith
      exact_mod_cast this
    · have : (n : ℝ) ≤ ((⌈2 * N₀⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  have hle : ∀ τ, ∑ n ∈ W.filter (fun n : ℤ => |(n : ℝ)| ≤ N₀), ‖Phi f M₂ L n τ‖ ^ 2 ≤ B := fun τ => by
    refine le_trans ?_ (sum_psi_norm_Phi_sq_le_J hfs hA hf hT hN₀ hM₂ hK L τ)
    calc ∑ n ∈ W.filter (fun n : ℤ => |(n : ℝ)| ≤ N₀), ‖Phi f M₂ L n τ‖ ^ 2
        = ∑ n ∈ W.filter (fun n : ℤ => |(n : ℝ)| ≤ N₀), psi0 (n / N₀) * ‖Phi f M₂ L n τ‖ ^ 2 :=
          Finset.sum_congr rfl fun n hn => by
            have h := (Finset.mem_filter.1 hn).2
            rw [psi0_eq_one (by rw [abs_div, abs_of_pos hN₀, div_le_one hN₀]; exact h), one_mul]
      _ ≤ ∑ n ∈ P3 N₀, psi0 (n / N₀) * ‖Phi f M₂ L n τ‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => mul_nonneg (psi0_nonneg _) (sq_nonneg _)
  calc ∑ n ∈ W.filter (fun n : ℤ => |(n : ℝ)| ≤ N₀), ∫ τ, ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2
      = ∫ τ, ∑ n ∈ W.filter (fun n : ℤ => |(n : ℝ)| ≤ N₀), ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2 :=
        (integral_finsetSum _ fun n _ => hΦi n).symm
    _ ≤ ∫ τ, ‖𝓕 psiC (-τ)‖ * B :=
        integral_mono (integrable_finsetSum _ fun n _ => hΦi n) (hw.mul_const B) fun τ => by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (hle τ) (norm_nonneg _)
    _ = (∫ τ, ‖𝓕 psiC (-τ)‖) * B := integral_mul_const B _

end LinnikCGLJtil

#print axioms LinnikCGLJtil.sum_res_le_gJ
#print axioms LinnikCGLJtil.integral_sum_mul_le
#print axioms LinnikCGLJtil.sum_Hmaj_le
#print axioms LinnikCGLJtil.sum_psi_norm_Phi_sq_le_J
#print axioms LinnikCGLJtil.sum_integral_Phi_le
