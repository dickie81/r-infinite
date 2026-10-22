/-
# Round 666: `S₃,₃`, `S₃,₄` and the block sums of `Ĩ`, by their Proposition 8.1 and Lemmas 9.1 and 9.2 (the CGL plan's
stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 662 bounds `S₃,₄` on the dyadic block `k` of round 657's `prop72` by sums of their `J`, round 663 does so at its
`f_b` (`S34_le_fb`), and round 665 proves the decay premise of their Proposition 8.1 for this `f_b` (`fb_decay_all`).
This file applies round 662's `CGLP81` to it. Their step: "Applying Proposition 8.1 then gives that S₃,₃ and S₃,₄ are
both bounded by ⪅ ϕ(q)M₂⁶ (∫_ℝ Σ_{b mod q, (b,q)=1} |R̃_{M₂}(u,−b)|² ψ(u) du)² + ϕ(q)²M₂⁴ ∫_ℝ Σ_{b mod q, (b,q)=1}
|R̃_{M₂}(u,−b)|⁴ ψ(u)² du" (text layer lines 5829–5847; spaces restored; the integrals, sums, tildes, large parentheses,
subscripts and exponents transcribed; the text layer's `R` under the integrals is the PDF's blackboard `ℝ`, `MSBM10`
glyphs at y = 139.2, x = 155.4 and 382.5 on page 49, `scratchpad/r671/probe/p49_all.txt`), and "This yields, by Lemmas
9.1 and 9.2, S₃,₃, S₃,₄ ⪅_ϵ ϕ(q)³M₂⁶|W|² + ϕ(q)³M₂⁴E(W)." (lines 5848–5851; spaces restored; the subscripts and
exponents transcribed).

The stack's form. On the block `k`, `M₂ = 2^k`, and `CGLP81` is applied with `M = 2^{k+1}`, the support bound `4`,
`κ = 2` and round 665's `D_j`. Its bound holds for every `0 < M_i < M`, so it covers the `k + 1` terms of round 662's
reduction, and `S₃,₄ ≤ 4(k + 1)²C(qT)^ε(φ(q)M⁶(∫Σ_bf_b)² + φ(q)²M⁴∫Σ_bf_b²)`. Since `0 ≤ ψ ≤ 1`, `∫Σ_bf_b ≤ ∫Σ_aR̃²`,
which round 658's `lemma91_Rt` evaluates as `2X∫ψ̃₀·(3/2)φ(q)|R|`, and `∫Σ_bf_b² ≤ ∫Σ_aR̃⁴`, which round 659's
`lemma92_Rt` bounds by `(2X∫ψ̃₀)²·2φ(q)X(∫ψ̃₀·E + |R|⁴D_K/X^K)`. With `X ≥ 1` the two combine to
`S₃,₄ ≤ V = 4(k + 1)²C(qT)^ε(∫ψ̃₀)²X³φ(q)³(9M⁶|R|² + 8M⁴(∫ψ̃₀·E + |R|⁴D_K/X^K))`, their bound with the error term of
Lemma 9.2 kept. Round 662's `S33_le_S34` gives `S₃,₃ ≤ 4V`. Round 660's two Cauchy–Schwarz steps and round 658's
`lemma91` then give `(Σ_{m⃗∈B}Ĩ(m⃗))² ≤ S₃,₁·√S₃,₃√S₃,₄ ≤ (3/2)φ(q)|R|·2V`. `CGLP81` does not say `C ≥ 0`; the stack
uses `max(C, 0)`.

Plain statements, with `q ≥ 1`, `L = NM₂/q`, `E` the energy and, on the block `k`, `M₂ = 2^k` and `M = 2^{k+1}`.
* `integral_sum_fb_le`: for `χ` injective on `R` and `L, X > 0`, `∫Σ_bf_b ≤ 2X∫ψ̃₀·(3/2)φ(q)|R|`.
* `integral_sum_fb_sq_le`: for `L > 0`, `X ≥ 1` and `K ∈ ℕ`,
  `∫Σ_bf_b² ≤ (2X∫ψ̃₀)²·2φ(q)X(∫ψ̃₀·E + |R|⁴D_K/X^K)`.
* `S34_le_P81`: from `CGLP81`, for `0 < ϖ < 1` and `ε > 0` there are `C ≥ 0` and `Q₀` such that, for `qT ≥ Q₀`,
  `T ≥ 1`, points `|t_i| ≤ T`, `N, X > 0`, `L ≤ XT` and `M ≤ (qT)^ϖ`,
  `S₃,₄ ≤ 4(k + 1)²C(qT)^ε(φ(q)M⁶(∫Σ_bf_b)² + φ(q)²M⁴∫Σ_bf_b²)` on the block `k`.
* `block_le`: from `CGLP81`, for `0 < ϖ < 1`, `ε > 0` and `K ∈ ℕ` there are `C ≥ 0` and `Q₀` such that, under the
  hypotheses of `S34_le_P81` with `X ≥ 1` and `χ` injective on `R`, the block `k` has `S₃,₄ ≤ V`, `S₃,₃ ≤ 4V` and
  `(Σ_{m⃗∈B}Ĩ(m⃗))² ≤ 3φ(q)|R|V`.

* `hasCompactSupport_fb`, `integrable_fb`, `integrable_fb_sq`, `integrable_Rt_four`: integrability.
* `integral_sum_fb_le`, `integral_sum_fb_sq_le`: the two moments of `f`.
* `S34_le_P81`, `Vblk`, `block_le`: the block `k`.

The file imports `LinnikCGLDecay.lean`.
-/

import LinnikCGLDecay

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLBlock

open LinnikCGLRFact LinnikCGLP71 LinnikCGLRt LinnikCGLP72 LinnikCGLMom LinnikCGLMom4 LinnikCGLCS LinnikCGLJ
  LinnikCGLFb LinnikCGLDecay

universe u

/-! ### The two moments of `f` -/

section moments

variable {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
  {X M₂ : ℝ}

lemma hasCompactSupport_fb (b : (ZMod q)ˣ) : HasCompactSupport (fb N R χ t X M₂ b) :=
  HasCompactSupport.intro (isCompact_Icc (a := -4) (b := 4)) fun u hu => fb_eq_zero R χ t b (by
    by_contra h
    push Not at h
    exact hu (abs_le.mp h))

lemma integrable_fb (hL : 0 < N * M₂ / q) (hX : 0 < X) (b : (ZMod q)ˣ) : Integrable (fb N R χ t X M₂ b) :=
  (contDiff_fb R χ t hL hX b).continuous.integrable_of_hasCompactSupport (hasCompactSupport_fb R χ t b)

lemma integrable_fb_sq (hL : 0 < N * M₂ / q) (hX : 0 < X) (b : (ZMod q)ˣ) :
    Integrable fun u => fb N R χ t X M₂ b u ^ 2 :=
  ((contDiff_fb R χ t hL hX b).continuous.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -4) (b := 4)) fun u hu => by
      rw [Pi.pow_apply, fb_eq_zero R χ t b (by by_contra h; push Not at h; exact hu (abs_le.mp h)),
        zero_pow two_ne_zero])

omit [NeZero q] in
/-- `v ↦ R̃_{M₂}(v, a)⁴` is integrable for `L, X > 0`: `R̃⁴ ≤ (3/2)L|R|²·R̃²`. -/
lemma integrable_Rt_four (hX : 0 < X) (hL : 0 < N * M₂ / q) (a : ZMod q) :
    Integrable fun v => Rt N R χ t X M₂ v a ^ 4 := by
  refine ((integral_Rt_sq R χ t hX hL a).1.const_mul (3 / 2 * (N * M₂ / q) * (R.card : ℝ) ^ 2)).mono'
    ((measurable_Rt N R χ t X M₂ a).pow_const 4).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  have h1 := Rt_sq_le R χ t (X := X) hL.le v a
  have h2 := sq_nonneg (Rt N R χ t X M₂ v a)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc Rt N R χ t X M₂ v a ^ 4 = Rt N R χ t X M₂ v a ^ 2 * Rt N R χ t X M₂ v a ^ 2 := by ring
    _ ≤ 3 / 2 * (N * M₂ / q) * (R.card : ℝ) ^ 2 * Rt N R χ t X M₂ v a ^ 2 := mul_le_mul_of_nonneg_right h1 h2

/-- **The first moment of `f`, by their Lemma 9.1**: `∫Σ_bf_b ≤ 2X∫ψ̃₀·(3/2)φ(q)|R|` for `χ` injective on `R` and
`L, X > 0`. -/
lemma integral_sum_fb_le (hinj : Set.InjOn χ R) (hX : 0 < X) (hL : 0 < N * M₂ / q) :
    ∫ u, ∑ b, fb N R χ t X M₂ b u ≤ 2 * X * (∫ x, psi0 x) * (3 / 2 * (q.totient * R.card)) := by
  rw [← lemma91_Rt R hinj t hX hL]
  refine integral_mono (integrable_finsetSum _ fun b _ => integrable_fb R χ t hL hX b)
    (integrable_finsetSum _ fun a _ => (integral_Rt_sq R χ t hX hL (a : ZMod q)).1) fun u => ?_
  calc ∑ b, fb N R χ t X M₂ b u ≤ ∑ b : (ZMod q)ˣ, Rt N R χ t X M₂ u ((-b : (ZMod q)ˣ) : ZMod q) ^ 2 :=
        Finset.sum_le_sum fun b _ => mul_le_of_le_one_left (sq_nonneg _) (psiW_le_one u)
    _ = ∑ a : (ZMod q)ˣ, Rt N R χ t X M₂ u a ^ 2 := Fintype.sum_equiv (Equiv.neg _) _ _ fun b => rfl

/-- **The second moment of `f`, by their Lemma 9.2**: for `L > 0`, `X ≥ 1` and `K ∈ ℕ`,
`∫Σ_bf_b² ≤ (2X∫ψ̃₀)²·2φ(q)X(∫ψ̃₀·E + |R|⁴D_K/X^K)`. -/
lemma integral_sum_fb_sq_le (hX : 1 ≤ X) (hL : 0 < N * M₂ / q) (K : ℕ) :
    ∫ u, ∑ b, fb N R χ t X M₂ b u ^ 2 ≤ (2 * X * ∫ x, psi0 x) ^ 2 *
      (2 * q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K)) := by
  have hX0 : 0 < X := by linarith
  refine le_trans ?_ (lemma92_Rt R χ t hX hL K)
  refine integral_mono (integrable_finsetSum _ fun b _ => integrable_fb_sq R χ t hL hX0 b)
    (integrable_finsetSum _ fun a _ => integrable_Rt_four R χ t hX0 hL (a : ZMod q)) fun u => ?_
  calc ∑ b, fb N R χ t X M₂ b u ^ 2 ≤ ∑ b : (ZMod q)ˣ, Rt N R χ t X M₂ u ((-b : (ZMod q)ˣ) : ZMod q) ^ 4 := by
        refine Finset.sum_le_sum fun b _ => ?_
        unfold fb
        have h1 := psiW_nonneg u
        have h2 := psiW_le_one u
        have h3 : 0 ≤ Rt N R χ t X M₂ u ((-b : (ZMod q)ˣ) : ZMod q) ^ 4 := by positivity
        calc (psiW u * Rt N R χ t X M₂ u ((-b : (ZMod q)ˣ) : ZMod q) ^ 2) ^ 2
            = psiW u ^ 2 * Rt N R χ t X M₂ u ((-b : (ZMod q)ˣ) : ZMod q) ^ 4 := by ring
          _ ≤ 1 * Rt N R χ t X M₂ u ((-b : (ZMod q)ˣ) : ZMod q) ^ 4 :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ h1 h2) h3
          _ = Rt N R χ t X M₂ u ((-b : (ZMod q)ˣ) : ZMod q) ^ 4 := one_mul _
    _ = ∑ a : (ZMod q)ˣ, Rt N R χ t X M₂ u a ^ 4 := Fintype.sum_equiv (Equiv.neg _) _ _ fun b => rfl

end moments

/-! ### The block `k` -/

/-- **`S₃,₄` on the block `k`, by their Proposition 8.1**: from `CGLP81`, for `0 < ϖ < 1` and `ε > 0` there are
`C ≥ 0` and `Q₀` such that, for `qT ≥ Q₀`, `T ≥ 1`, points `|t_i| ≤ T`, `N, X > 0`, `L = 2^kN/q ≤ XT` and
`M = 2^{k+1} ≤ (qT)^ϖ`, `S₃,₄ ≤ 4(k + 1)²C(qT)^ε(φ(q)M⁶(∫Σ_bf_b)² + φ(q)²M⁴∫Σ_bf_b²)`. -/
theorem S34_le_P81 (hP : CGLP81) {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι)
      (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {X T : ℝ} (M k : ℕ), Q₀ ≤ (q : ℝ) * T → 1 ≤ T →
      (∀ i ∈ R, |t i| ≤ T) → 0 < N → 0 < X → N * 2 ^ k / q ≤ X * T → (2 : ℝ) ^ (k + 1) ≤ ((q : ℝ) * T) ^ ϖ →
      S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤ 4 * (k + 1) ^ 2 * C * ((q : ℝ) * T) ^ ε *
        ((q.totient : ℝ) * (2 ^ (k + 1)) ^ 6 * (∫ u, ∑ b, fb N R χ t X (2 ^ k) b u) ^ 2 +
          (q.totient : ℝ) ^ 2 * (2 ^ (k + 1)) ^ 4 * ∫ u, ∑ b, fb N R χ t X (2 ^ k) b u ^ 2) := by
  obtain ⟨C, Q₀, hCQ⟩ := hP ϖ hϖ0 hϖ1 4 2 Dfb ε hε
  refine ⟨max C 0, Q₀, le_max_right _ _, ?_⟩
  intro ι q hq0 N R χ t X T M k hQ hT ht hN hX hLX hMϖ
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hL : 0 < N * 2 ^ k / q := div_pos (mul_pos hN (by positivity)) hq
  obtain ⟨b₀, u₀, hdec⟩ := fb_decay_all R χ t hL hX hT ht hLX
  set f := fb N R χ t X (2 ^ k) with hf
  set Y := (q.totient : ℝ) * (2 ^ (k + 1)) ^ 6 * (∫ u, ∑ b, f b u) ^ 2 +
    (q.totient : ℝ) ^ 2 * (2 ^ (k + 1)) ^ 4 * ∫ u, ∑ b, f b u ^ 2 with hY
  have hY0 : 0 ≤ Y := by
    have : 0 ≤ ∫ u, ∑ b, f b u ^ 2 := integral_nonneg fun u => Finset.sum_nonneg fun b _ => sq_nonneg _
    exact add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (mul_nonneg (by positivity) this)
  have hqT : 0 ≤ ((q : ℝ) * T) ^ ε := Real.rpow_nonneg (mul_pos hq (by linarith)).le ε
  have hJ : ∀ j ∈ Finset.range (k + 1), Jint f (2 ^ j - 1 / 2) (2 ^ k - 1 / 2) (2 ^ k - 1 / 2) 2 ≤
      max C 0 * ((q : ℝ) * T) ^ ε * Y := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hjk
    have h3 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h4 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have hJ0 := hCQ q T (2 ^ (k + 1)) f b₀ u₀ hQ hT (by positivity) hMϖ (fun b => contDiff_fb R χ t hL hX b)
      (fun b u => fb_nonneg R χ t b u) (fun b _u hu => fb_eq_zero R χ t b hu) hdec (2 ^ j - 1 / 2)
      (2 ^ k - 1 / 2) (2 ^ k - 1 / 2) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith)
    refine hJ0.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hqT) hY0
  calc S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)
      ≤ 4 * (k + 1) * ∑ j ∈ Finset.range (k + 1), Jint f (2 ^ j - 1 / 2) (2 ^ k - 1 / 2) (2 ^ k - 1 / 2) 2 :=
        S34_le_fb R χ t hL hX
    _ ≤ 4 * (k + 1) * ∑ _j ∈ Finset.range (k + 1), max C 0 * ((q : ℝ) * T) ^ ε * Y :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hJ) (by positivity)
    _ = 4 * (k + 1) ^ 2 * max C 0 * ((q : ℝ) * T) ^ ε * Y := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- The bound `V` on the block `k`: `4(k + 1)²C(qT)^ε(∫ψ̃₀)²X³φ(q)³(9M⁶|R|² + 8M⁴(∫ψ̃₀·E + |R|⁴D_K/X^K))`, with
`M = 2^{k+1}`. -/
def Vblk {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (C ε T X : ℝ) (K k : ℕ) :
    ℝ :=
  4 * (k + 1) ^ 2 * C * ((q : ℝ) * T) ^ ε * ((∫ x, psi0 x) ^ 2 * X ^ 3 * (q.totient : ℝ) ^ 3 *
    (9 * (2 ^ (k + 1)) ^ 6 * (R.card : ℝ) ^ 2 +
      8 * (2 ^ (k + 1)) ^ 4 * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K)))

/-- **The block `k`, by their Proposition 8.1 and Lemmas 9.1 and 9.2**: from `CGLP81`, for `0 < ϖ < 1`, `ε > 0` and
`K ∈ ℕ` there are `C ≥ 0` and `Q₀` such that, for `χ` injective on `R`, `qT ≥ Q₀`, `T ≥ 1`, points `|t_i| ≤ T`,
`N > 0`, `X ≥ 1`, `L = 2^kN/q ≤ XT` and `2^{k+1} ≤ (qT)^ϖ`, the block `k` has `S₃,₄ ≤ V`, `S₃,₃ ≤ 4V` and
`(Σ_{m⃗∈B}Ĩ(m⃗))² ≤ 3φ(q)|R|V`, with `V = Vblk`. -/
theorem block_le (hP : CGLP81) {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1) {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι)
      (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {X T : ℝ} (M k : ℕ), Set.InjOn χ R → Q₀ ≤ (q : ℝ) * T →
      1 ≤ T → (∀ i ∈ R, |t i| ≤ T) → 0 < N → 1 ≤ X → N * 2 ^ k / q ≤ X * T →
      (2 : ℝ) ^ (k + 1) ≤ ((q : ℝ) * T) ^ ϖ →
      S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤ Vblk R χ t C ε T X K k ∧
      S33 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤ 4 * Vblk R χ t C ε T X K k ∧
      (∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2) ^ 2 ≤
        3 * q.totient * R.card * Vblk R χ t C ε T X K k := by
  obtain ⟨C, Q₀, hC0, hS⟩ := S34_le_P81 hP hϖ0 hϖ1 hε
  refine ⟨C, Q₀, hC0, ?_⟩
  intro ι q hq0 N R χ t X T M k hinj hQ hT ht hN hX hLX hMϖ
  have hX0 : 0 < X := by linarith
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hL : 0 < N * 2 ^ k / q := div_pos (mul_pos hN (by positivity)) hq
  have hqT : 0 ≤ ((q : ℝ) * T) ^ ε := Real.rpow_nonneg (mul_pos hq (by linarith)).le ε
  set Iψ := ∫ x, psi0 x with hI
  have hI0 : 0 ≤ Iψ := integral_nonneg psi0_nonneg
  set ph : ℝ := (q.totient : ℝ) with hφ
  set Rc : ℝ := (R.card : ℝ) with hRc
  set Mk : ℝ := (2 : ℝ) ^ (k + 1) with hMk
  set A1 := ∫ u, ∑ b, fb N R χ t X (2 ^ k) b u with hA1
  set A2 := ∫ u, ∑ b, fb N R χ t X (2 ^ k) b u ^ 2 with hA2
  set G := Iψ * energy R χ t + Rc ^ 4 * Dpsi K / X ^ K with hG
  have hA10 : 0 ≤ A1 := integral_nonneg fun u => Finset.sum_nonneg fun b _ => fb_nonneg R χ t b u
  have hA1le : A1 ≤ 2 * X * Iψ * (3 / 2 * (ph * Rc)) := integral_sum_fb_le R χ t hinj hX0 hL
  have hA2le : A2 ≤ (2 * X * Iψ) ^ 2 * (2 * ph * X * G) := integral_sum_fb_sq_le R χ t hX hL K
  have hφ0 : 0 ≤ ph := Nat.cast_nonneg _
  have hRc0 : 0 ≤ Rc := Nat.cast_nonneg _
  have hM0 : 0 ≤ Mk := by positivity
  have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hX (by norm_num)
  -- `S₃,₄ ≤ V`
  have hS34 : S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤ Vblk R χ t C ε T X K k := by
    refine (hS R χ t M k hQ hT ht hN hX0 hLX hMϖ).trans ?_
    unfold Vblk
    rw [← hI, ← hφ, ← hRc, ← hMk, ← hG, ← hA1, ← hA2]
    have hpre : 0 ≤ 4 * ((k : ℝ) + 1) ^ 2 * C * ((q : ℝ) * T) ^ ε :=
      mul_nonneg (mul_nonneg (by positivity) hC0) hqT
    refine mul_le_mul_of_nonneg_left ?_ hpre
    have h1 : A1 ^ 2 ≤ (2 * X * Iψ * (3 / 2 * (ph * Rc))) ^ 2 := pow_le_pow_left₀ hA10 hA1le 2
    have hc1 : 0 ≤ ph * Mk ^ 6 := mul_nonneg hφ0 (pow_nonneg hM0 6)
    have hc2 : 0 ≤ ph ^ 2 * Mk ^ 4 := mul_nonneg (sq_nonneg _) (pow_nonneg hM0 4)
    have hc3 : 0 ≤ 9 * (Iψ ^ 2 * ph ^ 3 * Mk ^ 6 * Rc ^ 2) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hφ0 3))
        (pow_nonneg hM0 6)) (sq_nonneg _))
    calc ph * Mk ^ 6 * A1 ^ 2 + ph ^ 2 * Mk ^ 4 * A2
        ≤ ph * Mk ^ 6 * (2 * X * Iψ * (3 / 2 * (ph * Rc))) ^ 2 +
            ph ^ 2 * Mk ^ 4 * ((2 * X * Iψ) ^ 2 * (2 * ph * X * G)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hc1) (mul_le_mul_of_nonneg_left hA2le hc2)
      _ = 9 * (Iψ ^ 2 * ph ^ 3 * Mk ^ 6 * Rc ^ 2) * X ^ 2 + Iψ ^ 2 * X ^ 3 * ph ^ 3 * (8 * Mk ^ 4 * G) := by
          ring
      _ ≤ 9 * (Iψ ^ 2 * ph ^ 3 * Mk ^ 6 * Rc ^ 2) * X ^ 3 + Iψ ^ 2 * X ^ 3 * ph ^ 3 * (8 * Mk ^ 4 * G) :=
          add_le_add (mul_le_mul_of_nonneg_left hX23 hc3) le_rfl
      _ = Iψ ^ 2 * X ^ 3 * ph ^ 3 * (9 * Mk ^ 6 * Rc ^ 2 + 8 * Mk ^ 4 * G) := by ring
  -- `S₃,₃ ≤ 4V`
  have hS33 : S33 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤ 4 * Vblk R χ t C ε T X K k :=
    (S33_le_S34 R χ t hL.le fun m hm => swap_mem_blk hm).trans (by linarith)
  refine ⟨hS34, hS33, ?_⟩
  -- the block sum
  set V := Vblk R χ t C ε T X K k with hV
  have hS34_0 : 0 ≤ S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) :=
    setIntegral_nonneg measurableSet_Icc fun v _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hV0 : 0 ≤ V := hS34_0.trans hS34
  have hS31 : S31 R χ t = 3 / 2 * (ph * Rc) := lemma91 R hinj t
  have h32 := S32_le R χ t (X := X) (M₂ := 2 ^ k) (blk M k) hL.le
  have hsq33 : Real.sqrt (S33 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)) ≤ 2 * Real.sqrt V := by
    calc Real.sqrt (S33 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)) ≤ Real.sqrt (4 * V) :=
          Real.sqrt_le_sqrt hS33
      _ = 2 * Real.sqrt V := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsq34 : Real.sqrt (S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)) ≤ Real.sqrt V :=
    Real.sqrt_le_sqrt hS34
  have h32' : S32 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤ 2 * V := by
    calc S32 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)
        ≤ Real.sqrt (S33 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)) *
          Real.sqrt (S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N)) := h32
      _ ≤ 2 * Real.sqrt V * Real.sqrt V :=
          mul_le_mul hsq33 hsq34 (Real.sqrt_nonneg _) (by positivity)
      _ = 2 * V := by rw [mul_assoc, Real.mul_self_sqrt hV0]
  have h31 : 0 ≤ S31 R χ t (q := q) := by
    rw [hS31]
    exact mul_nonneg (by norm_num) (mul_nonneg hφ0 hRc0)
  calc (∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2) ^ 2
      ≤ S31 R χ t * S32 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) := sum_It_sq_le R χ t (blk M k) hL.le
    _ ≤ S31 R χ t * (2 * V) := mul_le_mul_of_nonneg_left h32' h31
    _ = 3 * ph * Rc * V := by rw [hS31]; ring

end LinnikCGLBlock

#print axioms LinnikCGLBlock.integral_sum_fb_le
#print axioms LinnikCGLBlock.integral_sum_fb_sq_le
#print axioms LinnikCGLBlock.S34_le_P81
#print axioms LinnikCGLBlock.block_le
