/-
# Round 691: their Lemma 8.2 in their form, with the parameters chosen (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li's Lemma 8.2 (lines 2495–2516) is `J(f⃗) ⪅ φ(q)M⁶(∫_ℝΣ_bf_b(u) du)² +
φ(q)(M⁴∫_ℝΣ_bf_b(u)² du)^{1/2}J(f̃⃗)^{1/2}` (transcribed), where "we write A ⪅ B to indicate that for any ϵ > 0, there
exists a constant C(ϵ) > 0, depending only on ϵ, such that A ≤ C(ϵ)(qT)^ϵ B for all sufficiently large qT." (lines
279–281; spaces restored, the exponent transcribed). Round 688 proved the lemma in explicit form, before any choice of
the parameters `L`, `X`, `N₀`, `δ`, `j` and `K`. This file chooses them and bounds every constant, and their negligible
errors, by `C(qT)^θ`, for every `θ > 0`.

The stack's form.
* The parameters, in powers of `R = (qT)^{1/m}` with `m ≥ 1` and `13/m ≤ θ`: `L = (|κ| + 1)M`, `X = (qT)³`,
  `N₀ = R^{m+4}/M₂`, `δ = 1/m`, `j = 2m + 11` and `K = 2m + 8`. Their split in `ξ` is at `(qT)²` (lines 2781–2796).
  Their footnote 7: "One might choose ψ₂(x) = ψ₀(x/(qT)^η), where ψ₀(x) is a smooth bump supported on [−2,2] and
  identically equal to 1 for |x| ≤ 1." (lines 3517–3518; spaces restored, the subscripts and the exponent
  transcribed); round 684's `N₀` for that choice is `qT(qT)^η/M₂`, which is `R^{m+4}/M₂` at `η = 4/m`.
* The term `|n| ≤ N₀` carries `R^{13} = (qT)^{13/m} ≤ (qT)^θ`. The errors are at most constants times `F²`, and
  `F² ≤ 64φ(q)M⁶F²` for `M ≥ 1/2`, so they join the first term.
* The decay premise enters at `j = 2m + 11` with `max(D_j, 0)`. The bound `Λ ≤ G(qT)²F` is a hypothesis here.
* `M₁ < 1/2` or `M₂ < 1/2` gives `Jint = 0` (round 689's `Jint_eq_zero`); otherwise `M ≥ 1/2`.
* The constant `C` depends on `θ`, `κ`, `G` and `D` only. The bound holds for every `qT ≥ 1`, not only for large `qT`.
* Their `φ(q)` in the second term is `q` here. Their `J(f̃⃗)` is `J̃ = Jint(f̃, M₂, M₂, M₂, 4|A| + 2)`, as in round 688.

Plain statements, with `q ≥ 1` (`[NeZero q]`), `F = Σ_b∫f_b`, `𝔖 = ∫Σ_bf_b²`, `J̃` as above, `I₀ = ∫|ψ̂₀(−τ)| dτ`,
`C_K` round 684's `CK`, `C_δ` round 525's `Cdiv`, `B₄` round 681's `B4`, `d(q)` the number of divisors of `q`,
`L = K₁M`, and `W₀`, `K_X`, `B_J`, `B_tail` and `G₁` round 688's `W0`, `KX`, `BJ`, `Btail` and `G1`.
* `term1_le`: for `f_b ≥ 0`, `1/2 ≤ M₁ ≤ M`, `1/2 ≤ M₂ ≤ M`, `K₁ ≥ 1` and `0 < δ ≤ 1`,
  `2φ(q)W₀²(2πM₁/L) ≤ 160000πB₄²K₁C_δ²q^{2δ}·φ(q)M⁶F²`.
* `term3_le`: for `T ≥ 1`, `1/2 ≤ M₁ ≤ M ≤ qT`, `1/2 ≤ M₂ ≤ M`, `K₁ ≥ 1`, `D, G ≥ 0`, `0 ≤ Λ ≤ G(qT)²F` and `j ≥ 10`, at
  `X = (qT)³`, `2πφ(q)G₁²X^{−(2j−2)} ≤ 128π(4000K₁DG·4^j)²·φ(q)M⁶F²`.
* `sum_P1_div_le`: for `M₁ ≥ 1/2`, `L > 0` and `S ≥ 0`, `Σ_{m₁∈P1 M₁}S/(|m₁|L) ≤ 10S/L`.
* `KX_le_Q`, `KX_nonneg`: for `T ≥ 1`, `L > 0`, `0 ≤ M₁ ≤ L` and `0 < δ ≤ 1`, at `X = (qT)³`,
  `K_X ≤ 240πC_δB₄d(q)⁴L²q(qT)^{5δ}`; and for `L > 0`, `M₁ ≥ 0` and `0 < δ ≤ 1`, `K_X ≥ 0`.
* `term2_split`: for `T ≥ 1`, `1/2 ≤ M₁ ≤ M`, `K₁ ≥ 1`, `0 < δ ≤ 1` and `S ≥ 0`, at `X = (qT)³`,
  `2K_XΣ_{m₁∈P1 M₁}S/(|m₁|L) ≤ 4800πC_δ⁵B₄Lq(qT)^{9δ}S`.
* `t2_main`, `t2_errA`, `t2_errB1`, `t2_errB2`: the four parts of `c₀LqR⁹(I₀B_J + B_tail)`, in real variables.
* `t2_fac`: for `R > 0`, `M₂ ≥ 1/2`, `qT = R^m` and `N₀M₂ = R^{m+4}`, `(2qT/M₂)^{n+2}N₀^{−n} ≤ 16·2ⁿR^{2m}R^{−4n}`.
* `term2_parts`: for `T ≥ 1`, `R ≥ 1` with `qT = R^m`, `1/2 ≤ M₂ ≤ M ≤ R^m`, `K₁ ≥ 1`, `c₀ ≥ 0`, `f_b ≥ 0`, `D ≥ 0`,
  `0 ≤ Λ ≤ GR^{2m}F`, `j ≥ 1`, `K ≥ 4`, `7m + 13 ≤ 4(K − 2)`, `12m + 9 ≤ 4(2j − 2)` and `8m + 9 ≤ 4(K − 4)`, at
  `N₀ = R^{m+4}/M₂`, `c₀LqR⁹(I₀B_J + B_tail) ≤ 4c₀I₀C_KK₁R^{13}·qM²√𝔖√J̃ +
  4800πc₀K₁(I₀C_K + 4^{j+1}I₀D²G² + 2^KπC_K)F²`.
* `rpow_inv_facts`: for `Q ≥ 1`, `m ≥ 1` and `R = Q^{1/m}`, `R ≥ 1`, `R^m = Q` and `Q^{k/m} = R^k` for natural `k`.
* `form_combine`, `form_t1`, `form_t2`, `form_main`: the final count in real variables, the terms at the chosen
  parameters, and their assembly.
* `lemma82_form`: for `θ > 0`, real `κ` and `G`, and `D : ℕ → ℝ`, there is `C ≥ 0` such that, for `T ≥ 1`, `M ≤ qT`,
  smooth `f_b ≥ 0` that are `0` for `|u| > A`, `0 ≤ Λ ≤ G(qT)²F`, the decay `Σ_b|f̂_b(ξ)| ≤ D_j(T/|ξ|)^jΛ` for every
  `j` and every `ξ ≠ 0`, `0 < M₁ ≤ M`, `0 < M₂ ≤ M` and `0 ≤ M₃ ≤ M`,
  `Jint(f, M₁, M₂, M₃, κ) ≤ C(qT)^θ(φ(q)M⁶F² + qM²√𝔖√J̃)`.

The file imports `LinnikCGLConst.lean`.
-/

import LinnikCGLConst

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLForm

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLSep LinnikCGLRFact LinnikCGLRam LinnikCGLJ LinnikCGLG
  LinnikCGLPois8 LinnikCGLCount LinnikCGLAsum LinnikCGLNsum LinnikCGLN0 LinnikCGLCov LinnikCGLSig2 LinnikCGLFtil
  LinnikCGLLoc LinnikCGLJtil LinnikCGLTail LinnikCGLL82 LinnikCGLConst

/-! ### The term `n = 0` -/

/-- For `q ≥ 1`, `f_b ≥ 0`, `1/2 ≤ M₁ ≤ M`, `1/2 ≤ M₂ ≤ M`, `K₁ ≥ 1` and `0 < δ ≤ 1`, with `L = K₁M`,
`2φ(q)W₀²(2πM₁/L) ≤ 160000πB₄²K₁C_δ²q^{2δ}·φ(q)M⁶F²`. -/
lemma term1_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) {M₁ M₂ M K₁ δ : ℝ}
    (hM₁ : 1 / 2 ≤ M₁) (hM₁M : M₁ ≤ M) (hM₂ : 1 / 2 ≤ M₂) (hM₂M : M₂ ≤ M) (hK₁ : 1 ≤ K₁) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    2 * ((q.totient : ℝ) * W0 f M₁ M₂ (K₁ * M) ^ 2 * (2 * π * M₁ / (K₁ * M))) ≤
      160000 * π * B4 ^ 2 * K₁ * LinnikPower.Cdiv δ ^ 2 * (q : ℝ) ^ (2 * δ) *
        ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hM : 0 < M := by linarith
  have hL : 0 < K₁ * M := by positivity
  have hF : 0 ≤ ∑ b, ∫ u, f b u := Finset.sum_nonneg fun b _ => integral_nonneg fun u => hf b u
  have hB := B4_nonneg
  have hG : 0 ≤ ∑ h : ZMod q, gw h := Finset.sum_nonneg fun h _ => gw_nonneg h
  have hφ : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  have hM₁0 : 0 < M₁ := by linarith
  have hW0 : 0 ≤ W0 f M₁ M₂ (K₁ * M) := by
    unfold W0
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hL.le hq.le)) hB) hG)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith) hM₁0.le)) hF)
  have hW := W0_le hf hM₁ hM₂ hL.le (q := q)
  have hd := LinnikPower.card_divisors_le hδ hδ1 q
  have hd0 : (0 : ℝ) ≤ q.divisors.card := Nat.cast_nonneg _
  have hW2 : W0 f M₁ M₂ (K₁ * M) ^ 2 ≤ (200 * B4 * (K₁ * M) * q.divisors.card * M₂ ^ 2 * ∑ b, ∫ u, f b u) ^ 2 :=
    pow_le_pow_left₀ hW0 hW 2
  have hd2 : (q.divisors.card : ℝ) ^ 2 ≤ LinnikPower.Cdiv δ ^ 2 * (q : ℝ) ^ (2 * δ) := by
    have h := pow_le_pow_left₀ hd0 hd 2
    rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ δ) 2, ← Real.rpow_mul hq.le] at h
    simpa [mul_comm] using h
  have hM₂4 : M₂ ^ 4 ≤ M ^ 4 := pow_le_pow_left₀ (by linarith) hM₂M 4
  calc 2 * ((q.totient : ℝ) * W0 f M₁ M₂ (K₁ * M) ^ 2 * (2 * π * M₁ / (K₁ * M)))
      ≤ 2 * ((q.totient : ℝ) * (200 * B4 * (K₁ * M) * q.divisors.card * M₂ ^ 2 * ∑ b, ∫ u, f b u) ^ 2 *
          (2 * π * M₁ / (K₁ * M))) := by gcongr
    _ = 160000 * π * B4 ^ 2 * K₁ * (q.divisors.card : ℝ) ^ 2 * (M ^ 6 * (M₂ ^ 4 / M ^ 4) * (M₁ / M)) *
          ((q.totient : ℝ) * (∑ b, ∫ u, f b u) ^ 2) := by
        field_simp
        ring
    _ ≤ 160000 * π * B4 ^ 2 * K₁ * (LinnikPower.Cdiv δ ^ 2 * (q : ℝ) ^ (2 * δ)) * (M ^ 6 * 1 * 1) *
          ((q.totient : ℝ) * (∑ b, ∫ u, f b u) ^ 2) := by
        gcongr
        · exact (div_le_one (by positivity)).2 hM₂4
        · exact (div_le_one hM).2 hM₁M
    _ = _ := by ring

/-! ### The range `|ξ| > X` -/

/-- For `q ≥ 1`, `T ≥ 1`, `1/2 ≤ M₁ ≤ M ≤ qT`, `1/2 ≤ M₂ ≤ M`, `K₁ ≥ 1`, `D, G ≥ 0`, `0 ≤ Λ ≤ G(qT)²F`, `j ≥ 10`
and `X = (qT)³`, with `L = K₁M`, `2πφ(q)G₁²X^{−(2j−2)} ≤ 128π(4000K₁DG·4^j)²·φ(q)M⁶F²`. -/
lemma term3_le {q : ℕ} [NeZero q] {T M M₁ M₂ K₁ D G Λ F : ℝ} {j : ℕ} (hT : 1 ≤ T) (hM₁ : 1 / 2 ≤ M₁)
    (hM₁M : M₁ ≤ M) (hMQ : M ≤ q * T) (hM₂ : 1 / 2 ≤ M₂) (hM₂M : M₂ ≤ M) (hK₁ : 1 ≤ K₁) (hD : 0 ≤ D)
    (hG : 0 ≤ G) (hΛ : 0 ≤ Λ) (hΛF : Λ ≤ G * ((q : ℝ) * T) ^ 2 * F) (hj : 10 ≤ j) :
    2 * π * q.totient * G1 q M₁ M₂ (K₁ * M) T D Λ j ^ 2 * ((((q : ℝ) * T) ^ 3) ^ (2 * j - 2))⁻¹ ≤
      128 * π * (4000 * K₁ * D * G * 4 ^ j) ^ 2 * ((q.totient : ℝ) * M ^ 6 * F ^ 2) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set Q : ℝ := q * T with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 < Q := by linarith
  have hM : 1 / 2 ≤ M := by linarith
  have hqQ : (q : ℝ) ≤ Q := by rw [hQ]; nlinarith
  have hTQ : T ≤ Q := by rw [hQ]; nlinarith
  have hM₁Q : M₁ ≤ Q := by linarith
  have hφ1 : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  -- the factors of `G₁`
  have h1 : ((P1 M₁).card : ℝ) ≤ 10 * Q := by linarith [card_P1_le (by linarith : (0 : ℝ) ≤ M₁)]
  have h2 : ((P2 M₂).card : ℝ) ≤ 10 * Q := by linarith [card_P2_le (by linarith : (0 : ℝ) ≤ M₂)]
  have h30 : 0 ≤ 2 * M₂ / M₁ := div_nonneg (by linarith) (by linarith)
  have h3 : 2 * M₂ / M₁ ≤ 4 * Q := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h4 : (q : ℝ) * (P3 (K₁ * M)).card ≤ Q * (10 * K₁ * Q) := by
    have h := card_P3_le (L := K₁ * M) (by nlinarith)
    have hKM : 4 * (K₁ * M) + 3 ≤ 10 * (K₁ * Q) := by nlinarith
    calc (q : ℝ) * (P3 (K₁ * M)).card ≤ Q * (10 * (K₁ * Q)) :=
          mul_le_mul hqQ (h.trans hKM) (Nat.cast_nonneg _) hQ0.le
      _ = Q * (10 * K₁ * Q) := by ring
  have h50 : 0 ≤ 2 * M₁ * T / M₂ := div_nonneg (by nlinarith) (by linarith)
  have h5 : (2 * M₁ * T / M₂) ^ j ≤ 4 ^ j * Q ^ (2 * j) := by
    have hb : 2 * M₁ * T / M₂ ≤ 4 * Q ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have : M₁ * T ≤ Q * Q := mul_le_mul hM₁Q hTQ (by linarith) hQ0.le
      nlinarith
    calc (2 * M₁ * T / M₂) ^ j ≤ (4 * Q ^ 2) ^ j := pow_le_pow_left₀ h50 hb j
      _ = 4 ^ j * Q ^ (2 * j) := by rw [mul_pow, ← pow_mul]
  have hG1 : G1 q M₁ M₂ (K₁ * M) T D Λ j ≤ 4000 * K₁ * D * G * 4 ^ j * Q ^ (7 + 2 * j) * F := by
    unfold G1
    calc ((P1 M₁).card : ℝ) * (P2 M₂).card * (2 * M₂ / M₁) * (q * (P3 (K₁ * M)).card) *
          (D * (2 * M₁ * T / M₂) ^ j * Λ)
        ≤ (10 * Q) * (10 * Q) * (4 * Q) * (Q * (10 * K₁ * Q)) * (D * (4 ^ j * Q ^ (2 * j)) * (G * Q ^ 2 * F)) := by
          gcongr
      _ = 4000 * K₁ * D * G * 4 ^ j * Q ^ (7 + 2 * j) * F := by ring
  have hG10 : 0 ≤ G1 q M₁ M₂ (K₁ * M) T D Λ j := by
    unfold G1
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) h30)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) (mul_nonneg (mul_nonneg hD (pow_nonneg h50 _)) hΛ)
  set B : ℝ := 4000 * K₁ * D * G * 4 ^ j with hB
  have hB0 : 0 ≤ B := by positivity
  have hpow : Q ^ (14 + 4 * j) ≤ (Q ^ 3) ^ (2 * j - 2) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hQ1 (by omega)
  have hX0 : 0 < (Q ^ 3) ^ (2 * j - 2) := by positivity
  have hsq : G1 q M₁ M₂ (K₁ * M) T D Λ j ^ 2 * ((Q ^ 3) ^ (2 * j - 2))⁻¹ ≤ B ^ 2 * F ^ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hX0]
    calc G1 q M₁ M₂ (K₁ * M) T D Λ j ^ 2 ≤ (B * Q ^ (7 + 2 * j) * F) ^ 2 := pow_le_pow_left₀ hG10 hG1 2
      _ = B ^ 2 * F ^ 2 * Q ^ (14 + 4 * j) := by ring
      _ ≤ B ^ 2 * F ^ 2 * (Q ^ 3) ^ (2 * j - 2) := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hM6 : 1 ≤ 64 * M ^ 6 := by
    have : (1 / 2 : ℝ) ^ 6 ≤ M ^ 6 := pow_le_pow_left₀ (by norm_num) hM 6
    norm_num at this ⊢
    linarith
  calc 2 * π * q.totient * G1 q M₁ M₂ (K₁ * M) T D Λ j ^ 2 * ((Q ^ 3) ^ (2 * j - 2))⁻¹
      = 2 * π * q.totient * (G1 q M₁ M₂ (K₁ * M) T D Λ j ^ 2 * ((Q ^ 3) ^ (2 * j - 2))⁻¹) := by ring
    _ ≤ 2 * π * q.totient * (B ^ 2 * F ^ 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ ≤ 2 * π * q.totient * (B ^ 2 * F ^ 2) * (64 * M ^ 6) :=
        le_mul_of_one_le_right (by positivity) hM6
    _ = 128 * π * B ^ 2 * ((q.totient : ℝ) * M ^ 6 * F ^ 2) := by ring

/-! ### The sum over `m₁` and `K_X` at `X = (qT)³` -/

/-- For `M₁ ≥ 1/2`, `L > 0` and `S ≥ 0`, `Σ_{m₁∈P1 M₁}S/(|m₁|L) ≤ 10S/L`. -/
lemma sum_P1_div_le {M₁ L S : ℝ} (hM₁ : 1 / 2 ≤ M₁) (hL : 0 < L) (hS : 0 ≤ S) :
    ∑ m₁ ∈ P1 M₁, S / (|(m₁ : ℝ)| * L) ≤ 10 * S / L := by
  have hc : ((P1 M₁).card : ℝ) ≤ 10 * M₁ := by linarith [card_P1_le (by linarith : (0 : ℝ) ≤ M₁)]
  have hM₁0 : 0 < M₁ := by linarith
  calc ∑ m₁ ∈ P1 M₁, S / (|(m₁ : ℝ)| * L) ≤ ∑ _m₁ ∈ P1 M₁, S / (M₁ * L) :=
        Finset.sum_le_sum fun m₁ hm₁ => div_le_div_of_nonneg_left hS (by positivity)
          (mul_le_mul_of_nonneg_right ((mem_P1 m₁).1 hm₁).1.le hL.le)
    _ = (P1 M₁).card * (S / (M₁ * L)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 10 * M₁ * (S / (M₁ * L)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 10 * S / L := by field_simp

/-- For `q ≥ 1`, `T ≥ 1`, `L > 0`, `0 ≤ M₁ ≤ L` and `0 < δ ≤ 1`, at `X = (qT)³`,
`K_X ≤ 240πC_δB₄d(q)⁴L²q(qT)^{5δ}`. -/
lemma KX_le_Q {q : ℕ} [NeZero q] {T L M₁ δ : ℝ} (hT : 1 ≤ T) (hL : 0 < L) (hM₁ : 0 ≤ M₁) (hM₁L : M₁ ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    KX q L M₁ (((q : ℝ) * T) ^ 3) δ ≤ 240 * π * LinnikPower.Cdiv δ * B4 * (q.divisors.card : ℝ) ^ 4 * L ^ 2 * q *
      ((q : ℝ) * T) ^ (5 * δ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set Q : ℝ := q * T with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 < Q := by linarith
  have hqQ : (q : ℝ) ≤ Q := by rw [hQ]; nlinarith
  have hB := B4_nonneg
  have hC : 0 ≤ LinnikPower.Cdiv δ := le_trans zero_le_one (LinnikPower.one_le_Cdiv hδ hδ1)
  have h := KX_le (q := q) hL hM₁ hM₁L (X := Q ^ 3) (by positivity) hδ hδ1
  have ha : (1 + q * Q ^ 3) ^ δ ≤ 2 * Q ^ (4 * δ) := by
    have h1 : 1 + q * Q ^ 3 ≤ 2 * Q ^ 4 := by
      have : (q : ℝ) * Q ^ 3 ≤ Q ^ 4 := by
        calc (q : ℝ) * Q ^ 3 ≤ Q * Q ^ 3 := mul_le_mul_of_nonneg_right hqQ (by positivity)
          _ = Q ^ 4 := by ring
      have : 1 ≤ Q ^ 4 := one_le_pow₀ hQ1
      linarith
    calc (1 + q * Q ^ 3) ^ δ ≤ (2 * Q ^ 4) ^ δ := Real.rpow_le_rpow (by positivity) h1 hδ.le
      _ = 2 ^ δ * Q ^ (4 * δ) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast Q 4, ← Real.rpow_mul hQ0.le]
          norm_num
      _ ≤ 2 * Q ^ (4 * δ) := by
          gcongr
          calc (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
            _ = 2 := Real.rpow_one 2
  have hb : (1 + 2 * (q : ℝ)) ^ δ ≤ 3 * Q ^ δ := by
    have h1 : 1 + 2 * (q : ℝ) ≤ 3 * Q := by linarith
    calc (1 + 2 * (q : ℝ)) ^ δ ≤ (3 * Q) ^ δ := Real.rpow_le_rpow (by positivity) h1 hδ.le
      _ = 3 ^ δ * Q ^ δ := Real.mul_rpow (by norm_num) hQ0.le
      _ ≤ 3 * Q ^ δ := by
          gcongr
          calc (3 : ℝ) ^ δ ≤ 3 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
            _ = 3 := Real.rpow_one 3
  have hQ5 : Q ^ (4 * δ) * Q ^ δ = Q ^ (5 * δ) := by
    rw [← Real.rpow_add hQ0]; ring_nf
  calc KX q L M₁ (Q ^ 3) δ ≤ 40 * π * LinnikPower.Cdiv δ * B4 * (q.divisors.card : ℝ) ^ 4 * L ^ 2 * q *
        (1 + q * Q ^ 3) ^ δ * (1 + 2 * q) ^ δ := h
    _ ≤ 40 * π * LinnikPower.Cdiv δ * B4 * (q.divisors.card : ℝ) ^ 4 * L ^ 2 * q *
        (2 * Q ^ (4 * δ)) * (3 * Q ^ δ) := by gcongr
    _ = 240 * π * LinnikPower.Cdiv δ * B4 * (q.divisors.card : ℝ) ^ 4 * L ^ 2 * q * (Q ^ (4 * δ) * Q ^ δ) := by
        ring
    _ = _ := by rw [hQ5]

/-- For `q ≥ 1`, `L > 0`, `M₁ ≥ 0` and `0 < δ ≤ 1`, round 688's `K_X ≥ 0`. -/
lemma KX_nonneg {q : ℕ} [NeZero q] {L M₁ X δ : ℝ} (hL : 0 < L) (hM₁ : 0 ≤ M₁) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ KX q L M₁ X δ := by
  have hB := B4_nonneg
  have hC : 0 ≤ LinnikPower.Cdiv δ := le_trans zero_le_one (LinnikPower.one_le_Cdiv hδ hδ1)
  have hG : 0 ≤ ∑ h : ZMod q, gw h := Finset.sum_nonneg fun h _ => gw_nonneg h
  have h1 : 0 ≤ (1 + (q : ℝ) * |X|) ^ δ := Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ (1 + 2 * (q : ℝ) * M₁ / L) ^ δ := Real.rpow_nonneg (by positivity) _
  unfold KX
  have h3 : 0 ≤ 2 * π + 8 * π * M₁ / L := by positivity
  have h4 : 0 ≤ 4 * LinnikPower.Cdiv δ * B4 * (1 + (q : ℝ) * |X|) ^ δ * (1 + 2 * q * M₁ / L) ^ δ *
      (∑ h : ZMod q, gw h) * (2 * π + 8 * π * M₁ / L) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC) hB)
      h1) h2) hG) h3
    simpa [mul_assoc] using this
  exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (sq_nonneg _)) h4

/-! ### The terms `n ≠ 0` -/

/-- **Their `II`, split**: for `q ≥ 1`, `T ≥ 1`, `1/2 ≤ M₁ ≤ M`, `K₁ ≥ 1`, `0 < δ ≤ 1` and `S ≥ 0`, with `L = K₁M` and
`X = (qT)³`, `2K_XΣ_{m₁∈P1 M₁}S/(|m₁|L) ≤ 4800πC_δ⁵B₄Lq(qT)^{9δ}S`. -/
lemma term2_split {q : ℕ} [NeZero q] {T M M₁ K₁ δ S : ℝ} (hT : 1 ≤ T) (hM₁ : 1 / 2 ≤ M₁) (hM₁M : M₁ ≤ M)
    (hK₁ : 1 ≤ K₁) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hS : 0 ≤ S) :
    2 * (KX q (K₁ * M) M₁ (((q : ℝ) * T) ^ 3) δ * ∑ m₁ ∈ P1 M₁, S / (|(m₁ : ℝ)| * (K₁ * M))) ≤
      4800 * π * LinnikPower.Cdiv δ ^ 5 * B4 * (K₁ * M) * q * ((q : ℝ) * T) ^ (9 * δ) * S := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set Q : ℝ := q * T with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 < Q := by linarith
  have hqQ : (q : ℝ) ≤ Q := by rw [hQ]; nlinarith
  have hM : 0 < M := by linarith
  have hL : 0 < K₁ * M := by positivity
  have hM₁L : M₁ ≤ K₁ * M := by nlinarith
  have hB := B4_nonneg
  have hC : 0 ≤ LinnikPower.Cdiv δ := le_trans zero_le_one (LinnikPower.one_le_Cdiv hδ hδ1)
  have hKX := KX_le_Q (q := q) hT hL (by linarith) hM₁L hδ hδ1
  have hKX0 := KX_nonneg (q := q) (M₁ := M₁) (X := Q ^ 3) hL (by linarith) hδ hδ1
  have hsum := sum_P1_div_le hM₁ hL hS
  have hd := LinnikPower.card_divisors_le hδ hδ1 q
  have hd4 : (q.divisors.card : ℝ) ^ 4 ≤ LinnikPower.Cdiv δ ^ 4 * Q ^ (4 * δ) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg _) hd 4
    have hq4 : ((q : ℝ) ^ δ) ^ 4 ≤ Q ^ (4 * δ) := by
      rw [← Real.rpow_natCast ((q : ℝ) ^ δ) 4, ← Real.rpow_mul (Nat.cast_nonneg _)]
      have e : δ * ((4 : ℕ) : ℝ) = 4 * δ := by push_cast; ring
      rw [e]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) hqQ (by positivity)
    calc (q.divisors.card : ℝ) ^ 4 ≤ (LinnikPower.Cdiv δ * (q : ℝ) ^ δ) ^ 4 := h
      _ = LinnikPower.Cdiv δ ^ 4 * ((q : ℝ) ^ δ) ^ 4 := mul_pow _ _ _
      _ ≤ LinnikPower.Cdiv δ ^ 4 * Q ^ (4 * δ) := mul_le_mul_of_nonneg_left hq4 (by positivity)
  have hQ9 : Q ^ (4 * δ) * Q ^ (5 * δ) = Q ^ (9 * δ) := by rw [← Real.rpow_add hQ0]; ring_nf
  calc 2 * (KX q (K₁ * M) M₁ (Q ^ 3) δ * ∑ m₁ ∈ P1 M₁, S / (|(m₁ : ℝ)| * (K₁ * M)))
      ≤ 2 * ((240 * π * LinnikPower.Cdiv δ * B4 * (q.divisors.card : ℝ) ^ 4 * (K₁ * M) ^ 2 * q * Q ^ (5 * δ)) *
          (10 * S / (K₁ * M))) := by
        gcongr
    _ ≤ 2 * ((240 * π * LinnikPower.Cdiv δ * B4 * (LinnikPower.Cdiv δ ^ 4 * Q ^ (4 * δ)) * (K₁ * M) ^ 2 * q *
          Q ^ (5 * δ)) * (10 * S / (K₁ * M))) := by
        gcongr
    _ = 4800 * π * LinnikPower.Cdiv δ ^ 5 * B4 * (K₁ * M) * q * (Q ^ (4 * δ) * Q ^ (5 * δ)) * S := by
        field_simp
        ring
    _ = _ := by rw [hQ9]

/-! ### The term `n ≠ 0`, its four parts -/

/-- For `qT = R^m`, `N₀M₂ = R^{m+4}`, `q, T, M₂ > 0`, `M₂ ≤ M` and `R, c₀, K₁, I₀, C, s, t ≥ 0`,
`c₀(K₁M)qR⁹·I₀N₀C(4M₂²/(qT))st ≤ 4c₀I₀CK₁R^{13}·qM²st`. -/
lemma t2_main {c₀ K₁ M q T R I₀ C N₀ M₂ s t : ℝ} {m : ℕ} (hQ : q * T = R ^ m) (hN : N₀ * M₂ = R ^ (m + 4))
    (hq : 0 < q) (hT : 0 < T) (hM₂ : 0 < M₂) (hM₂M : M₂ ≤ M) (hR : 0 ≤ R) (hc₀ : 0 ≤ c₀) (hK₁ : 0 ≤ K₁)
    (hI : 0 ≤ I₀) (hC : 0 ≤ C) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    c₀ * (K₁ * M) * q * R ^ 9 * (I₀ * (N₀ * C * (4 * M₂ ^ 2 / (q * T) * s * t))) ≤
      4 * c₀ * I₀ * C * K₁ * R ^ 13 * (q * M ^ 2 * s * t) := by
  have hRm : R ^ m ≠ 0 := by rw [← hQ]; exact (mul_pos hq hT).ne'
  have e : N₀ * (4 * M₂ ^ 2 / (q * T)) = 4 * M₂ * R ^ 4 := by
    rw [show N₀ * (4 * M₂ ^ 2 / (q * T)) = 4 * M₂ * (N₀ * M₂) / (q * T) by ring, hN, hQ, pow_add,
      div_eq_iff hRm]
    ring
  have hMM : M₂ * M ≤ M ^ 2 := by nlinarith
  calc c₀ * (K₁ * M) * q * R ^ 9 * (I₀ * (N₀ * C * (4 * M₂ ^ 2 / (q * T) * s * t)))
      = c₀ * K₁ * q * R ^ 9 * I₀ * C * s * t * M * (N₀ * (4 * M₂ ^ 2 / (q * T))) := by ring
    _ = 4 * c₀ * I₀ * C * K₁ * R ^ 13 * (q * (M₂ * M) * s * t) := by rw [e]; ring
    _ ≤ 4 * c₀ * I₀ * C * K₁ * R ^ 13 * (q * M ^ 2 * s * t) := by gcongr

/-- For `R ≥ 1`, `0 ≤ q ≤ R^m`, `M ≤ R^m`, `c₀, K₁, I₀, C ≥ 0`, `0 ≤ N₀ ≤ 2R^{m+4}`,
`0 ≤ E ≤ 6πR^{−4(K−2)}`, `0 ≤ P ≤ 20R^{2m}` and `7m + 13 ≤ 4(K − 2)`,
`c₀(K₁M)qR⁹·I₀N₀C·EP²F² ≤ 4800πc₀K₁·I₀C·F²`. -/
lemma t2_errA {c₀ K₁ M q R I₀ C N₀ E P F : ℝ} {m K : ℕ} (hR : 1 ≤ R) (hq : 0 ≤ q) (hqR : q ≤ R ^ m)
    (hMR : M ≤ R ^ m) (hc₀ : 0 ≤ c₀) (hK₁ : 0 ≤ K₁) (hI : 0 ≤ I₀) (hC : 0 ≤ C) (hN0 : 0 ≤ N₀)
    (hN : N₀ ≤ 2 * R ^ (m + 4)) (hE0 : 0 ≤ E) (hE : E ≤ 6 * π * (R ^ (4 * (K - 2)))⁻¹) (hP0 : 0 ≤ P)
    (hP : P ≤ 20 * R ^ (2 * m)) (hKa : 7 * m + 13 ≤ 4 * (K - 2)) :
    c₀ * (K₁ * M) * q * R ^ 9 * (I₀ * (N₀ * C * (E * P ^ 2 * F ^ 2))) ≤
      4800 * π * c₀ * K₁ * (I₀ * C) * F ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hpow : R ^ (7 * m + 13) * (R ^ (4 * (K - 2)))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    exact pow_le_pow_right₀ hR hKa
  calc c₀ * (K₁ * M) * q * R ^ 9 * (I₀ * (N₀ * C * (E * P ^ 2 * F ^ 2)))
      ≤ c₀ * (K₁ * R ^ m) * R ^ m * R ^ 9 * (I₀ * (2 * R ^ (m + 4) * C *
          (6 * π * (R ^ (4 * (K - 2)))⁻¹ * (20 * R ^ (2 * m)) ^ 2 * F ^ 2))) := by gcongr
    _ = 4800 * π * c₀ * K₁ * (I₀ * C) * (R ^ (7 * m + 13) * (R ^ (4 * (K - 2)))⁻¹) * F ^ 2 := by ring
    _ ≤ 4800 * π * c₀ * K₁ * (I₀ * C) * 1 * F ^ 2 := by gcongr
    _ = 4800 * π * c₀ * K₁ * (I₀ * C) * F ^ 2 := by ring

/-- For `R > 0`, `M₂ ≥ 1/2`, `qT = R^m` and `N₀M₂ = R^{m+4}`, `(2qT/M₂)^{n+2}N₀^{−n} ≤ 16·2ⁿR^{2m}R^{−4n}`. -/
lemma t2_fac {q T R M₂ N₀ : ℝ} {m n : ℕ} (hR : 0 < R) (hM₂ : 1 / 2 ≤ M₂) (hQ : q * T = R ^ m)
    (hN : N₀ * M₂ = R ^ (m + 4)) :
    (2 * q * T / M₂) ^ (n + 2) * (N₀ ^ n)⁻¹ ≤ 16 * 2 ^ n * R ^ (2 * m) * (R ^ (4 * n))⁻¹ := by
  have hM₂0 : 0 < M₂ := by linarith
  have hN' : N₀ = R ^ (m + 4) / M₂ := by rw [eq_div_iff hM₂0.ne']; exact hN
  have hNx : N₀ = 2 * q * T / M₂ * (R ^ 4 / 2) := by rw [hN', pow_add R m 4, ← hQ]; ring
  have hx : 2 * q * T / M₂ = 2 * R ^ m / M₂ := by rw [mul_assoc, hQ]
  rw [hNx, hx]
  have hy : 2 * R ^ m / M₂ ≠ 0 := by positivity
  have e : (2 * R ^ m / M₂) ^ (n + 2) * ((2 * R ^ m / M₂ * (R ^ 4 / 2)) ^ n)⁻¹ =
      (2 * R ^ m / M₂) ^ 2 * (2 ^ n * (R ^ (4 * n))⁻¹) := by
    set y : ℝ := 2 * R ^ m / M₂ with hy'
    have h2 : ((R ^ 4 / 2) ^ n)⁻¹ = 2 ^ n * (R ^ (4 * n))⁻¹ := by
      rw [div_pow, inv_div, pow_mul, div_eq_mul_inv]
    rw [mul_pow y, mul_inv, h2, pow_add]
    calc y ^ n * y ^ 2 * ((y ^ n)⁻¹ * (2 ^ n * (R ^ (4 * n))⁻¹))
        = (y ^ n * (y ^ n)⁻¹) * (y ^ 2 * (2 ^ n * (R ^ (4 * n))⁻¹)) := by ring
      _ = y ^ 2 * (2 ^ n * (R ^ (4 * n))⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero n hy), one_mul]
  have hM : (M₂ ^ 2)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  rw [e]
  calc (2 * R ^ m / M₂) ^ 2 * (2 ^ n * (R ^ (4 * n))⁻¹)
      = 4 * 2 ^ n * R ^ (2 * m) * (M₂ ^ 2)⁻¹ * (R ^ (4 * n))⁻¹ := by ring
    _ ≤ 4 * 2 ^ n * R ^ (2 * m) * 4 * (R ^ (4 * n))⁻¹ := by gcongr
    _ = 16 * 2 ^ n * R ^ (2 * m) * (R ^ (4 * n))⁻¹ := by ring

/-- For `R ≥ 1`, `0 ≤ q ≤ R^m`, `T ≥ 0`, `M ≤ R^m`, `qT = R^m`, `M₂ ≥ 1/2`, `N₀M₂ = R^{m+4}`,
`c₀, K₁, I₀, D ≥ 0`, `0 ≤ P ≤ 20R^{2m}`, `0 ≤ Λ ≤ GR^{2m}F`, `j ≥ 1` and `12m + 9 ≤ 4(2j − 2)`,
`c₀(K₁M)qR⁹·12πI₀(PDΛ)²(2qT/M₂)^{2j}N₀^{−(2j−2)} ≤ 4800πc₀K₁·4^{j+1}I₀D²G²·F²`. -/
lemma t2_errB1 {c₀ K₁ M q T R I₀ N₀ M₂ P D G Λ F : ℝ} {m j : ℕ} (hR : 1 ≤ R) (hq : 0 ≤ q) (hqR : q ≤ R ^ m)
    (hT : 0 ≤ T) (hMR : M ≤ R ^ m) (hQ : q * T = R ^ m) (hM₂ : 1 / 2 ≤ M₂)
    (hN : N₀ * M₂ = R ^ (m + 4)) (hc₀ : 0 ≤ c₀) (hK₁ : 0 ≤ K₁) (hI : 0 ≤ I₀) (hP0 : 0 ≤ P)
    (hP : P ≤ 20 * R ^ (2 * m)) (hD : 0 ≤ D) (hΛ : 0 ≤ Λ) (hΛF : Λ ≤ G * R ^ (2 * m) * F)
    (hj : 1 ≤ j) (hjb : 12 * m + 9 ≤ 4 * (2 * j - 2)) :
    c₀ * (K₁ * M) * q * R ^ 9 * (12 * π * (I₀ * (P * D * Λ) ^ 2 * (2 * q * T / M₂) ^ (2 * j) *
        (N₀ ^ (2 * j - 2))⁻¹)) ≤ 4800 * π * c₀ * K₁ * (4 ^ (j + 1) * I₀ * D ^ 2 * G ^ 2) * F ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  have hN0 : 0 < N₀ := by nlinarith [pow_pos hR0 (m + 4)]
  obtain ⟨n, hn⟩ : ∃ n, 2 * j - 2 = n := ⟨_, rfl⟩
  have hn2 : 2 * j = n + 2 := by omega
  rw [hn] at hjb ⊢
  rw [hn2]
  have hfac := t2_fac (n := n) hR0 hM₂ hQ hN
  have h16 : (16 : ℝ) * 2 ^ n = 4 ^ (j + 1) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, show 2 * (j + 1) = n + 4 by omega, pow_add]; ring
  rw [h16] at hfac
  have hX0 : 0 ≤ (2 * q * T / M₂) ^ (n + 2) * (N₀ ^ n)⁻¹ := by positivity
  have hpow : R ^ (12 * m + 9) * (R ^ (4 * n))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    exact pow_le_pow_right₀ hR hjb
  generalize hX : (2 * q * T / M₂) ^ (n + 2) * (N₀ ^ n)⁻¹ = X at hfac hX0
  calc c₀ * (K₁ * M) * q * R ^ 9 * (12 * π * (I₀ * (P * D * Λ) ^ 2 * (2 * q * T / M₂) ^ (n + 2) * (N₀ ^ n)⁻¹))
      = c₀ * (K₁ * M) * q * R ^ 9 * (12 * π) * I₀ * (P * D * Λ) ^ 2 * X := by rw [← hX]; ring
    _ ≤ c₀ * (K₁ * R ^ m) * R ^ m * R ^ 9 * (12 * π) * I₀ * (20 * R ^ (2 * m) * D * (G * R ^ (2 * m) * F)) ^ 2 *
          (4 ^ (j + 1) * R ^ (2 * m) * (R ^ (4 * n))⁻¹) := by gcongr
    _ = 4800 * π * c₀ * K₁ * (4 ^ (j + 1) * I₀ * D ^ 2 * G ^ 2) * (R ^ (12 * m + 9) * (R ^ (4 * n))⁻¹) * F ^ 2 := by
        ring
    _ ≤ 4800 * π * c₀ * K₁ * (4 ^ (j + 1) * I₀ * D ^ 2 * G ^ 2) * 1 * F ^ 2 := by gcongr
    _ = 4800 * π * c₀ * K₁ * (4 ^ (j + 1) * I₀ * D ^ 2 * G ^ 2) * F ^ 2 := by ring

/-- For `R ≥ 1`, `T ≥ 1`, `0 ≤ q ≤ R^m`, `M ≤ R^m`, `qT = R^m`, `1/2 ≤ M₂ ≤ K₁M`, `N₀M₂ = R^{m+4}`,
`c₀, K₁, C, F ≥ 0`, `0 ≤ P ≤ 20R^{2m}`, `K ≥ 4` and `8m + 9 ≤ 4(K − 4)`,
`c₀(K₁M)qR⁹·12π·πC(PF)²(2q/(K₁M))^{K−2}N₀^{−(K−4)} ≤ 4800πc₀K₁·2^KπC·F²`. -/
lemma t2_errB2 {c₀ K₁ M q T R C N₀ M₂ P F : ℝ} {m K : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hq : 0 ≤ q)
    (hqR : q ≤ R ^ m) (hMR : M ≤ R ^ m) (hQ : q * T = R ^ m) (hM₂ : 1 / 2 ≤ M₂) (hM₂L : M₂ ≤ K₁ * M)
    (hN : N₀ * M₂ = R ^ (m + 4)) (hc₀ : 0 ≤ c₀) (hK₁ : 0 ≤ K₁) (hC : 0 ≤ C) (hP0 : 0 ≤ P)
    (hP : P ≤ 20 * R ^ (2 * m)) (hF : 0 ≤ F) (hK : 4 ≤ K) (hKb : 8 * m + 9 ≤ 4 * (K - 4)) :
    c₀ * (K₁ * M) * q * R ^ 9 * (12 * π * (π * C * (P * F) ^ 2 * (2 * q / (K₁ * M)) ^ (K - 2) *
        (N₀ ^ (K - 4))⁻¹)) ≤ 4800 * π * c₀ * K₁ * (2 ^ K * π * C) * F ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  have hL : 0 < K₁ * M := by linarith
  have hN0 : 0 < N₀ := by nlinarith [pow_pos hR0 (m + 4)]
  obtain ⟨n, hn⟩ : ∃ n, K - 4 = n := ⟨_, rfl⟩
  have hn2 : K - 2 = n + 2 := by omega
  rw [hn] at hKb ⊢
  rw [hn2]
  have hfac := t2_fac (n := n) hR0 hM₂ hQ hN
  have h16 : (16 : ℝ) * 2 ^ n = 2 ^ K := by
    rw [show K = n + 4 by omega, pow_add]; ring
  rw [h16] at hfac
  have hb : 2 * q / (K₁ * M) ≤ 2 * q * T / M₂ := by
    calc 2 * q / (K₁ * M) ≤ 2 * q / M₂ := by gcongr
      _ ≤ 2 * q * T / M₂ := by
          gcongr ?_ / M₂
          exact le_mul_of_one_le_right (by positivity) hT
  have hY : (2 * q / (K₁ * M)) ^ (n + 2) * (N₀ ^ n)⁻¹ ≤ 2 ^ K * R ^ (2 * m) * (R ^ (4 * n))⁻¹ :=
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hb _) (by positivity)) hfac
  have hY0 : 0 ≤ (2 * q / (K₁ * M)) ^ (n + 2) * (N₀ ^ n)⁻¹ := by positivity
  have hpow : R ^ (8 * m + 9) * (R ^ (4 * n))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    exact pow_le_pow_right₀ hR hKb
  generalize hX : (2 * q / (K₁ * M)) ^ (n + 2) * (N₀ ^ n)⁻¹ = X at hY hY0
  calc c₀ * (K₁ * M) * q * R ^ 9 * (12 * π * (π * C * (P * F) ^ 2 * (2 * q / (K₁ * M)) ^ (n + 2) * (N₀ ^ n)⁻¹))
      = c₀ * (K₁ * M) * q * R ^ 9 * (12 * π) * (π * C) * (P * F) ^ 2 * X := by rw [← hX]; ring
    _ ≤ c₀ * (K₁ * R ^ m) * R ^ m * R ^ 9 * (12 * π) * (π * C) * (20 * R ^ (2 * m) * F) ^ 2 *
          (2 ^ K * R ^ (2 * m) * (R ^ (4 * n))⁻¹) := by gcongr
    _ = 4800 * π * c₀ * K₁ * (2 ^ K * π * C) * (R ^ (8 * m + 9) * (R ^ (4 * n))⁻¹) * F ^ 2 := by ring
    _ ≤ 4800 * π * c₀ * K₁ * (2 ^ K * π * C) * 1 * F ^ 2 := by gcongr
    _ = 4800 * π * c₀ * K₁ * (2 ^ K * π * C) * F ^ 2 := by ring

/-- **Their `II`, the parts**: for `q ≥ 1`, `T ≥ 1`, `R ≥ 1` with `qT = R^m`, `1/2 ≤ M₂ ≤ M ≤ R^m`, `K₁ ≥ 1`, `c₀ ≥ 0`,
`f_b ≥ 0`, `D ≥ 0`, `0 ≤ Λ ≤ GR^{2m}F`, `j ≥ 1`, `K ≥ 4`, `7m + 13 ≤ 4(K − 2)`, `12m + 9 ≤ 4(2j − 2)` and
`8m + 9 ≤ 4(K − 4)`, with `L = K₁M` and `N₀ = R^{m+4}/M₂`,
`c₀LqR⁹(I₀B_J + B_tail) ≤ 4c₀I₀C_KK₁R^{13}·qM²√𝔖√J̃ + 4800πc₀K₁(I₀C_K + 4^{j+1}I₀D²G² + 2^KπC_K)F²`. -/
lemma term2_parts {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u)
    {A T M M₂ K₁ R c₀ D G Λ : ℝ} {m j K : ℕ} (hT : 1 ≤ T) (hR : 1 ≤ R) (hQ : (q : ℝ) * T = R ^ m)
    (hM₂ : 1 / 2 ≤ M₂) (hM₂M : M₂ ≤ M) (hMQ : M ≤ R ^ m) (hK₁ : 1 ≤ K₁) (hc₀ : 0 ≤ c₀) (hD : 0 ≤ D)
    (hΛ : 0 ≤ Λ) (hΛF : Λ ≤ G * R ^ (2 * m) * ∑ b, ∫ u, f b u) (hj : 1 ≤ j) (hK : 4 ≤ K)
    (hKa : 7 * m + 13 ≤ 4 * (K - 2)) (hjb : 12 * m + 9 ≤ 4 * (2 * j - 2)) (hKb : 8 * m + 9 ≤ 4 * (K - 4)) :
    c₀ * (K₁ * M) * q * R ^ 9 * ((∫ τ, ‖𝓕 psiC (-τ)‖) * BJ f A M₂ T (R ^ (m + 4) / M₂) K +
        Btail f M₂ (K₁ * M) (R ^ (m + 4) / M₂) T D Λ j K) ≤
      4 * c₀ * (∫ τ, ‖𝓕 psiC (-τ)‖) * CK K * K₁ * R ^ 13 *
          (q * M ^ 2 * √(∫ u, ∑ b, f b u ^ 2) * √(Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2))) +
        4800 * π * c₀ * K₁ * ((∫ τ, ‖𝓕 psiC (-τ)‖) * CK K + 4 ^ (j + 1) * (∫ τ, ‖𝓕 psiC (-τ)‖) * D ^ 2 * G ^ 2 +
          2 ^ K * π * CK K) * (∑ b, ∫ u, f b u) ^ 2 := by
  unfold BJ Btail
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hT0 : 0 < T := by linarith
  have hR0 : 0 < R := by linarith
  have hqR : (q : ℝ) ≤ R ^ m := by rw [← hQ]; exact le_mul_of_one_le_right hq.le hT
  have hM₂0 : 0 < M₂ := by linarith
  have hM : 0 < M := by linarith
  have hK₁0 : 0 ≤ K₁ := by linarith
  have hM₂L : M₂ ≤ K₁ * M := by nlinarith
  have hCK : 0 ≤ CK K := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (norm_fourier_psiC_le_CK K 0)
  set I₀ : ℝ := ∫ τ, ‖𝓕 psiC (-τ)‖ with hI₀
  have hI0 : 0 ≤ I₀ := integral_nonneg fun τ => norm_nonneg _
  set F : ℝ := ∑ b, ∫ u, f b u with hF
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun b _ => integral_nonneg fun u => hf b u
  set P : ℝ := ∑ m₂ ∈ P2 M₂, (m₂ : ℝ) with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun m₂ hm₂ => by have := (mem_P2 m₂).1 hm₂; linarith [this.1]
  have hPle : P ≤ 20 * R ^ (2 * m) := by
    have h := sum_P2_le (by linarith : (0 : ℝ) ≤ M₂)
    have h2 : M₂ ^ 2 ≤ (R ^ m) ^ 2 := pow_le_pow_left₀ (by linarith) (hM₂M.trans hMQ) 2
    rw [← pow_mul, mul_comm m 2] at h2
    nlinarith
  set sS : ℝ := √(∫ u, ∑ b, f b u ^ 2) with hsS
  set sJ : ℝ := √(Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2)) with hsJ
  have hsS0 : 0 ≤ sS := Real.sqrt_nonneg _
  have hsJ0 : 0 ≤ sJ := Real.sqrt_nonneg _
  set N₀ : ℝ := R ^ (m + 4) / M₂ with hN₀
  have hN₀M : N₀ * M₂ = R ^ (m + 4) := div_mul_cancel₀ _ hM₂0.ne'
  have hN₀0 : 0 < N₀ := by positivity
  have hN₀le : N₀ ≤ 2 * R ^ (m + 4) := by
    rw [hN₀, div_le_iff₀ hM₂0]; nlinarith [pow_pos hR0 (m + 4)]
  have hRm4 : R ^ (m + 4) = R ^ m * R ^ 4 := pow_add _ _ _
  -- `1 + N₀M₂/(qT) = 1 + R⁴`
  have hbase : 1 + N₀ * M₂ / (q * T) = 1 + R ^ 4 := by
    rw [hN₀M, hQ, hRm4, mul_div_cancel_left₀ _ (pow_ne_zero m hR0.ne')]
  set E : ℝ := ((1 + N₀ * M₂ / (q * T)) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) with hE
  have hE0 : 0 ≤ E := by
    rw [hE, hbase]; positivity
  have hEle : E ≤ 6 * π * (R ^ (4 * (K - 2)))⁻¹ := by
    rw [hE, hbase]
    have h1 : (R ^ (4 * (K - 2)))⁻¹ ≥ ((1 + R ^ 4) ^ (K - 2))⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have h2 : 2 * π + 4 * π / N₀ ≤ 6 * π := by
      have hN1 : 1 ≤ N₀ := by
        rw [hN₀, le_div_iff₀ hM₂0, one_mul, hRm4]
        nlinarith [one_le_pow₀ (n := 4) hR, one_le_pow₀ (n := m) hR]
      have : 4 * π / N₀ ≤ 4 * π := div_le_self (by positivity) hN1
      linarith
    calc ((1 + R ^ 4) ^ (K - 2))⁻¹ * (2 * π + 4 * π / N₀) ≤ (R ^ (4 * (K - 2)))⁻¹ * (6 * π) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 6 * π * (R ^ (4 * (K - 2)))⁻¹ := by ring
  clear_value I₀ F P sS sJ N₀ E
  have h1 := t2_main (c₀ := c₀) (C := CK K) hQ hN₀M hq hT0 hM₂0 hM₂M hR0.le hc₀ hK₁0 hI0 hCK hsS0 hsJ0
  have h2 := t2_errA (F := F) hR hq.le hqR hMQ hc₀ hK₁0 hI0 hCK hN₀0.le hN₀le hE0 hEle hP0 hPle hKa
  have h3 := t2_errB1 (c₀ := c₀) (K₁ := K₁) hR hq.le hqR hT0.le hMQ hQ hM₂ hN₀M hc₀ hK₁0 hI0 hP0 hPle hD hΛ
    hΛF hj hjb
  have h4 := t2_errB2 (c₀ := c₀) hR hT hq.le hqR hMQ hQ hM₂ hM₂L hN₀M hc₀ hK₁0 hCK hP0 hPle hF0 hK hKb
  refine Eq.trans_le ?_ ((add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq ?_) <;> ring

/-! ### The parameters, and their form -/

/-- For `Q ≥ 1`, `m ≥ 1` and `R = Q^{1/m}`: `R ≥ 1`, `R^m = Q`, and `Q^{k/m} = R^k` for every natural number `k`. -/
lemma rpow_inv_facts {Q R : ℝ} {m : ℕ} (hQ : 1 ≤ Q) (hm : 1 ≤ m) (hR : R = Q ^ (1 / (m : ℝ))) :
    1 ≤ R ∧ R ^ m = Q ∧ ∀ k : ℕ, Q ^ ((k : ℝ) * (1 / (m : ℝ))) = R ^ k := by
  have hQ0 : 0 ≤ Q := by linarith
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [hR]; exact Real.one_le_rpow hQ (by positivity)
  · rw [hR, ← Real.rpow_natCast, ← Real.rpow_mul hQ0, one_div, inv_mul_cancel₀ hm0, Real.rpow_one]
  · intro k
    rw [hR, ← Real.rpow_natCast, ← Real.rpow_mul hQ0, mul_comm]

/-- The final count: from `J ≤ t₁ + t₂ + t₃`, `t₁ ≤ c₁R²P`, `t₂ ≤ c₂R^{13}W + c₃F₂`, `t₃ ≤ c₄P`, `R ≥ 1`,
`R^{13} ≤ Q_θ`, `F₂ ≤ 64P` and `c₁, c₂, c₃, c₄, P, W ≥ 0`, `J ≤ (c₁ + c₄ + 64c₃ + c₂)Q_θ(P + W)`. -/
lemma form_combine {J t1 t2 t3 c1 c2 c3 c4 R Qθ P W F2 : ℝ} (hJ : J ≤ t1 + t2 + t3) (h1 : t1 ≤ c1 * R ^ 2 * P)
    (h2 : t2 ≤ c2 * R ^ 13 * W + c3 * F2) (h3 : t3 ≤ c4 * P) (hR : 1 ≤ R) (hRQ : R ^ 13 ≤ Qθ) (hF2 : F2 ≤ 64 * P)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4) (hP : 0 ≤ P) (hW : 0 ≤ W) :
    J ≤ (c1 + c4 + 64 * c3 + c2) * Qθ * (P + W) := by
  have hR2 : R ^ 2 ≤ Qθ := (pow_le_pow_right₀ hR (by norm_num : 2 ≤ 13)).trans hRQ
  have hQ1 : 1 ≤ Qθ := (one_le_pow₀ hR).trans hRQ
  have a1 : c1 * R ^ 2 * P ≤ c1 * Qθ * P := by gcongr
  have a2 : c2 * R ^ 13 * W ≤ c2 * Qθ * W := by gcongr
  have a3 : c3 * F2 ≤ 64 * c3 * Qθ * P :=
    calc c3 * F2 ≤ c3 * (64 * P) := mul_le_mul_of_nonneg_left hF2 hc3
      _ = 64 * c3 * 1 * P := by ring
      _ ≤ 64 * c3 * Qθ * P := by gcongr
  have a4 : c4 * P ≤ c4 * Qθ * P :=
    calc c4 * P = c4 * 1 * P := by ring
      _ ≤ c4 * Qθ * P := by gcongr
  have hx : 0 ≤ c2 * Qθ * P + (c1 + c4 + 64 * c3) * Qθ * W := by positivity
  have e : (c1 + c4 + 64 * c3 + c2) * Qθ * (P + W) =
      c1 * Qθ * P + c2 * Qθ * W + 64 * c3 * Qθ * P + c4 * Qθ * P + (c2 * Qθ * P + (c1 + c4 + 64 * c3) * Qθ * W) := by
    ring
  linarith

/-- The term `n = 0` at the chosen parameters: for `q ≥ 1`, `f_b ≥ 0`, `1/2 ≤ M₁ ≤ M`, `1/2 ≤ M₂ ≤ M`, `K₁ ≥ 1`,
`0 < δ ≤ 1`, `q^{2δ} ≤ R²` and `c₁ = 160000πB₄²K₁C_δ²`, `2φ(q)W₀²(2πM₁/(K₁M)) ≤ c₁R²·φ(q)M⁶F²`. -/
lemma form_t1 {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) {M₁ M₂ M K₁ δ R c1 : ℝ}
    (hM₁ : 1 / 2 ≤ M₁) (hM₁M : M₁ ≤ M) (hM₂ : 1 / 2 ≤ M₂) (hM₂M : M₂ ≤ M) (hK₁ : 1 ≤ K₁) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hq2 : (q : ℝ) ^ (2 * δ) ≤ R ^ 2) (hc1 : c1 = 160000 * π * B4 ^ 2 * K₁ * LinnikPower.Cdiv δ ^ 2) :
    2 * ((q.totient : ℝ) * W0 f M₁ M₂ (K₁ * M) ^ 2 * (2 * π * M₁ / (K₁ * M))) ≤
      c1 * R ^ 2 * ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2) := by
  have h1 := term1_le hf hM₁ hM₁M hM₂ hM₂M hK₁ hδ hδ1
  rw [← hc1] at h1
  have hB := B4_nonneg
  have hCd : 0 ≤ LinnikPower.Cdiv δ := le_trans zero_le_one (LinnikPower.one_le_Cdiv hδ hδ1)
  have hc : 0 ≤ c1 := by rw [hc1]; positivity
  exact h1.trans (by gcongr)

/-- The terms `n ≠ 0` at the chosen parameters: for `q ≥ 1`, `f_b ≥ 0`, `T ≥ 1`, `1/2 ≤ M₁ ≤ M`, `1/2 ≤ M₂ ≤ M`,
`K₁ ≥ 1`, `0 < δ ≤ 1`, `R ≥ 1` with `R^m = qT`, `(qT)^{9δ} = R⁹` and `M ≤ R^m`, `I₀ = ∫|ψ̂₀(−τ)| dτ`,
`c₀ = 4800πC_δ⁵B₄`, `c₂ = 4c₀I₀C_KK₁`, `c₃ = 4800πc₀K₁(I₀C_K + 4^{j+1}I₀D²G² + 2^KπC_K)`, `D ≥ 0`, `0 ≤ Λ ≤ GR^{2m}F`,
`j ≥ 1`, `K ≥ 4`, `7m + 13 ≤ 4(K − 2)`, `12m + 9 ≤ 4(2j − 2)` and `8m + 9 ≤ 4(K − 4)`, with `X = (qT)³` and
`N₀ = R^{m+4}/M₂`, `2K_XΣ_{m₁∈P1 M₁}(I₀B_J + B_tail)/(|m₁|K₁M) ≤ c₂R^{13}·qM²√𝔖√J̃ + c₃F²`. -/
lemma form_t2 {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u)
    {A T M M₁ M₂ K₁ δ R c₀ c2 c3 I₀ D G Λ : ℝ} {m j K : ℕ} (hT : 1 ≤ T) (hM₁ : 1 / 2 ≤ M₁) (hM₁M : M₁ ≤ M)
    (hM₂ : 1 / 2 ≤ M₂) (hM₂M : M₂ ≤ M) (hK₁ : 1 ≤ K₁) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hRm : R ^ m = (q : ℝ) * T) (hQ9 : ((q : ℝ) * T) ^ (9 * δ) = R ^ 9) (hMR : M ≤ R ^ m)
    (hI₀ : I₀ = ∫ τ, ‖𝓕 psiC (-τ)‖) (hc₀ : c₀ = 4800 * π * LinnikPower.Cdiv δ ^ 5 * B4)
    (hc2 : c2 = 4 * c₀ * I₀ * CK K * K₁)
    (hc3 : c3 = 4800 * π * c₀ * K₁ * (I₀ * CK K + 4 ^ (j + 1) * I₀ * D ^ 2 * G ^ 2 + 2 ^ K * π * CK K))
    (hD : 0 ≤ D) (hΛ : 0 ≤ Λ) (hΛR : Λ ≤ G * R ^ (2 * m) * ∑ b, ∫ u, f b u) (hj : 1 ≤ j) (hK : 4 ≤ K)
    (hKa : 7 * m + 13 ≤ 4 * (K - 2)) (hjb : 12 * m + 9 ≤ 4 * (2 * j - 2)) (hKb : 8 * m + 9 ≤ 4 * (K - 4)) :
    2 * (KX q (K₁ * M) M₁ (((q : ℝ) * T) ^ 3) δ * ∑ m₁ ∈ P1 M₁,
        (I₀ * BJ f A M₂ T (R ^ (m + 4) / M₂) K + Btail f M₂ (K₁ * M) (R ^ (m + 4) / M₂) T D Λ j K) /
          (|(m₁ : ℝ)| * (K₁ * M))) ≤
      c2 * R ^ 13 * (q * M ^ 2 * √(∫ u, ∑ b, f b u ^ 2) * √(Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2))) +
        c3 * (∑ b, ∫ u, f b u) ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  have hR0 : 0 < R := by linarith
  have hM0 : 0 < M := by linarith
  have hCK : 0 ≤ CK K := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (norm_fourier_psiC_le_CK K 0)
  have hI0 : 0 ≤ I₀ := by rw [hI₀]; exact integral_nonneg fun τ => norm_nonneg _
  have hB := B4_nonneg
  have hCd : 0 ≤ LinnikPower.Cdiv δ := le_trans zero_le_one (LinnikPower.one_le_Cdiv hδ hδ1)
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  have hS : 0 ≤ I₀ * BJ f A M₂ T (R ^ (m + 4) / M₂) K + Btail f M₂ (K₁ * M) (R ^ (m + 4) / M₂) T D Λ j K := by
    unfold BJ Btail
    rw [← hI₀]
    positivity
  have h2 := term2_split (q := q) hT hM₁ hM₁M hK₁ hδ hδ1 hS
  rw [hQ9, ← hc₀] at h2
  have h2p := term2_parts (A := A) hf hT hR hRm.symm hM₂ hM₂M hMR hK₁ hc₀0 hD hΛ hΛR hj hK hKa hjb hKb
  rw [← hI₀, ← hc2, ← hc3] at h2p
  exact h2.trans h2p

/-- The assembly at the chosen parameters: for `q ≥ 1`, smooth `f_b ≥ 0` that are `0` for `|u| > A`, `m ≥ 1` with
`13/m ≤ θ`, `K = 2m + 8`, `j = 2m + 11`, `δ = 1/m`, `K₁ = |κ| + 1`, `D' = max(D_j, 0)`, `G' = max(G, 0)`,
`I₀ = ∫|ψ̂₀(−τ)| dτ`, `c₀ = 4800πC_δ⁵B₄`, `c₁ = 160000πB₄²K₁C_δ²`, `c₂ = 4c₀I₀C_KK₁`,
`c₃ = 4800πc₀K₁(I₀C_K + 4^{j+1}I₀D'²G'² + 2^KπC_K)`, `c₄ = 128π(4000K₁D'G'·4^j)²`, `R = (qT)^{1/m}`, `T ≥ 1`,
`M ≤ qT`, `0 ≤ Λ ≤ G(qT)²F`, the decay `Σ_b|f̂_b(ξ)| ≤ D_j(T/|ξ|)^jΛ` for every `j` and every `ξ ≠ 0`,
`1/2 ≤ M₁ ≤ M`, `1/2 ≤ M₂ ≤ M` and `0 ≤ M₃ ≤ M`, `Jint(f, M₁, M₂, M₃, κ) ≤ (c₁ + c₄ + 64c₃ + c₂)(qT)^θ(φ(q)M⁶F² +
qM²√𝔖√J̃)`: round 688's `lemma82_explicit` with `L = K₁M`, `X = (qT)³` and `N₀ = R^{m+4}/M₂`, bounded by `form_t1`,
`form_t2` and `term3_le`, and counted by `form_combine`. -/
lemma form_main {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    (hf : ∀ b u, 0 ≤ f b u) {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0)
    {θ κ G T M Λ M₁ M₂ M₃ δ K₁ D' G' I₀ c₀ c1 c2 c3 c4 R : ℝ} {D : ℕ → ℝ} {m j K : ℕ} (hm1 : 1 ≤ m)
    (hmθ : 13 / (m : ℝ) ≤ θ) (hKdef : K = 2 * m + 8) (hjdef : j = 2 * m + 11) (hδdef : δ = 1 / (m : ℝ))
    (hK₁def : K₁ = |κ| + 1) (hD'def : D' = max (D j) 0) (hG'def : G' = max G 0)
    (hI₀def : I₀ = ∫ τ, ‖𝓕 psiC (-τ)‖) (hc₀def : c₀ = 4800 * π * LinnikPower.Cdiv δ ^ 5 * B4)
    (hc1def : c1 = 160000 * π * B4 ^ 2 * K₁ * LinnikPower.Cdiv δ ^ 2) (hc2def : c2 = 4 * c₀ * I₀ * CK K * K₁)
    (hc3def : c3 = 4800 * π * c₀ * K₁ * (I₀ * CK K + 4 ^ (j + 1) * I₀ * D' ^ 2 * G' ^ 2 + 2 ^ K * π * CK K))
    (hc4def : c4 = 128 * π * (4000 * K₁ * D' * G' * 4 ^ j) ^ 2) (hRdef : R = ((q : ℝ) * T) ^ (1 / (m : ℝ)))
    (hT : 1 ≤ T) (hMQ : M ≤ q * T) (hΛ : 0 ≤ Λ) (hΛF : Λ ≤ G * ((q : ℝ) * T) ^ 2 * ∑ b, ∫ u, f b u)
    (hdec : ∀ (j : ℕ) (ξ : ℝ), ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D j * (T / |ξ|) ^ j * Λ)
    (hM₁ : 1 / 2 ≤ M₁) (hM₁M : M₁ ≤ M) (hM₂ : 1 / 2 ≤ M₂) (hM₂M : M₂ ≤ M) (hM₃ : 0 ≤ M₃) (hM₃M : M₃ ≤ M) :
    Jint f M₁ M₂ M₃ κ ≤ (c1 + c4 + 64 * c3 + c2) * ((q : ℝ) * T) ^ θ *
      ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2 +
        q * M ^ 2 * √(∫ u, ∑ b, f b u ^ 2) * √(Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2))) := by
  have hT0 : 0 < T := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one hm0]; exact_mod_cast hm1
  have hB := B4_nonneg
  have hCd : 0 ≤ LinnikPower.Cdiv δ := le_trans zero_le_one (LinnikPower.one_le_Cdiv hδ hδ1)
  have hCK : 0 ≤ CK K := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (norm_fourier_psiC_le_CK K 0)
  have hI0 : 0 ≤ I₀ := by rw [hI₀def]; exact integral_nonneg fun τ => norm_nonneg _
  have hK₁ : 1 ≤ K₁ := by rw [hK₁def]; linarith [abs_nonneg κ]
  have hD' : 0 ≤ D' := by rw [hD'def]; exact le_max_right _ _
  have hG' : 0 ≤ G' := by rw [hG'def]; exact le_max_right _ _
  have hc₀ : 0 ≤ c₀ := by rw [hc₀def]; positivity
  have hc1 : 0 ≤ c1 := by rw [hc1def]; positivity
  have hc2 : 0 ≤ c2 := by rw [hc2def]; positivity
  have hc3 : 0 ≤ c3 := by rw [hc3def]; positivity
  have hc4 : 0 ≤ c4 := by rw [hc4def]; positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hQ1 : (1 : ℝ) ≤ q * T := one_le_mul_of_one_le_of_one_le hq1 hT
  obtain ⟨hR1, hRm, hRk⟩ := rpow_inv_facts hQ1 hm1 hRdef
  have hM : 1 / 2 ≤ M := hM₁.trans hM₁M
  have hM0 : 0 ≤ M := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  have hF0 : 0 ≤ ∑ b, ∫ u, f b u := Finset.sum_nonneg fun b _ => integral_nonneg fun u => hf b u
  -- the hypotheses at the chosen parameters
  have hdec' : ∀ ξ : ℝ, ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D' * (T / |ξ|) ^ j * Λ := fun ξ hξ =>
    (hdec j ξ hξ).trans (by rw [hD'def]; gcongr; exact le_max_left _ _)
  have hΛF' : Λ ≤ G' * ((q : ℝ) * T) ^ 2 * ∑ b, ∫ u, f b u :=
    hΛF.trans (by rw [hG'def]; gcongr; exact le_max_left _ _)
  have hΛR : Λ ≤ G' * R ^ (2 * m) * ∑ b, ∫ u, f b u := by rw [pow_mul', hRm]; exact hΛF'
  have hMR : M ≤ R ^ m := by rw [hRm]; exact hMQ
  have hL : 0 < K₁ * M := by rw [hK₁def]; positivity
  have hκL : κ * M₃ ≤ K₁ * M := by
    have h1 : κ * M₃ ≤ |κ| * M₃ := mul_le_mul_of_nonneg_right (le_abs_self κ) hM₃
    have h2 : |κ| * M₃ ≤ |κ| * M := mul_le_mul_of_nonneg_left hM₃M (abs_nonneg κ)
    have h3 : (|κ| + 1) * M = |κ| * M + M := by ring
    rw [hK₁def, h3]; linarith
  have hR0 : 0 < R := by linarith
  have hN₀ : 0 < R ^ (m + 4) / M₂ := by positivity
  have hX : (1 : ℝ) ≤ ((q : ℝ) * T) ^ 3 := one_le_pow₀ hQ1
  have hK4 : 4 ≤ K := by omega
  have hj1 : 1 ≤ j := by omega
  have hj10 : 10 ≤ j := by omega
  have hKa : 7 * m + 13 ≤ 4 * (K - 2) := by omega
  have hjb : 12 * m + 9 ≤ 4 * (2 * j - 2) := by omega
  have hKb : 8 * m + 9 ≤ 4 * (K - 4) := by omega
  -- round 688's bound
  have hM₁0 : 0 < M₁ := by linarith
  have hexp := lemma82_explicit (L := K₁ * M) (X := ((q : ℝ) * T) ^ 3) (N₀ := R ^ (m + 4) / M₂) (δ := δ)
    (M₃ := M₃) (κ := κ) hfs hf hA hM₁0 hM₂0 hL hκL hδ hδ1 hX hT hN₀ hK4 hj1 hD' hΛ hdec'
  rw [← hI₀def] at hexp
  -- the three terms
  have hq2 : (q : ℝ) ^ (2 * δ) ≤ R ^ 2 := by
    calc (q : ℝ) ^ (2 * δ) ≤ ((q : ℝ) * T) ^ (2 * δ) :=
          Real.rpow_le_rpow (by positivity) (le_mul_of_one_le_right (by positivity) hT) (by positivity)
      _ = R ^ 2 := by rw [hδdef, ← hRk 2]; norm_num
  have h1 := form_t1 hf hM₁ hM₁M hM₂ hM₂M hK₁ hδ hδ1 hq2 hc1def
  have hQ9 : ((q : ℝ) * T) ^ (9 * δ) = R ^ 9 := by rw [hδdef, ← hRk 9]; norm_num
  have h2 := form_t2 (A := A) hf hT hM₁ hM₁M hM₂ hM₂M hK₁ hδ hδ1 hR1 hRm hQ9 hMR hI₀def hc₀def hc2def hc3def hD' hΛ
    hΛR hj1 hK4 hKa hjb hKb
  have h3 := term3_le hT hM₁ hM₁M hMQ hM₂ hM₂M hK₁ hD' hG' hΛ hΛF' hj10
  rw [← hc4def] at h3
  -- the count
  have hR13 : R ^ 13 ≤ ((q : ℝ) * T) ^ θ := by
    rw [← hRk 13]
    refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
    rw [← mul_div_assoc, mul_one]
    exact_mod_cast hmθ
  have hφ1 : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hM6 : (1 / 64 : ℝ) ≤ M ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num) hM 6
    norm_num at h ⊢
    linarith
  have hF2 : (∑ b, ∫ u, f b u) ^ 2 ≤ 64 * ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2) :=
    calc (∑ b, ∫ u, f b u) ^ 2 = 64 * (1 * (1 / 64) * (∑ b, ∫ u, f b u) ^ 2) := by ring
      _ ≤ 64 * ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2) := by gcongr
  exact form_combine hexp h1 h2 h3 hR1 hR13 hF2 hc1 hc2 hc3 hc4 (by positivity) (by positivity)

/-- **Their Lemma 8.2, in their form**: for `θ > 0`, real `κ` and `G`, and `D : ℕ → ℝ`, there is `C ≥ 0` such that,
for `q ≥ 1`, `T ≥ 1`, `M ≤ qT`, smooth `f_b ≥ 0` that are `0` for `|u| > A`, `0 ≤ Λ ≤ G(qT)²F` and the decay
`Σ_b|f̂_b(ξ)| ≤ D_j(T/|ξ|)^jΛ` for every `j` and every `ξ ≠ 0`, and `0 < M₁ ≤ M`, `0 < M₂ ≤ M` and `0 ≤ M₃ ≤ M`,
`Jint(f, M₁, M₂, M₃, κ) ≤ C(qT)^θ(φ(q)M⁶F² + qM²√𝔖√J̃)`, with `F = Σ_b∫f_b`, `𝔖 = ∫Σ_bf_b²` and
`J̃ = Jint(f̃, M₂, M₂, M₂, 4|A| + 2)`. -/
theorem lemma82_form {θ : ℝ} (hθ : 0 < θ) (κ G : ℝ) (D : ℕ → ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) [NeZero q] (T M A Λ : ℝ) (f : (ZMod q)ˣ → ℝ → ℝ), 1 ≤ T → M ≤ q * T →
      (∀ b, ContDiff ℝ ∞ (f b)) → (∀ b u, 0 ≤ f b u) → (∀ b u, A < |u| → f b u = 0) → 0 ≤ Λ →
      Λ ≤ G * ((q : ℝ) * T) ^ 2 * ∑ b, ∫ u, f b u →
      (∀ (j : ℕ) (ξ : ℝ), ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D j * (T / |ξ|) ^ j * Λ) →
      ∀ M₁ M₂ M₃ : ℝ, 0 < M₁ → M₁ ≤ M → 0 < M₂ → M₂ ≤ M → 0 ≤ M₃ → M₃ ≤ M →
        Jint f M₁ M₂ M₃ κ ≤ C * ((q : ℝ) * T) ^ θ * ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2 +
          q * M ^ 2 * √(∫ u, ∑ b, f b u ^ 2) * √(Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2))) := by
  -- the parameters: `m` with `13/m ≤ θ`, `K = 2m + 8`, `j = 2m + 11`, `δ = 1/m`
  obtain ⟨m, hm1, hmθ⟩ : ∃ m : ℕ, 1 ≤ m ∧ 13 / (m : ℝ) ≤ θ := by
    refine ⟨⌈13 / θ⌉₊ + 1, by omega, ?_⟩
    have h1 : 13 / θ ≤ (⌈13 / θ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : 13 ≤ (⌈13 / θ⌉₊ : ℝ) * θ := (div_le_iff₀ hθ).1 h1
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = 2 * m + 8 := ⟨_, rfl⟩
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = 2 * m + 11 := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (m : ℝ) := ⟨_, rfl⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one hm0]; exact_mod_cast hm1
  -- the constants
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : ℝ, K₁ = |κ| + 1 := ⟨_, rfl⟩
  obtain ⟨D', hD'def⟩ : ∃ D' : ℝ, D' = max (D j) 0 := ⟨_, rfl⟩
  obtain ⟨G', hG'def⟩ : ∃ G' : ℝ, G' = max G 0 := ⟨_, rfl⟩
  obtain ⟨I₀, hI₀def⟩ : ∃ I₀ : ℝ, I₀ = ∫ τ, ‖𝓕 psiC (-τ)‖ := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀def⟩ : ∃ c : ℝ, c = 4800 * π * LinnikPower.Cdiv δ ^ 5 * B4 := ⟨_, rfl⟩
  obtain ⟨c1, hc1def⟩ : ∃ c : ℝ, c = 160000 * π * B4 ^ 2 * K₁ * LinnikPower.Cdiv δ ^ 2 := ⟨_, rfl⟩
  obtain ⟨c2, hc2def⟩ : ∃ c : ℝ, c = 4 * c₀ * I₀ * CK K * K₁ := ⟨_, rfl⟩
  obtain ⟨c3, hc3def⟩ : ∃ c : ℝ,
      c = 4800 * π * c₀ * K₁ * (I₀ * CK K + 4 ^ (j + 1) * I₀ * D' ^ 2 * G' ^ 2 + 2 ^ K * π * CK K) := ⟨_, rfl⟩
  obtain ⟨c4, hc4def⟩ : ∃ c : ℝ, c = 128 * π * (4000 * K₁ * D' * G' * 4 ^ j) ^ 2 := ⟨_, rfl⟩
  have hB := B4_nonneg
  have hCd : 0 ≤ LinnikPower.Cdiv δ := le_trans zero_le_one (LinnikPower.one_le_Cdiv hδ hδ1)
  have hCK : 0 ≤ CK K := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (norm_fourier_psiC_le_CK K 0)
  have hI0 : 0 ≤ I₀ := by rw [hI₀def]; exact integral_nonneg fun τ => norm_nonneg _
  have hK₁ : 0 ≤ K₁ := by rw [hK₁def]; positivity
  have hD' : 0 ≤ D' := by rw [hD'def]; exact le_max_right _ _
  have hG' : 0 ≤ G' := by rw [hG'def]; exact le_max_right _ _
  have hc₀ : 0 ≤ c₀ := by rw [hc₀def]; positivity
  have hc1 : 0 ≤ c1 := by rw [hc1def]; positivity
  have hc2 : 0 ≤ c2 := by rw [hc2def]; positivity
  have hc3 : 0 ≤ c3 := by rw [hc3def]; positivity
  have hc4 : 0 ≤ c4 := by rw [hc4def]; positivity
  refine ⟨c1 + c4 + 64 * c3 + c2, by positivity, ?_⟩
  intro q _ T M A Λ f hT hMQ hfs hf hA hΛ hΛF hdec M₁ M₂ M₃ hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M
  have hT0 : 0 < T := by linarith
  by_cases hsmall : M₁ < 1 / 2 ∨ M₂ < 1 / 2
  · rw [Jint_eq_zero f M₃ κ hsmall]
    positivity
  push Not at hsmall
  exact form_main hfs hf hA hm1 hmθ hKdef hjdef hδdef hK₁def hD'def hG'def hI₀def hc₀def hc1def hc2def hc3def hc4def
    rfl hT hMQ hΛ hΛF hdec hsmall.1 hM₁M hsmall.2 hM₂M hM₃ hM₃M
end LinnikCGLForm

#print axioms LinnikCGLForm.term1_le
#print axioms LinnikCGLForm.term3_le
#print axioms LinnikCGLForm.term2_parts
#print axioms LinnikCGLForm.lemma82_form
