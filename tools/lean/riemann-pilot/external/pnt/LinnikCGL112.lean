/-
# Round 667: their (11.2), the blocks of their Proposition 7.2 summed (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 657's `prop72` bounds `S₃`, its sums truncated at `0 < |m_i| ≤ M`, by `3Σ_{k≤log₂M}Σ_{m⃗∈B_k}A_k(m⃗)` plus three
explicit errors, with the dyadic blocks `B_k` of round 660's `blk` and `A_k = 2C_J(0)d(q)(N²/(q²2^k))Ĩ_{2^k}`. Round
666's `block_le` bounds each block by `(Σ_{m⃗∈B_k}Ĩ)² ≤ 3φ(q)|R|V_k`. This file takes the square root and sums over `k`.
Their step: "Gathering all these estimates together, we arrive at S₃ ⪅_ϵ (N²/(q²M₂)) (ϕ(q)|W|)^{1/2} ϕ(q)^{3/2} (M₂⁶|W|²
+ M₂⁴E(W))^{1/2} + |W| ≤ N²M₂²|W|^{3/2} + N²M₂|W|^{1/2}E(W)^{1/2}. Since M₂ ⪅ qT/N, we get (11.2) S₃ ⪅ (qT)²|W|^{3/2} +
qTN|W|^{1/2}E(W)^{1/2}." (text layer lines 5855–5866; spaces restored; the fraction, subscripts and exponents
transcribed).

The stack's form. With `G = ∫ψ̃₀·E + |R|⁴D_K/X^K` (`Gq`), `P = 12C(qT)^εX³|R|` and `M_k = 2^{k+1}`, `3φ(q)|R|V_k` is
`((k + 1)∫ψ̃₀·φ(q)²)²·P·(9M_k⁶|R|² + 8M_k⁴G)`, and `√(9M_k⁶|R|² + 8M_k⁴G) ≤ 3M_k³|R| + 3M_k²√G`. So
`Σ_{m⃗∈B_k}Ĩ ≤ (k + 1)∫ψ̃₀·φ(q)²√P(24·2^{3k}|R| + 12·2^{2k}√G)` (`sum_blk_It_le`). With `φ(q) ≤ q`, `k ≤ log₂M` and
`2^k ≤ M`, each block's `Σ_{m⃗∈B_k}A_k` is at most `2C_J(0)d(q)∫ψ̃₀(log₂M + 1)√P(24(NM)²|R| + 12N²M√G)`, and the
`log₂M + 1` blocks give `S3_le_blocks`, with round 657's three explicit errors carried unchanged. The hypothesis
`NM/q ≤ XT`, which round 665 needs on every block, plays the part of their "M₂ ⪅ qT/N" and gives the form of (11.2)
(`S3_le_112`). The stack's `(log₂M + 1)²` has one factor from the number of blocks and one from the `4(k + 1)²` of round
666's `V_k`, under the square root; it is a power of a logarithm, which their `⪅` absorbs.

Plain statements, with `q ≥ 1`, `E` the energy, `G = ∫ψ̃₀·E + |R|⁴D_K/X^K`, `P = 12C(qT)^εX³|R|` and the constants
`C ≥ 0` and `Q₀` that round 666's `block_le` takes from `CGLP81`, for `0 < ϖ < 1`, `ε > 0` and `K ∈ ℕ`.
* `sum_blk_It_le`: for `χ` injective on `R`, `qT ≥ Q₀`, `T ≥ 1`, points `|t_i| ≤ T`, `N > 0`, `X ≥ 1`,
  `2^kN/q ≤ XT` and `2^{k+1} ≤ (qT)^ϖ`, `Σ_{m⃗∈B_k}Ĩ ≤ (k + 1)∫ψ̃₀·φ(q)²√P(24·2^{3k}|R| + 12·2^{2k}√G)`.
* `S3_le_blocks`: for `χ` injective on `R`, `qT ≥ Q₀`, `T ≥ 1`, points `|t_i| ≤ T`, `N > 0`, `X ≥ 1`, `M ≥ 1`,
  `K_t ≥ 2`, `NM/q ≤ XT` and `2M ≤ (qT)^ϖ`, `S₃ ≤ 6C_J(0)d(q)∫ψ̃₀(log₂M + 1)²√P(24(NM)²|R| + 12N²M√G)` plus round
  657's three errors at `M`, `K_t` and any `K′`.
* `S3_le_112`: under the same hypotheses, the same with `(NM)²` and `N²M` replaced by `(XqT)²` and `XqTN`.

* `Gq`, `Gq_nonneg`: the energy term.
* `sum_blk_It_le`: one block.
* `block_alg`, `S3_le_blocks`, `S3_le_112`: their (11.2).

The file imports `LinnikCGLBlock.lean`.
-/

import LinnikCGLBlock

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGL112

open LinnikCGLRFact LinnikCGLP71 LinnikCGLRt LinnikCGLP72 LinnikCGLMom LinnikCGLMom4 LinnikCGLCS LinnikCGLJ
  LinnikCGLFb LinnikCGLDecay LinnikCGLBlock LinnikCGLS23 LinnikCGLTrunc LinnikCGLMat

universe u

/-! ### The energy term -/

/-- `G = ∫ψ̃₀·E + |R|⁴D_K/X^K`: the energy with the error of round 659's Lemma 9.2. -/
def Gq {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (X : ℝ) (K : ℕ) : ℝ :=
  (∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K

lemma Gq_nonneg {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {X : ℝ}
    (hX : 0 < X) (K : ℕ) : 0 ≤ Gq R χ t X K := by
  unfold Gq
  have h1 : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  have h2 := Dpsi_nonneg K
  positivity

/-! ### One block -/

/-- **One block, square-rooted**: from `CGLP81`, for `0 < ϖ < 1`, `ε > 0` and `K ∈ ℕ` there are `C ≥ 0` and `Q₀` such
that, for `χ` injective on `R`, `qT ≥ Q₀`, `T ≥ 1`, points `|t_i| ≤ T`, `N > 0`, `X ≥ 1`, `2^kN/q ≤ XT` and
`2^{k+1} ≤ (qT)^ϖ`, `Σ_{m⃗∈B_k}Ĩ ≤ (k + 1)∫ψ̃₀·φ(q)²√P(24·2^{3k}|R| + 12·2^{2k}√G)` with
`P = 12C(qT)^εX³|R|`. -/
theorem sum_blk_It_le (hP : CGLP81) {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1) {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι)
      (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {X T : ℝ} (M k : ℕ), Set.InjOn χ R → Q₀ ≤ (q : ℝ) * T →
      1 ≤ T → (∀ i ∈ R, |t i| ≤ T) → 0 < N → 1 ≤ X → N * 2 ^ k / q ≤ X * T →
      (2 : ℝ) ^ (k + 1) ≤ ((q : ℝ) * T) ^ ϖ →
      ∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2 ≤ (k + 1) * (∫ x, psi0 x) * (q.totient : ℝ) ^ 2 *
        Real.sqrt (12 * C * ((q : ℝ) * T) ^ ε * X ^ 3 * R.card) *
        (24 * ((2 : ℝ) ^ k) ^ 3 * R.card + 12 * ((2 : ℝ) ^ k) ^ 2 * Real.sqrt (Gq R χ t X K)) := by
  obtain ⟨C, Q₀, hC0, hB⟩ := block_le hP hϖ0 hϖ1 hε K
  refine ⟨C, Q₀, hC0, ?_⟩
  intro ι q hq0 N R χ t X T M k hinj hQ hT ht hN hX hLX hMϖ
  obtain ⟨-, -, hsq⟩ := hB R χ t M k hinj hQ hT ht hN hX hLX hMϖ
  have hX0 : 0 < X := by linarith
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hqT : 0 ≤ ((q : ℝ) * T) ^ ε := Real.rpow_nonneg (mul_pos hq (by linarith)).le ε
  have hI0 : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  have hG0 := Gq_nonneg R χ t hX0 K
  have hφ0 : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  have hRc0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  set P := 12 * C * ((q : ℝ) * T) ^ ε * X ^ 3 * R.card with hPdef
  have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hqT) (by positivity)) hRc0
  set a := ((k : ℝ) + 1) * (∫ x, psi0 x) * (q.totient : ℝ) ^ 2 with ha
  have ha0 : 0 ≤ a := mul_nonneg (mul_nonneg (by positivity) hI0) (sq_nonneg _)
  set G := Gq R χ t X K with hG
  set Mk : ℝ := (2 : ℝ) ^ (k + 1) with hMk
  have hM0 : 0 ≤ Mk := by positivity
  set Q := 9 * Mk ^ 6 * (R.card : ℝ) ^ 2 + 8 * Mk ^ 4 * G with hQdef
  have hV : 3 * (q.totient : ℝ) * R.card * Vblk R χ t C ε T X K k = a ^ 2 * (P * Q) := by
    unfold Vblk
    rw [hQdef, hG, hMk, ha, hPdef]
    unfold Gq
    ring
  have hs : ∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2 ≤ Real.sqrt (a ^ 2 * (P * Q)) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (hsq.trans_eq hV))
  have hsqrt : Real.sqrt (a ^ 2 * (P * Q)) = a * Real.sqrt P * Real.sqrt Q := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha0, Real.sqrt_mul hP0]
    ring
  have hsG : Real.sqrt G ^ 2 = G := Real.sq_sqrt hG0
  have hsG0 : 0 ≤ Real.sqrt G := Real.sqrt_nonneg G
  have hQle : Real.sqrt Q ≤ 3 * Mk ^ 3 * R.card + 3 * Mk ^ 2 * Real.sqrt G := by
    have hB0 : 0 ≤ 3 * Mk ^ 3 * R.card + 3 * Mk ^ 2 * Real.sqrt G :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hM0 3)) hRc0)
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hM0 2)) hsG0)
    have h1 : 0 ≤ Mk ^ 5 * R.card * Real.sqrt G := mul_nonneg (mul_nonneg (pow_nonneg hM0 5) hRc0) hsG0
    have h2 : 0 ≤ Mk ^ 4 * G := mul_nonneg (pow_nonneg hM0 4) hG0
    have hle : Q ≤ (3 * Mk ^ 3 * R.card + 3 * Mk ^ 2 * Real.sqrt G) ^ 2 := by
      have e : (3 * Mk ^ 3 * R.card + 3 * Mk ^ 2 * Real.sqrt G) ^ 2 =
          9 * Mk ^ 6 * (R.card : ℝ) ^ 2 + 18 * (Mk ^ 5 * R.card * Real.sqrt G) + 9 * Mk ^ 4 * Real.sqrt G ^ 2 := by
        ring
      rw [e, hsG, hQdef]
      linarith
    calc Real.sqrt Q ≤ Real.sqrt ((3 * Mk ^ 3 * R.card + 3 * Mk ^ 2 * Real.sqrt G) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 3 * Mk ^ 3 * R.card + 3 * Mk ^ 2 * Real.sqrt G := Real.sqrt_sq hB0
  have hPs0 : 0 ≤ a * Real.sqrt P := mul_nonneg ha0 (Real.sqrt_nonneg P)
  calc ∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2
      ≤ a * Real.sqrt P * Real.sqrt Q := hs.trans_eq hsqrt
    _ ≤ a * Real.sqrt P * (3 * Mk ^ 3 * R.card + 3 * Mk ^ 2 * Real.sqrt G) := mul_le_mul_of_nonneg_left hQle hPs0
    _ = (k + 1) * (∫ x, psi0 x) * (q.totient : ℝ) ^ 2 * Real.sqrt P *
          (24 * ((2 : ℝ) ^ k) ^ 3 * R.card + 12 * ((2 : ℝ) ^ k) ^ 2 * Real.sqrt G) := by
        rw [ha, hMk]
        ring

/-! ### Their (11.2) -/

/-- The algebra of one block: `A N²/(q²u)·(k + 1)Iφ²s(24u³ρ + 12u²g) = AIs·(k + 1)(φ²/q²)(24N²u²ρ + 12N²ug)`. -/
lemma block_alg (A N q u I φ s g ρ k : ℝ) (hq : q ≠ 0) (hu : u ≠ 0) :
    A * N ^ 2 / (q ^ 2 * u) * ((k + 1) * I * φ ^ 2 * s * (24 * u ^ 3 * ρ + 12 * u ^ 2 * g)) =
      A * I * s * ((k + 1) * (φ ^ 2 / q ^ 2) * (24 * N ^ 2 * u ^ 2 * ρ + 12 * N ^ 2 * u * g)) := by
  field_simp

/-- **The blocks summed**: from `CGLP81`, for `0 < ϖ < 1`, `ε > 0` and `K ∈ ℕ` there are `C ≥ 0` and `Q₀` such that,
for `χ` injective on `R`, `qT ≥ Q₀`, `T ≥ 1`, points `|t_i| ≤ T`, `N > 0`, `X ≥ 1`, `M ≥ 1`, `K_t ≥ 2`, `NM/q ≤ XT`
and `2M ≤ (qT)^ϖ`, `S₃ ≤ 6C_J(0)d(q)∫ψ̃₀(log₂M + 1)²√P(24(NM)²|R| + 12N²M√G)` plus round 657's three errors. -/
theorem S3_le_blocks (hP : CGLP81) {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1) {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [DecidableEq ι] {q : ℕ} [NeZero q] {N : ℝ} {R : Finset ι}
      {χ : ι → DirichletCharacter ℂ q} (t : ι → ℝ) {X T : ℝ} {M Kt : ℕ} (K' : ℕ), Set.InjOn χ R →
      Q₀ ≤ (q : ℝ) * T → 1 ≤ T → (∀ i ∈ R, |t i| ≤ T) → 0 < N → 1 ≤ X → 1 ≤ M → 2 ≤ Kt →
      N * M / q ≤ X * T → 2 * (M : ℝ) ≤ ((q : ℝ) * T) ^ ϖ →
      S3 q N R χ t ≤ 6 * CJ 0 * q.divisors.card * (∫ x, psi0 x) * (Nat.log 2 M + 1) ^ 2 *
          Real.sqrt (12 * C * ((q : ℝ) * T) ^ ε * X ^ 3 * R.card) *
          (24 * (N * M) ^ 2 * R.card + 12 * N ^ 2 * M * Real.sqrt (Gq R χ t X K)) +
        3 * (2 * (M : ℝ)) ^ 3 * E71 q N R X K' + R.card * |muP q N - mu0 q N| ^ 3 +
        3 * (R.card : ℝ) ^ 3 * tauM N q T M Kt * (2 * N + 1 + tauM N q T M Kt) ^ 2 := by
  obtain ⟨C, Q₀, hC0, hB⟩ := sum_blk_It_le.{u} hP hϖ0 hϖ1 hε K
  refine ⟨C, Q₀, hC0, ?_⟩
  intro ι _ q hq0 N R χ t X T M Kt K' hinj hQ hT ht hN hX hM hKt hNM hMϖ
  have hX0 : 0 < X := by linarith
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hqT : 0 ≤ ((q : ℝ) * T) ^ ε := Real.rpow_nonneg (mul_pos hq (by linarith)).le ε
  have h72 := prop72 hN hinj t ht hM hKt hX0 K'
  set Kl := Nat.log 2 M with hKl
  set P := 12 * C * ((q : ℝ) * T) ^ ε * X ^ 3 * R.card with hPdef
  set G := Gq R χ t X K with hG
  have hI0 : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  have hG0 : 0 ≤ G := Gq_nonneg R χ t hX0 K
  have hd0 : (0 : ℝ) ≤ q.divisors.card := Nat.cast_nonneg _
  have hRc0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have hN0 : 0 ≤ N := hN.le
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  -- the constant in front
  set c := 2 * CJ 0 * q.divisors.card * (∫ x, psi0 x) * Real.sqrt P with hc
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (CJ_nonneg 0)) hd0) hI0)
    (Real.sqrt_nonneg _)
  set W := 24 * (N * M) ^ 2 * R.card + 12 * N ^ 2 * M * Real.sqrt G with hW
  have hKM : 2 ^ Kl ≤ M := by
    rw [hKl]
    exact Nat.pow_log_le_self 2 (by omega)
  clear_value Kl P G c W
  -- each block
  have hblock : ∀ k ∈ Finset.range (Kl + 1),
      ∑ m ∈ blk M k, Ak N R χ t X k m.1 m.2.1 m.2.2 ≤ c * ((Kl + 1) * W) := by
    intro k hk
    have hkK : k ≤ Kl := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h2k : (2 : ℝ) ^ k ≤ M := by
      have : 2 ^ k ≤ M := (Nat.pow_le_pow_right (by norm_num) hkK).trans hKM
      exact_mod_cast this
    have h2k0 : (0 : ℝ) < 2 ^ k := by positivity
    have hLk : N * 2 ^ k / q ≤ X * T :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2k hN0) hq.le).trans hNM
    have hMk : (2 : ℝ) ^ (k + 1) ≤ ((q : ℝ) * T) ^ ϖ := by
      rw [pow_succ]
      linarith
    have hS := hB R χ t M k hinj hQ hT ht hN hX hLk hMk
    rw [← hPdef, ← hG] at hS
    have hAk : ∑ m ∈ blk M k, Ak N R χ t X k m.1 m.2.1 m.2.2 =
        2 * CJ 0 * q.divisors.card * N ^ 2 / (q ^ 2 * 2 ^ k) *
          ∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2 := by
      unfold Ak
      rw [Finset.mul_sum]
    have hck : 0 ≤ 2 * CJ 0 * q.divisors.card * N ^ 2 / (q ^ 2 * 2 ^ k) :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (CJ_nonneg 0)) hd0) (sq_nonneg _))
        (by positivity)
    have hφq : (q.totient : ℝ) ^ 2 / (q : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.totient_le q) 2
    have hφq0 : 0 ≤ (q.totient : ℝ) ^ 2 / (q : ℝ) ^ 2 := by positivity
    have hk1 : (k : ℝ) + 1 ≤ Kl + 1 := by
      have : (k : ℝ) ≤ Kl := by exact_mod_cast hkK
      linarith
    have hinner : 24 * N ^ 2 * ((2 : ℝ) ^ k) ^ 2 * R.card + 12 * N ^ 2 * 2 ^ k * Real.sqrt G ≤ W := by
      rw [hW]
      have h1 : ((2 : ℝ) ^ k) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ h2k0.le h2k 2
      have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
      have e1 : (N * M) ^ 2 = N ^ 2 * (M : ℝ) ^ 2 := by ring
      rw [e1]
      have hA : 24 * N ^ 2 * ((2 : ℝ) ^ k) ^ 2 * R.card ≤ 24 * (N ^ 2 * (M : ℝ) ^ 2) * R.card :=
        mul_le_mul_of_nonneg_right (by nlinarith) hRc0
      have hB' : 12 * N ^ 2 * 2 ^ k * Real.sqrt G ≤ 12 * N ^ 2 * M * Real.sqrt G :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2k (by positivity)) (Real.sqrt_nonneg _)
      linarith
    have hinner0 : 0 ≤ 24 * N ^ 2 * ((2 : ℝ) ^ k) ^ 2 * R.card + 12 * N ^ 2 * 2 ^ k * Real.sqrt G := by
      have := Real.sqrt_nonneg G
      positivity
    rw [hAk]
    calc 2 * CJ 0 * q.divisors.card * N ^ 2 / (q ^ 2 * 2 ^ k) *
          ∑ m ∈ blk M k, It N R χ t X (2 ^ k) m.1 m.2.1 m.2.2
        ≤ 2 * CJ 0 * q.divisors.card * N ^ 2 / (q ^ 2 * 2 ^ k) *
          ((k + 1) * (∫ x, psi0 x) * (q.totient : ℝ) ^ 2 * Real.sqrt P *
            (24 * ((2 : ℝ) ^ k) ^ 3 * R.card + 12 * ((2 : ℝ) ^ k) ^ 2 * Real.sqrt G)) :=
          mul_le_mul_of_nonneg_left hS hck
      _ = c * (((k : ℝ) + 1) * ((q.totient : ℝ) ^ 2 / (q : ℝ) ^ 2) *
            (24 * N ^ 2 * ((2 : ℝ) ^ k) ^ 2 * R.card + 12 * N ^ 2 * 2 ^ k * Real.sqrt G)) := by
          rw [hc]
          exact block_alg _ _ _ _ _ _ _ _ _ _ hq.ne' h2k0.ne'
      _ ≤ c * (((Kl : ℝ) + 1) * 1 * W) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0
          have hA : ((k : ℝ) + 1) * ((q.totient : ℝ) ^ 2 / (q : ℝ) ^ 2) ≤ ((Kl : ℝ) + 1) * 1 :=
            mul_le_mul hk1 hφq hφq0 (by positivity)
          have hA0 : (0 : ℝ) ≤ ((Kl : ℝ) + 1) * 1 := by positivity
          exact mul_le_mul hA hinner hinner0 hA0
      _ = c * ((Kl + 1) * W) := by ring
  -- the sum over the blocks
  have hmain : 3 * ∑ k ∈ Finset.range (Kl + 1), ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M,
      (if Nat.log 2 m₂.natAbs = k ∧ |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X k m₁ m₂ m₃ else 0) ≤
      6 * CJ 0 * q.divisors.card * (∫ x, psi0 x) * (Kl + 1) ^ 2 * Real.sqrt P * W := by
    rw [Finset.sum_congr rfl fun k _ => sum_blk M k (Ak N R χ t X k)]
    calc 3 * ∑ k ∈ Finset.range (Kl + 1), ∑ m ∈ blk M k, Ak N R χ t X k m.1 m.2.1 m.2.2
        ≤ 3 * ∑ _k ∈ Finset.range (Kl + 1), c * ((Kl + 1) * W) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hblock) (by norm_num)
      _ = 6 * CJ 0 * q.divisors.card * (∫ x, psi0 x) * (Kl + 1) ^ 2 * Real.sqrt P * W := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc]
          push_cast
          ring
  exact h72.trans (add_le_add (add_le_add (add_le_add hmain le_rfl) le_rfl) le_rfl)

/-- **Their (11.2), in explicit form**: under the hypotheses of `S3_le_blocks`, `NM ≤ XqT` turns its bound into
`S₃ ≤ 6C_J(0)d(q)∫ψ̃₀(log₂M + 1)²√P(24(XqT)²|R| + 12XqTN√G)` plus round 657's three errors. -/
theorem S3_le_112 (hP : CGLP81) {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1) {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [DecidableEq ι] {q : ℕ} [NeZero q] {N : ℝ} {R : Finset ι}
      {χ : ι → DirichletCharacter ℂ q} (t : ι → ℝ) {X T : ℝ} {M Kt : ℕ} (K' : ℕ), Set.InjOn χ R →
      Q₀ ≤ (q : ℝ) * T → 1 ≤ T → (∀ i ∈ R, |t i| ≤ T) → 0 < N → 1 ≤ X → 1 ≤ M → 2 ≤ Kt →
      N * M / q ≤ X * T → 2 * (M : ℝ) ≤ ((q : ℝ) * T) ^ ϖ →
      S3 q N R χ t ≤ 6 * CJ 0 * q.divisors.card * (∫ x, psi0 x) * (Nat.log 2 M + 1) ^ 2 *
          Real.sqrt (12 * C * ((q : ℝ) * T) ^ ε * X ^ 3 * R.card) *
          (24 * (X * ((q : ℝ) * T)) ^ 2 * R.card + 12 * (X * ((q : ℝ) * T)) * N * Real.sqrt (Gq R χ t X K)) +
        3 * (2 * (M : ℝ)) ^ 3 * E71 q N R X K' + R.card * |muP q N - mu0 q N| ^ 3 +
        3 * (R.card : ℝ) ^ 3 * tauM N q T M Kt * (2 * N + 1 + tauM N q T M Kt) ^ 2 := by
  obtain ⟨C, Q₀, hC0, hB⟩ := S3_le_blocks.{u} hP hϖ0 hϖ1 hε K
  refine ⟨C, Q₀, hC0, ?_⟩
  intro ι _ q hq0 N R χ t X T M Kt K' hinj hQ hT ht hN hX hM hKt hNM hMϖ
  have h := hB t K' hinj hQ hT ht hN hX hM hKt hNM hMϖ
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hX0 : 0 < X := by linarith
  have hNM' : N * M ≤ X * ((q : ℝ) * T) := by
    rw [div_le_iff₀ hq] at hNM
    linarith
  have hNM0 : 0 ≤ N * M := mul_nonneg hN.le (by positivity)
  have hRc0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have hpre : 0 ≤ 6 * CJ 0 * q.divisors.card * (∫ x, psi0 x) * (Nat.log 2 M + 1) ^ 2 *
      Real.sqrt (12 * C * ((q : ℝ) * T) ^ ε * X ^ 3 * R.card) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (CJ_nonneg 0)) (Nat.cast_nonneg _))
      (integral_nonneg psi0_nonneg)) (by positivity)) (Real.sqrt_nonneg _)
  have hW : 24 * (N * M) ^ 2 * R.card + 12 * N ^ 2 * M * Real.sqrt (Gq R χ t X K) ≤
      24 * (X * ((q : ℝ) * T)) ^ 2 * R.card + 12 * (X * ((q : ℝ) * T)) * N * Real.sqrt (Gq R χ t X K) := by
    have h1 : (N * M) ^ 2 ≤ (X * ((q : ℝ) * T)) ^ 2 := pow_le_pow_left₀ hNM0 hNM' 2
    have h3 : (N * M) * N ≤ (X * ((q : ℝ) * T)) * N := mul_le_mul_of_nonneg_right hNM' hN.le
    have hs := Real.sqrt_nonneg (Gq R χ t X K)
    have hA : 24 * (N * M) ^ 2 * R.card ≤ 24 * (X * ((q : ℝ) * T)) ^ 2 * R.card :=
      mul_le_mul_of_nonneg_right (by linarith) hRc0
    have hB' : 12 * N ^ 2 * M * Real.sqrt (Gq R χ t X K) ≤
        12 * (X * ((q : ℝ) * T)) * N * Real.sqrt (Gq R χ t X K) := by
      have : 12 * N ^ 2 * (M : ℝ) ≤ 12 * (X * ((q : ℝ) * T)) * N := by nlinarith
      exact mul_le_mul_of_nonneg_right this hs
    linarith
  have := mul_le_mul_of_nonneg_left hW hpre
  linarith

end LinnikCGL112

#print axioms LinnikCGL112.sum_blk_It_le
#print axioms LinnikCGL112.S3_le_blocks
#print axioms LinnikCGL112.S3_le_112
