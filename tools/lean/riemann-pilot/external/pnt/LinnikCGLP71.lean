/-
# Round 654: their Proposition 7.1 (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li's Proposition 7.1: "We have |I′_{m⃗}| ≪_ϵ (N³/q³) ∫_{|m₁v₁+m₂v₂+m₃|≤(qT)^ϵq/N, v₁,v₂∈[1/2,2]}
Σ_{b₁ mod q, (b₁,q)=1} Σ_{b₂ mod q, (b₂,q)=1} |R(v₁,b₁)R(v₂/v₁, b₁⁻¹b₂)R(1/v₂, b₂⁻¹)| · (b₁m₁+b₂m₂+m₃, q) dv₁dv₂
+ O_ϵ((qT)^{−200})" (text layer lines 2041–2066; spaces restored and the display transcribed). The absolute-value bars
are large delimiters, which the text layer encodes as four form-feed characters each, invisible in a listing (lines 2054
and 2065); their positions are read from the PDF (page 23, `CMEX10` glyphs at x = 337.6 and x = 516.7 in the rows
y = 508.1–529.6, the display's first line; `scratchpad/r661/probe/p23_460_545.txt`). Their proof inserts the two bounds
of round 653 into their (7.3), round 652's `Ip_eq`, and applies the triangle inequality. This file does that with
explicit constants.

Plain statement (`prop71`). For `q ≥ 1`, `N > 0`, `X > 0`, every `K`, points `t_i` and characters `χ_i` modulo `q`
(`i ∈ R`) and integers `m₁, m₂, m₃`,
`|I′(m⃗)| ≤ (N/q)³(C₀d(q)∫∫W(v₁, v₂)[|m₁v₁ + m₂v₂ + m₃| ≤ Xq/N] dv₂ dv₁ + (9/4)C_K(2πX)^{−K}φ(q)³|R|³)`.
Both integrals run over `[1/2, 2]`, `[·]` is `1` or `0`, `C_K` is the constant of round 653's `Jk_decay` (`CJ K`),
and `W(v₁, v₂) = Σ_{b₁,b₂}(b₁m₁ + b₂m₂ + m₃, q)|R(v₁, b₁)||R(v₂/v₁, b₂b₁⁻¹)||R(1/v₂, b₂⁻¹)|` with `b₁, b₂` over the
units modulo `q`. Taking `X = (qT)^ε` and `K` large in terms of `ε` makes the second term their
`O_ϵ((qT)^{−200})` when `N`, `q` and `|R|` are at most a power of `qT`; the first is theirs times `C₀d(q)`, the
`d(q)` from round 653's `norm_Cq_le`.

The proof. By round 652's `Ip_eq`, `I′ = (N/q)³∫∫Ψ`, and `Ψ = 0` off `[1/2, 2]²` (round 653's `Jk_eq_zero_of`). On
`[1/2, 2]²`, with `λ = (N/q)(m₁v₁ + m₂v₂ + m₃)` (`norm_Psi_le`):
* where `|λ| ≤ X`, `|Ψ| ≤ C₀d(q)W`, by `|J| ≤ C₀` and `|C_q| ≤ d(q)(·, q)`;
* elsewhere `|Ψ| ≤ C_K(2πX)^{−K}φ(q)³|R|³`, by `|J| ≤ C_K(2π|λ|)^{−K}`, `|C_q| ≤ φ(q)` and `|R(v, a)| ≤ |R|`, the
  number of points, for `v > 0`.
The majorant is measurable and bounded on `[1/2, 2]²`, so it is integrable in `v₂` and its integral over `v₂` in
`v₁`. `‖∫f‖ ≤ ∫g` for `‖f‖ ≤ g` needs only the integrability of `g` (Mathlib's `norm_integral_le_of_norm_le` and
`integral_mono_of_nonneg`).

* `norm_Rf_le`, `norm_Cq_le_totient`: `|R(v, a)| ≤ |R|` for `v > 0`, and `|C_q(n)| ≤ φ(q)`.
* `Wm`, `Wm_nonneg`, `Wm_le`, `measurable_Rf`, `measurable_Wm`: their integrand, bounded and measurable.
* `CJ`, `CJ_nonneg`, `CJ_spec`: the constants of round 653's `Jk_decay`.
* `norm_Psi_le`, `Psi_eq_zero`, `prop71`: the bound.

The file imports `LinnikCGLRam.lean`.
-/

import LinnikCGLRam

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff

noncomputable section

namespace LinnikCGLP71

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLTrunc LinnikCGLProd LinnikCGLRFact
  LinnikCGLRam

/-! ### Pointwise bounds -/

/-- `|R(v, a)| ≤ |R|` for `v > 0`. -/
lemma norm_Rf_le {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {v : ℝ}
    (hv : 0 < v) (a : ZMod q) : ‖Rf R χ t v a‖ ≤ R.card := by
  unfold Rf
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ i ∈ R, ‖(v : ℂ) ^ ((t i : ℂ) * I) * χ i a‖ ≤ 1 := by
    intro i _
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv]
    have hre : ((t i : ℂ) * I).re = 0 := by simp
    rw [hre, Real.rpow_zero, one_mul]
    exact DirichletCharacter.norm_le_one _ _
  calc ∑ i ∈ R, ‖(v : ℂ) ^ ((t i : ℂ) * I) * χ i a‖ ≤ ∑ _i ∈ R, (1 : ℝ) := Finset.sum_le_sum h1
    _ = R.card := by simp

/-- `|C_q(n)| ≤ φ(q)`. -/
lemma norm_Cq_le_totient (q : ℕ) [NeZero q] (n : ZMod q) : ‖Cq q n‖ ≤ q.totient := by
  unfold Cq
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ a : (ZMod q)ˣ, ‖ZMod.stdAddChar ((a : ZMod q) * n)‖ = 1 := fun a => by
    rw [ZMod.stdAddChar_apply, Circle.norm_coe]
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact_mod_cast (ZMod.card_units_eq_totient q).le

/-- The integrand of their Proposition 7.1:
`W(v₁, v₂) = Σ_{b₁,b₂}(b₁m₁ + b₂m₂ + m₃, q)|R(v₁, b₁)||R(v₂/v₁, b₂b₁⁻¹)||R(1/v₂, b₂⁻¹)|`. -/
def Wm {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (m₁ m₂ m₃ : ℤ) (v₁ v₂ : ℝ) : ℝ :=
  ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ,
    (Nat.gcd ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)).val q : ℝ) *
      (‖Rf R χ t v₁ b₁‖ * ‖Rf R χ t (v₂ / v₁) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q)‖ *
        ‖Rf R χ t (1 / v₂) ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q)‖)

lemma Wm_nonneg {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (m₁ m₂ m₃ : ℤ) (v₁ v₂ : ℝ) : 0 ≤ Wm R χ t m₁ m₂ m₃ v₁ v₂ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

lemma Wm_le {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (m₁ m₂ m₃ : ℤ) {v₁ v₂ : ℝ} (h1 : 0 < v₁) (h2 : 0 < v₂) :
    Wm R χ t m₁ m₂ m₃ v₁ v₂ ≤ (q.totient : ℝ) ^ 2 * (q * (R.card : ℝ) ^ 3) := by
  unfold Wm
  have hb : ∀ b₁ b₂ : (ZMod q)ˣ,
      (Nat.gcd ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)).val q : ℝ) *
        (‖Rf R χ t v₁ b₁‖ * ‖Rf R χ t (v₂ / v₁) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q)‖ *
          ‖Rf R χ t (1 / v₂) ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q)‖) ≤ q * (R.card : ℝ) ^ 3 := by
    intro b₁ b₂
    have hg : (Nat.gcd ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)).val q : ℝ)
        ≤ q := by exact_mod_cast Nat.gcd_le_right _ (Nat.pos_of_ne_zero (NeZero.ne q))
    have r1 := norm_Rf_le R χ t h1 (b₁ : ZMod q)
    have r2 := norm_Rf_le R χ t (div_pos h2 h1) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q)
    have r3 := norm_Rf_le R χ t (one_div_pos.2 h2) ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q)
    have hR : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
    calc _ ≤ (q : ℝ) * ((R.card : ℝ) * R.card * R.card) := by
          refine mul_le_mul hg (mul_le_mul (mul_le_mul r1 r2 (norm_nonneg _) hR) r3 (norm_nonneg _)
            (by positivity)) (by positivity) (Nat.cast_nonneg _)
      _ = q * (R.card : ℝ) ^ 3 := by ring
  calc _ ≤ ∑ _b₁ : (ZMod q)ˣ, ∑ _b₂ : (ZMod q)ˣ, (q : ℝ) * (R.card : ℝ) ^ 3 :=
        Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => hb b₁ b₂
    _ = (q.totient : ℝ) ^ 2 * (q * (R.card : ℝ) ^ 3) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card_units_eq_totient]
        ring

lemma measurable_Rf {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (a : ZMod q) : Measurable fun v : ℝ => Rf R χ t v a := by
  unfold Rf
  fun_prop

lemma measurable_Wm {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (m₁ m₂ m₃ : ℤ) : Measurable fun p : ℝ × ℝ => Wm R χ t m₁ m₂ m₃ p.1 p.2 := by
  unfold Wm
  refine Finset.measurable_sum _ fun b₁ _ => Finset.measurable_sum _ fun b₂ _ => ?_
  refine measurable_const.mul ((((measurable_Rf R χ t _).comp measurable_fst).norm.mul
    ((measurable_Rf R χ t _).comp (measurable_snd.div measurable_fst)).norm).mul
    ((measurable_Rf R χ t _).comp (measurable_const.div measurable_snd)).norm)

/-! ### The constants of the decay of `J` -/

/-- The constant of round 653's `Jk_decay` at `K`. -/
def CJ (K : ℕ) : ℝ := Classical.choose (Jk_decay K)

lemma CJ_nonneg (K : ℕ) : 0 ≤ CJ K := (Classical.choose_spec (Jk_decay K)).1

lemma CJ_spec (K : ℕ) {v₁ v₂ : ℝ} (h1 : |v₁| ≤ 2) (h2 : |v₂| ≤ 2) (lam : ℝ) :
    (2 * π * |lam|) ^ K * ‖Jk v₁ v₂ lam‖ ≤ CJ K :=
  (Classical.choose_spec (Jk_decay K)).2 v₁ v₂ lam h1 h2

/-! ### Their Proposition 7.1 -/

/-- **The integrand of their (7.3), bounded**: for `N > 0`, `X > 0` and any `K`, on `[1/2, 2]²`,
`|Ψ| ≤ C₀d(q)W·[|m₁v₁ + m₂v₂ + m₃| ≤ Xq/N] + C_K(2πX)^{−K}φ(q)³|R|³`. -/
lemma norm_Psi_le {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (m₁ m₂ m₃ : ℤ) {X : ℝ} (hX : 0 < X) (K : ℕ) {v₁ v₂ : ℝ}
    (h1 : v₁ ∈ Icc (1 / 2 : ℝ) 2) (h2 : v₂ ∈ Icc (1 / 2 : ℝ) 2) :
    ‖Psi N R χ t m₁ m₂ m₃ v₁ v₂‖ ≤
      CJ 0 * q.divisors.card * (if |m₁ * v₁ + m₂ * v₂ + m₃| ≤ X * q / N then Wm R χ t m₁ m₂ m₃ v₁ v₂ else 0) +
        CJ K / (2 * π * X) ^ K * ((q.totient : ℝ) ^ 3 * (R.card : ℝ) ^ 3) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hv₁ : 0 < v₁ := by linarith [h1.1]
  have hv₂ : 0 < v₂ := by linarith [h2.1]
  have ha₁ : |v₁| ≤ 2 := by rw [abs_of_pos hv₁]; exact h1.2
  have ha₂ : |v₂| ≤ 2 := by rw [abs_of_pos hv₂]; exact h2.2
  set lam := v₁ * (N * m₁ / q) + v₂ * (N * m₂ / q) + N * m₃ / q with hlam
  have hlam' : lam = N / q * (m₁ * v₁ + m₂ * v₂ + m₃) := by rw [hlam]; ring
  set S := ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ,
      Cq q ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)) *
      (Rf R χ t v₁ b₁ * Rf R χ t (v₂ / v₁) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q) *
        Rf R χ t (1 / v₂) ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q)) with hS
  have hPsi : Psi N R χ t m₁ m₂ m₃ v₁ v₂ = Jk v₁ v₂ lam * S := rfl
  have hE0 : 0 ≤ CJ K / (2 * π * X) ^ K * ((q.totient : ℝ) ^ 3 * (R.card : ℝ) ^ 3) := by
    have := CJ_nonneg K; positivity
  have hW0 := Wm_nonneg R χ t m₁ m₂ m₃ v₁ v₂
  have hC0 := CJ_nonneg 0
  have hd0 : (0 : ℝ) ≤ q.divisors.card := Nat.cast_nonneg _
  rw [hPsi, norm_mul]
  -- the termwise bound of `S`
  have hSle : ‖S‖ ≤ ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ,
      ‖Cq q ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q))‖ *
        (‖Rf R χ t v₁ b₁‖ * ‖Rf R χ t (v₂ / v₁) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q)‖ *
          ‖Rf R χ t (1 / v₂) ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q)‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₁ _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun b₂ _ => ?_))
    rw [norm_mul, norm_mul, norm_mul]
  split_ifs with hreg
  · -- inside: `|J| ≤ C₀` and `|C_q| ≤ d(q)(·, q)`
    have hJ : ‖Jk v₁ v₂ lam‖ ≤ CJ 0 := by simpa using CJ_spec 0 ha₁ ha₂ lam
    have hS2 : ‖S‖ ≤ q.divisors.card * Wm R χ t m₁ m₂ m₃ v₁ v₂ := by
      refine hSle.trans ?_
      unfold Wm
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b₂ _ => ?_
      have hc := norm_Cq_le q ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q))
      calc _ ≤ ((q.divisors.card : ℝ) *
            (Nat.gcd ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)).val q : ℝ)) *
            (‖Rf R χ t v₁ b₁‖ * ‖Rf R χ t (v₂ / v₁) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q)‖ *
              ‖Rf R χ t (1 / v₂) ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q)‖) := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by ring
    calc ‖Jk v₁ v₂ lam‖ * ‖S‖ ≤ CJ 0 * (q.divisors.card * Wm R χ t m₁ m₂ m₃ v₁ v₂) :=
          mul_le_mul hJ hS2 (norm_nonneg _) hC0
      _ ≤ _ := by nlinarith
  · -- outside: `|J| ≤ C_K(2πX)^{−K}` and the trivial bounds
    have hlamX : X < |lam| := by
      rw [hlam', abs_mul, abs_of_pos (div_pos hN hq)]
      rw [not_le] at hreg
      calc X = N / q * (X * q / N) := by field_simp
        _ < N / q * |m₁ * v₁ + m₂ * v₂ + m₃| := mul_lt_mul_of_pos_left hreg (div_pos hN hq)
    have hJ : ‖Jk v₁ v₂ lam‖ ≤ CJ K / (2 * π * X) ^ K := by
      have hspec := CJ_spec K ha₁ ha₂ lam
      have hXp : 0 < (2 * π * X) ^ K := by positivity
      rw [le_div_iff₀ hXp]
      calc ‖Jk v₁ v₂ lam‖ * (2 * π * X) ^ K ≤ ‖Jk v₁ v₂ lam‖ * (2 * π * |lam|) ^ K := by
            refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ K) (norm_nonneg _)
            have := Real.pi_pos; nlinarith
        _ ≤ CJ K := by linarith
    have hS2 : ‖S‖ ≤ (q.totient : ℝ) ^ 3 * (R.card : ℝ) ^ 3 := by
      refine hSle.trans ?_
      have hb : ∀ b₁ b₂ : (ZMod q)ˣ,
          ‖Cq q ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q))‖ *
            (‖Rf R χ t v₁ b₁‖ * ‖Rf R χ t (v₂ / v₁) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q)‖ *
              ‖Rf R χ t (1 / v₂) ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q)‖) ≤ q.totient * (R.card : ℝ) ^ 3 := by
        intro b₁ b₂
        have r1 := norm_Rf_le R χ t hv₁ (b₁ : ZMod q)
        have r2 := norm_Rf_le R χ t (div_pos hv₂ hv₁) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q)
        have r3 := norm_Rf_le R χ t (one_div_pos.2 hv₂) ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q)
        have hc := norm_Cq_le_totient q
          ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q))
        have hR : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
        calc _ ≤ (q.totient : ℝ) * ((R.card : ℝ) * R.card * R.card) :=
              mul_le_mul hc (mul_le_mul (mul_le_mul r1 r2 (norm_nonneg _) hR) r3 (norm_nonneg _) (by positivity))
                (by positivity) (Nat.cast_nonneg _)
          _ = q.totient * (R.card : ℝ) ^ 3 := by ring
      calc _ ≤ ∑ _b₁ : (ZMod q)ˣ, ∑ _b₂ : (ZMod q)ˣ, (q.totient : ℝ) * (R.card : ℝ) ^ 3 :=
            Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => hb b₁ b₂
        _ = (q.totient : ℝ) ^ 3 * (R.card : ℝ) ^ 3 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card_units_eq_totient]
            ring
    calc ‖Jk v₁ v₂ lam‖ * ‖S‖ ≤ CJ K / (2 * π * X) ^ K * ((q.totient : ℝ) ^ 3 * (R.card : ℝ) ^ 3) :=
          mul_le_mul hJ hS2 (norm_nonneg _) (by have := CJ_nonneg K; positivity)
      _ = _ := by ring

/-- `Ψ = 0` off `[1/2, 2]²`. -/
lemma Psi_eq_zero {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) (m₁ m₂ m₃ : ℤ) {v₁ v₂ : ℝ} (h : v₁ ∉ Icc (1 / 2 : ℝ) 2 ∨ v₂ ∉ Icc (1 / 2 : ℝ) 2) :
    Psi N R χ t m₁ m₂ m₃ v₁ v₂ = 0 := by
  have h' : v₁ ∉ Ioo (1 / 2 : ℝ) 2 ∨ v₂ ∉ Ioo (1 / 2 : ℝ) 2 := by
    rcases h with h | h
    · exact Or.inl fun h0 => h (Ioo_subset_Icc_self h0)
    · exact Or.inr fun h0 => h (Ioo_subset_Icc_self h0)
  unfold Psi
  rw [Jk_eq_zero_of h', zero_mul]

/-- **Their Proposition 7.1** at one point per character, with explicit constants: for `N > 0`, `X > 0` and every
`K`, `|I′(m⃗)| ≤ (N/q)³(C₀d(q)∫∫_{[1/2,2]²}W·[|m₁v₁ + m₂v₂ + m₃| ≤ Xq/N] + (9/4)C_K(2πX)^{−K}φ(q)³|R|³)`. -/
theorem prop71 {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (m₁ m₂ m₃ : ℤ) {X : ℝ} (hX : 0 < X) (K : ℕ) :
    ‖Ip N R χ t m₁ m₂ m₃‖ ≤ (N / q) ^ 3 * (CJ 0 * q.divisors.card *
      (∫ v₁ in Icc (1 / 2 : ℝ) 2, ∫ v₂ in Icc (1 / 2 : ℝ) 2,
        (if |m₁ * v₁ + m₂ * v₂ + m₃| ≤ X * q / N then Wm R χ t m₁ m₂ m₃ v₁ v₂ else 0)) +
      9 / 4 * (CJ K / (2 * π * X) ^ K * ((q.totient : ℝ) ^ 3 * (R.card : ℝ) ^ 3))) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set c₀ : ℝ := CJ 0 * q.divisors.card with hc₀
  set E : ℝ := CJ K / (2 * π * X) ^ K * ((q.totient : ℝ) ^ 3 * (R.card : ℝ) ^ 3) with hE
  set V : ℝ → ℝ → ℝ := fun v₁ v₂ =>
    if |m₁ * v₁ + m₂ * v₂ + m₃| ≤ X * q / N then Wm R χ t m₁ m₂ m₃ v₁ v₂ else 0 with hV
  have hc₀0 : 0 ≤ c₀ := mul_nonneg (CJ_nonneg 0) (Nat.cast_nonneg _)
  have hE0 : 0 ≤ E := by have := CJ_nonneg K; positivity
  have hV0 : ∀ v₁ v₂, 0 ≤ V v₁ v₂ := fun v₁ v₂ => by
    simp only [hV]; split_ifs
    · exact Wm_nonneg R χ t m₁ m₂ m₃ v₁ v₂
    · exact le_rfl
  have hVm : Measurable fun p : ℝ × ℝ => V p.1 p.2 := by
    simp only [hV]
    refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (measurable_Wm R χ t m₁ m₂ m₃)
      measurable_const
  set M : ℝ := (q.totient : ℝ) ^ 2 * (q * (R.card : ℝ) ^ 3) with hM
  have hVle : ∀ v₁ ∈ Icc (1 / 2 : ℝ) 2, ∀ v₂ ∈ Icc (1 / 2 : ℝ) 2, V v₁ v₂ ≤ M := by
    intro v₁ h1 v₂ h2
    simp only [hV]; split_ifs
    · exact Wm_le R χ t m₁ m₂ m₃ (by linarith [h1.1]) (by linarith [h2.1])
    · positivity
  have hM0 : 0 ≤ M := by positivity
  -- (I1) integrability in `v₂`
  have hI1 : ∀ v₁ ∈ Icc (1 / 2 : ℝ) 2, IntegrableOn (fun v₂ => V v₁ v₂) (Icc (1 / 2 : ℝ) 2) := by
    intro v₁ h1
    refine Integrable.mono' (integrableOn_const (C := M) (by simp)) ?_ ?_
    · exact (hVm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun v₂ h2 => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hV0 v₁ v₂)]
      exact hVle v₁ h1 v₂ h2
  -- (I2) integrability in `v₁`
  have hI2 : IntegrableOn (fun v₁ => ∫ v₂ in Icc (1 / 2 : ℝ) 2, V v₁ v₂) (Icc (1 / 2 : ℝ) 2) := by
    refine Integrable.mono' (integrableOn_const (C := 3 / 2 * M) (by simp)) ?_ ?_
    · exact (hVm.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Icc (1 / 2 : ℝ) 2))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun v₁ h1 => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Icc fun v₂ _ => hV0 v₁ v₂)]
      calc ∫ v₂ in Icc (1 / 2 : ℝ) 2, V v₁ v₂ ≤ ∫ _ in Icc (1 / 2 : ℝ) 2, M :=
            setIntegral_mono_on (hI1 v₁ h1) (integrableOn_const (by simp)) measurableSet_Icc
              fun v₂ h2 => hVle v₁ h1 v₂ h2
        _ = 3 / 2 * M := by
            rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by norm_num)]; ring
  -- the inner bound
  have hinner : ∀ v₁ ∈ Icc (1 / 2 : ℝ) 2,
      ‖∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂‖ ≤ c₀ * (∫ v₂ in Icc (1 / 2 : ℝ) 2, V v₁ v₂) + 3 / 2 * E := by
    intro v₁ h1
    have e : ∫ v₂ in Icc (1 / 2 : ℝ) 2, Psi N R χ t m₁ m₂ m₃ v₁ v₂ = ∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun v₂ hv₂ => Psi_eq_zero N R χ t m₁ m₂ m₃ (Or.inr hv₂)
    rw [← e]
    have hint : IntegrableOn (fun v₂ => c₀ * V v₁ v₂ + E) (Icc (1 / 2 : ℝ) 2) :=
      ((hI1 v₁ h1).const_mul c₀).add (integrableOn_const (by simp))
    refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun v₂ h2 => ?_))).trans (le_of_eq ?_)
    · exact norm_Psi_le hN R χ t m₁ m₂ m₃ hX K h1 h2
    · rw [integral_add ((hI1 v₁ h1).const_mul c₀) (integrableOn_const (by simp)), integral_const_mul,
        setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by norm_num)]
      ring
  -- assembly
  rw [Ip_eq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_pos hN hq).le]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e1 : ∫ v₁ in Icc (1 / 2 : ℝ) 2, ‖∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂‖ =
      ∫ v₁ : ℝ, ‖∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun v₁ hv₁ => by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun v₂ => Psi_eq_zero N R χ t m₁ m₂ m₃ (Or.inl hv₁)),
        integral_zero, norm_zero]
  calc ‖∫ v₁ : ℝ, ∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂‖
      ≤ ∫ v₁ : ℝ, ‖∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂‖ := norm_integral_le_integral_norm _
    _ = ∫ v₁ in Icc (1 / 2 : ℝ) 2, ‖∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂‖ := e1.symm
    _ ≤ ∫ v₁ in Icc (1 / 2 : ℝ) 2, (c₀ * (∫ v₂ in Icc (1 / 2 : ℝ) 2, V v₁ v₂) + 3 / 2 * E) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          ((hI2.const_mul c₀).add (integrableOn_const (by simp)))
          ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hinner))
    _ = c₀ * (∫ v₁ in Icc (1 / 2 : ℝ) 2, ∫ v₂ in Icc (1 / 2 : ℝ) 2, V v₁ v₂) + 9 / 4 * E := by
        rw [integral_add (hI2.const_mul c₀) (integrableOn_const (by simp)), integral_const_mul, setIntegral_const,
          smul_eq_mul, Real.volume_real_Icc_of_le (by norm_num)]
        ring

end LinnikCGLP71

#print axioms LinnikCGLP71.norm_Psi_le
#print axioms LinnikCGLP71.prop71
