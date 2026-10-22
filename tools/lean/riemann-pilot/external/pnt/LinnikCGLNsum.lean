/-
# Round 682: `ĝ_a` as a sum over `m₁` and `n`, and the sum over `a` for every `n ≠ 0` (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li continue the proof of their Lemma 8.2 with (8.2), `ĝ_a(ξ)` as sums over `b`, `m₁`, `m₂`, `d` and `n`
(lines 2804–2833), and "We separate the terms on the right-hand side of (8.2) where q∤n to define ĝ_{a,1}(ξ) and
define ĝ_{a,2}(ξ) using the remaining terms." (lines 2834–2835; spaces restored, the hats and subscripts transcribed).
This file writes round 680's `fourier_ga_poisson` as a sum over `m₁` and `n`, splits off the term `n = 0`, and passes
round 681's `sum_a_finite_le` from finite sets of `n` to every `n ≠ 0`.

The stack's form.
* `ĝ_a(ξ) = Σ_{m₁∈P1 M₁}Σ_{n∈ℤ}(L/q)Ψ(m₁, n)c_q(n)F(m₁, n)e_q(−anm₁)`, with their inner sums over `b` and `m₂` in
  `F(m₁, n) = Σ_bΣ_{m₂∈P2 M₂}(m₂/|m₁|)f̂_b(m₂ξ/m₁)e_q(−nbm₂)` (`Fb`), by `e_q(−n(am₁ + bm₂)) = e_q(−anm₁)e_q(−nbm₂)`.
* Their restriction of `n` to `|ξ − nm₁/q| ⪅ M₁/M₃`, with its error `O((qT)^{−103})`, is not made: every `n` is kept.
* The split is `n = 0` against `n ≠ 0`, not their `q ∤ n` against `q | n`: round 681's `sum_a_finite_le` holds for
  every `n ≠ 0`.
* The sum over `a` passes from finite sets of `n` to all of them by the limit over finite sets (`sum_norm_sq_tsum_le`).

Plain statements, with `q ≥ 1` (`[NeZero q]`), `Ψ(m₁, n) = ψ̂₀(L(n/q − ξ/m₁))` (round 659's `𝓕 psiC`), `c_q(n)` round
680's `cqg` and `e_q` Mathlib's `ZMod.stdAddChar`.
* `Fb`, `norm_Fb_le`: `F(m₁, n)` as above, and `|F(m₁, n)| ≤ Σ_bΣ_{m₂}|(m₂/|m₁|)f̂_b(m₂ξ/m₁)|`.
* `tg`, `summable_tg`: the term `(L/q)Ψ(m₁, n)c_q(n)F(m₁, n)e_q(−anm₁)`, and for `L > 0` its series over `n ∈ ℤ`
  converges.
* `fourier_ga_eq`, `fourier_ga_split`: for smooth `f_b` that are `0` for `|u| > A`, `M₁ > 0` and `L > 0`,
  `ĝ_a(ξ) = Σ_{m₁}Σ_n tg(a, m₁, n) = Σ_{m₁}tg(a, m₁, 0) + Σ_{m₁}Σ_{n≠0}tg(a, m₁, n)`.
* `sum_ite_zero`: `Σ_{n∈T}[n ≠ 0]G(n) = Σ_{n∈T, n≠0}G(n)`.
* `sum_norm_sq_tsum_le`: for `a` in a finite type and a finite set `P` of integers, if
  `Σ_a|Σ_{m∈P}Σ_{n∈T}t_a(m, n)|² ≤ KΣ_{m∈P}Σ_{n∈T}r(m, n)` for every finite set `T` of integers, with `K ≥ 0`, `r ≥ 0`
  and the series `Σ_nt_a(m, n)` and `Σ_nr(m, n)` convergent, the same holds with the sums over `n ∈ ℤ`.
* `sum_a_le`: for `L > 0`, `M₁ > 0`, `0 < δ ≤ 1`, real `ξ` and coefficients `F(m, n)` bounded in `n` for each `m`,
  `Σ_a|Σ_{m∈P1 M₁}Σ_{n≠0}(L/q)Ψ(m, n)c_q(n)F(m, n)e_q(−anm)|² ≤
  d(q)(L/q)²(Σ_h(h, q))²N_δΣ_{m∈P1 M₁}Σ_{n≠0}|Ψ(m, n)||F(m, n)|²`, with `N_δ` the bound of round 681's `count_le`.
* `sum_a_fourier_ga_le`: for smooth `f_b` that are `0` for `|u| > A`, `M₁ > 0`, `L > 0`, `0 < δ ≤ 1` and real `ξ`,
  `Σ_a|ĝ_a(ξ) − Σ_{m₁}tg(a, m₁, 0)|² ≤ d(q)(L/q)²(Σ_h(h, q))²N_δΣ_{m₁∈P1 M₁}Σ_{n≠0}|Ψ(m₁, n)||F(m₁, n)|²`.

The file imports `LinnikCGLAsum.lean`.
-/

import LinnikCGLAsum

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLNsum

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLSep LinnikCGLRFact LinnikCGLRam LinnikCGLJ LinnikCGLG
  LinnikCGLPois8 LinnikCGLCount LinnikCGLAsum

/-! ### The terms -/

/-- Their inner sums over `b` and `m₂`: `F(m₁, n) = Σ_bΣ_{m₂∈P2 M₂}(m₂/|m₁|)f̂_b(m₂ξ/m₁)e_q(−nbm₂)`. -/
def Fb {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (M₂ ξ : ℝ) (m₁ n : ℤ) : ℂ :=
  ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, (((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * 𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁) *
    ZMod.stdAddChar (-((n : ZMod q) * ((b : ZMod q) * (m₂ : ZMod q))))

/-- For `q ≥ 1`, `|F(m₁, n)| ≤ Σ_bΣ_{m₂}|(m₂/|m₁|)f̂_b(m₂ξ/m₁)|`, a bound independent of `n`. -/
lemma norm_Fb_le {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (M₂ ξ : ℝ) (m₁ n : ℤ) :
    ‖Fb f M₂ ξ m₁ n‖ ≤ ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂,
      ‖(((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * 𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁)‖ := by
  unfold Fb
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans (le_of_eq ?_))
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [norm_mul, norm_stdAddChar, mul_one]

/-- The term `(L/q)Ψ(m₁, n)c_q(n)F(m₁, n)e_q(−anm₁)`, with `Ψ(m₁, n) = ψ̂₀(L(n/q − ξ/m₁))`. -/
def tg {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (M₂ L ξ : ℝ) (a : (ZMod q)ˣ) (m₁ n : ℤ) : ℂ :=
  ((L / q : ℝ) : ℂ) * 𝓕 psiC (L * (n / q - ξ / m₁)) * cqg q n * Fb f M₂ ξ m₁ n *
    ZMod.stdAddChar (-((a : ZMod q) * ((n : ZMod q) * (m₁ : ZMod q))))

/-- For `q ≥ 1` and `L > 0`, the series `Σ_{n∈ℤ}(L/q)Ψ(m₁, n)c_q(n)F(m₁, n)e_q(−anm₁)` converges. -/
lemma summable_tg {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (M₂ : ℝ) {L : ℝ} (hL : 0 < L) (ξ : ℝ)
    (a : (ZMod q)ˣ) (m₁ : ℤ) : Summable fun n : ℤ => tg f M₂ L ξ a m₁ n := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hG : 0 ≤ ∑ h : ZMod q, gw h := Finset.sum_nonneg fun h _ => gw_nonneg h
  have hw : ∀ n : ℤ, ‖((L / q : ℝ) : ℂ) * cqg q n * Fb f M₂ ξ m₁ n *
      ZMod.stdAddChar (-((a : ZMod q) * ((n : ZMod q) * (m₁ : ZMod q))))‖ ≤
      L / q * ((∑ h : ZMod q, gw h) * ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂,
        ‖(((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * 𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁)‖) := by
    intro n
    rw [norm_mul, norm_mul, norm_mul, norm_stdAddChar, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    calc _ = L / q * (‖cqg q n‖ * ‖Fb f M₂ ξ m₁ n‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul (norm_cqg_le _) (norm_Fb_le f M₂ ξ m₁ n) (norm_nonneg _) hG)
          (by positivity)
  refine (summable_psiC_lattice hL hq (ξ / m₁) _ hw).congr fun n => ?_
  unfold tg
  ring

/-! ### `ĝ_a` as a sum over `m₁` and `n` -/

/-- **`ĝ_a` as a sum over `m₁` and `n`**: for `q ≥ 1`, smooth `f_b` that are `0` for `|u| > A`, `M₁ > 0` and `L > 0`,
`ĝ_a(ξ) = Σ_{m₁∈P1 M₁}Σ_{n∈ℤ}(L/q)Ψ(m₁, n)c_q(n)F(m₁, n)e_q(−anm₁)`. -/
theorem fourier_ga_eq {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ L : ℝ} (hM₁ : 0 < M₁) (hL : 0 < L) (a : (ZMod q)ˣ) (ξ : ℝ) :
    𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ = ∑ m₁ ∈ P1 M₁, ∑' n : ℤ, tg f M₂ L ξ a m₁ n := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [fourier_ga_poisson hfs hA hM₁ hL a ξ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  have hs : ∀ (b : (ZMod q)ˣ) (m₂ : ℤ), Summable fun n : ℤ => ((L / q : ℝ) : ℂ) * 𝓕 psiC (L * (n / q - ξ / m₁)) *
      (ZMod.stdAddChar (-((n : ZMod q) * ((a : ZMod q) * (m₁ : ZMod q) + (b : ZMod q) * (m₂ : ZMod q)))) *
        cqg q n) := by
    intro b m₂
    have hw : ∀ n : ℤ, ‖((L / q : ℝ) : ℂ) *
        (ZMod.stdAddChar (-((n : ZMod q) * ((a : ZMod q) * (m₁ : ZMod q) + (b : ZMod q) * (m₂ : ZMod q)))) *
          cqg q n)‖ ≤ L / q * ∑ h : ZMod q, gw h := by
      intro n
      rw [norm_mul, norm_mul, norm_stdAddChar, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (norm_cqg_le _) (by positivity)
    refine (summable_psiC_lattice hL hq (ξ / m₁) _ hw).congr fun n => ?_
    ring
  have key : ∀ n : ℤ, tg f M₂ L ξ a m₁ n = ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂,
      (((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * 𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁) *
        (((L / q : ℝ) : ℂ) * 𝓕 psiC (L * (n / q - ξ / m₁)) *
          (ZMod.stdAddChar (-((n : ZMod q) * ((a : ZMod q) * (m₁ : ZMod q) + (b : ZMod q) * (m₂ : ZMod q)))) *
            cqg q n)) := by
    intro n
    unfold tg Fb
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    have hχ : ZMod.stdAddChar (-((n : ZMod q) * ((a : ZMod q) * (m₁ : ZMod q) + (b : ZMod q) * (m₂ : ZMod q)))) =
        ZMod.stdAddChar (-((a : ZMod q) * ((n : ZMod q) * (m₁ : ZMod q)))) *
          ZMod.stdAddChar (-((n : ZMod q) * ((b : ZMod q) * (m₂ : ZMod q)))) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [hχ]
    ring
  symm
  refine HasSum.tsum_eq ?_
  convert hasSum_sum (s := Finset.univ) fun b _ => hasSum_sum (s := P2 M₂) fun m₂ _ =>
    (hs b m₂).hasSum.mul_left ((((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * 𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁)) using 1
  funext n
  exact key n

/-- **The term `n = 0` split off**: for `q ≥ 1`, smooth `f_b` that are `0` for `|u| > A`, `M₁ > 0` and `L > 0`,
`ĝ_a(ξ) = Σ_{m₁}tg(a, m₁, 0) + Σ_{m₁}Σ_{n≠0}tg(a, m₁, n)`. -/
theorem fourier_ga_split {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ L : ℝ} (hM₁ : 0 < M₁) (hL : 0 < L) (a : (ZMod q)ˣ) (ξ : ℝ) :
    𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ = ∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0 +
      ∑ m₁ ∈ P1 M₁, ∑' n : ℤ, if n = 0 then 0 else tg f M₂ L ξ a m₁ n := by
  rw [fourier_ga_eq hfs hA hM₁ hL a ξ, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m₁ _ => (summable_tg f M₂ hL ξ a m₁).tsum_eq_add_tsum_ite 0

/-! ### The limit over finite sets of `n` -/

/-- `Σ_{n∈T}[n ≠ 0]G(n) = Σ_{n∈T, n≠0}G(n)`. -/
lemma sum_ite_zero {M : Type*} [AddCommMonoid M] (T : Finset ℤ) (G : ℤ → M) :
    ∑ n ∈ T, (if n = 0 then 0 else G n) = ∑ n ∈ T.filter (· ≠ 0), G n := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : n = 0 <;> simp [h]

/-- **The limit over finite sets**: for `a` in a finite type and a finite set `P` of integers, if
`Σ_a|Σ_{m∈P}Σ_{n∈T}t_a(m, n)|² ≤ KΣ_{m∈P}Σ_{n∈T}r(m, n)` for every finite set `T` of integers, with `K ≥ 0`, `r ≥ 0`
and the series `Σ_nt_a(m, n)` and `Σ_nr(m, n)` convergent, then
`Σ_a|Σ_{m∈P}Σ_{n∈ℤ}t_a(m, n)|² ≤ KΣ_{m∈P}Σ_{n∈ℤ}r(m, n)`. -/
lemma sum_norm_sq_tsum_le {α : Type*} [Fintype α] (P : Finset ℤ) (t : α → ℤ → ℤ → ℂ) (r : ℤ → ℤ → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (ht : ∀ a m, Summable (t a m)) (hr : ∀ m, Summable (r m)) (hr0 : ∀ m n, 0 ≤ r m n)
    (hfin : ∀ T : Finset ℤ, ∑ a, ‖∑ m ∈ P, ∑ n ∈ T, t a m n‖ ^ 2 ≤ K * ∑ m ∈ P, ∑ n ∈ T, r m n) :
    ∑ a, ‖∑ m ∈ P, ∑' n, t a m n‖ ^ 2 ≤ K * ∑ m ∈ P, ∑' n, r m n := by
  have hlim : Tendsto (fun T : Finset ℤ => ∑ a, ‖∑ m ∈ P, ∑ n ∈ T, t a m n‖ ^ 2) atTop
      (𝓝 (∑ a, ‖∑ m ∈ P, ∑' n, t a m n‖ ^ 2)) :=
    tendsto_finsetSum _ fun a _ => ((tendsto_finsetSum _ fun m _ => (ht a m).hasSum).norm).pow 2
  refine le_of_tendsto' hlim fun T => (hfin T).trans ?_
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => (hr m).sum_le_tsum T fun n _ => hr0 m n) hK

/-- **The sum over `a`, for every `n ≠ 0`**: for `q ≥ 1`, `L > 0`, `M₁ > 0`, `0 < δ ≤ 1`, real `ξ` and coefficients
`F(m, n)` bounded in `n` for each `m`, `Σ_a|Σ_{m∈P1 M₁}Σ_{n≠0}(L/q)Ψ(m, n)c_q(n)F(m, n)e_q(−anm)|² ≤
d(q)(L/q)²(Σ_h(h, q))²N_δΣ_{m∈P1 M₁}Σ_{n≠0}|Ψ(m, n)||F(m, n)|²`, with `N_δ` the bound of round 681's `count_le`. -/
theorem sum_a_le {q : ℕ} [NeZero q] {L M₁ δ : ℝ} (hL : 0 < L) (hM₁ : 0 < M₁) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ξ : ℝ) (F : ℤ → ℤ → ℂ) (hF : ∀ m, ∃ B, ∀ n, ‖F m n‖ ≤ B) :
    ∑ a : (ZMod q)ˣ, ‖∑ m ∈ P1 M₁, ∑' n : ℤ, (if n = 0 then 0 else ((L / q : ℝ) : ℂ) *
        𝓕 psiC (L * (n / q - ξ / m)) * cqg q n * F m n *
          ZMod.stdAddChar (-((a : ZMod q) * ((n : ZMod q) * (m : ZMod q)))))‖ ^ 2 ≤
      (q.divisors.card : ℝ) * (L / q) ^ 2 * (∑ h : ZMod q, gw h) ^ 2 *
        (4 * LinnikPower.Cdiv δ * B4 * (1 + q * |ξ|) ^ δ * (1 + 2 * q * M₁ / L) ^ δ * (∑ h : ZMod q, gw h) *
          (2 * π + 8 * π * M₁ / L)) *
        ∑ m ∈ P1 M₁, ∑' n : ℤ, (if n = 0 then 0 else ‖𝓕 psiC (L * (n / q - ξ / m))‖ * ‖F m n‖ ^ 2) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hG : 0 ≤ ∑ h : ZMod q, gw h := Finset.sum_nonneg fun h _ => gw_nonneg h
  have hC : 0 ≤ LinnikPower.Cdiv δ := le_trans zero_le_one (LinnikPower.one_le_Cdiv hδ hδ1)
  have hB4 := B4_nonneg
  refine sum_norm_sq_tsum_le (P1 M₁) (fun (a : (ZMod q)ˣ) (m n : ℤ) => if n = 0 then 0 else ((L / q : ℝ) : ℂ) *
      𝓕 psiC (L * (n / q - ξ / m)) * cqg q n * F m n *
        ZMod.stdAddChar (-((a : ZMod q) * ((n : ZMod q) * (m : ZMod q)))))
    (fun (m n : ℤ) => if n = 0 then 0 else ‖𝓕 psiC (L * (n / q - ξ / m))‖ * ‖F m n‖ ^ 2) (by positivity) ?_ ?_ ?_ ?_
  · intro a m
    obtain ⟨B, hB⟩ := hF m
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
    have hw : ∀ n : ℤ, ‖(if n = 0 then 0 else ((L / q : ℝ) : ℂ) * cqg q n * F m n *
        ZMod.stdAddChar (-((a : ZMod q) * ((n : ZMod q) * (m : ZMod q)))))‖ ≤
        L / q * ((∑ h : ZMod q, gw h) * B) := by
      intro n
      split_ifs
      · rw [norm_zero]; positivity
      · rw [norm_mul, norm_mul, norm_mul, norm_stdAddChar, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        calc _ = L / q * (‖cqg q n‖ * ‖F m n‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul (norm_cqg_le _) (hB n) (norm_nonneg _) hG) (by positivity)
    refine (summable_psiC_lattice hL hq (ξ / m) _ hw).congr fun n => ?_
    split_ifs <;> ring
  · intro m
    obtain ⟨B, hB⟩ := hF m
    have hΨ : Summable fun n : ℤ => ‖𝓕 psiC (L * (n / q - ξ / m))‖ :=
      summable_norm_iff.mpr ((summable_psiC_lattice hL hq (ξ / m) (fun _ => 1) (B := 1) fun _ => by simp).congr
        fun n => one_mul _)
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hΨ.mul_left (B ^ 2))
    · split_ifs
      · exact le_refl 0
      · positivity
    · split_ifs
      · positivity
      · calc ‖𝓕 psiC (L * (n / q - ξ / m))‖ * ‖F m n‖ ^ 2 ≤ ‖𝓕 psiC (L * (n / q - ξ / m))‖ * B ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hB n) 2) (norm_nonneg _)
          _ = B ^ 2 * ‖𝓕 psiC (L * (n / q - ξ / m))‖ := by ring
  · intro m n
    split_ifs
    · exact le_refl 0
    · positivity
  · intro T
    simpa only [sum_ite_zero] using sum_a_finite_le (q := q) hL hM₁ hδ hδ1 ξ T F

/-- **`ĝ_a` without its term `n = 0`**: for `q ≥ 1`, smooth `f_b` that are `0` for `|u| > A`, `M₁ > 0`, `L > 0`,
`0 < δ ≤ 1` and real `ξ`, `Σ_a|ĝ_a(ξ) − Σ_{m₁}tg(a, m₁, 0)|² ≤
d(q)(L/q)²(Σ_h(h, q))²N_δΣ_{m₁∈P1 M₁}Σ_{n≠0}|Ψ(m₁, n)||F(m₁, n)|²`, with `N_δ` the bound of round 681's
`count_le`. -/
theorem sum_a_fourier_ga_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ L δ : ℝ} (hM₁ : 0 < M₁) (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ξ : ℝ) :
    ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ - ∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 ≤
      (q.divisors.card : ℝ) * (L / q) ^ 2 * (∑ h : ZMod q, gw h) ^ 2 *
        (4 * LinnikPower.Cdiv δ * B4 * (1 + q * |ξ|) ^ δ * (1 + 2 * q * M₁ / L) ^ δ * (∑ h : ZMod q, gw h) *
          (2 * π + 8 * π * M₁ / L)) *
        ∑ m₁ ∈ P1 M₁, ∑' n : ℤ,
          (if n = 0 then 0 else ‖𝓕 psiC (L * (n / q - ξ / m₁))‖ * ‖Fb f M₂ ξ m₁ n‖ ^ 2) := by
  have e : ∀ a : (ZMod q)ˣ, 𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ - ∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0 =
      ∑ m₁ ∈ P1 M₁, ∑' n : ℤ, if n = 0 then 0 else tg f M₂ L ξ a m₁ n := by
    intro a
    rw [fourier_ga_split hfs hA hM₁ hL a ξ, add_sub_cancel_left]
  simp_rw [e]
  exact sum_a_le hL hM₁ hδ hδ1 ξ (Fb f M₂ ξ) fun m => ⟨_, norm_Fb_le f M₂ ξ m⟩

end LinnikCGLNsum

#print axioms LinnikCGLNsum.summable_tg
#print axioms LinnikCGLNsum.fourier_ga_eq
#print axioms LinnikCGLNsum.fourier_ga_split
#print axioms LinnikCGLNsum.sum_norm_sq_tsum_le
#print axioms LinnikCGLNsum.sum_a_le
#print axioms LinnikCGLNsum.sum_a_fourier_ga_le
