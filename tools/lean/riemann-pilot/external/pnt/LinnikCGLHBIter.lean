/-
# Round 699: Kerr's iteration with characters (the CGL plan's stage M5)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Kerr's §6 proves his Theorem 16 (arXiv:1909.12075) from three bounds for his double sums: the reflection (his
Corollary 28, round 698), the squaring (his Lemma 22, round 694's `shat_sq_le`) and the lengthening (his Corollary 21,
from his Lemma 20; round 696's `sig_le_lengthen`). This file runs his argument with characters for round 694's `σ(N)`,
the double sum over `N < n ≤ 2N`, against `B(N) = RN + R² + R^{5/4}Q^{1/2}`, with `R` the number of points and
`Q = q(1 + 2T)`.

The stack's form.
* Kerr's first case closes at one length, `S(N) ≪ I^{1/2}S(N)^{1/2} + …` (his (45)), since his Corollary 21 lengthens
  to exactly `N`. Round 696's lengthening bounds `σ(N)` by `σ(NU) + σ(2NU)`, two lengths, so the iteration here runs
  through the supremum `s` of `σ(N)/B(N)` over `N > 0` (`sup_arg`), finite by the trivial bound (`sig_le_triv`): one
  step shows `s ≤ a√s + b`, whence `s ≤ a² + 2b`.
* Case A, `N ≥ min(N*, Q^{1+δ})` with `N* = Q^{1/2+δ}R^{1/4}`: round 698's reflection at `Z = ⌈Q^{1+δ}/N⌉`, where
  `NZ ≥ Q^{1+δ}` makes the tail small for `Kδ ≥ 1`, then the squaring `Ŝ(Z)² ≤ R²D²Ŝ(Z²)`, the dyadic pieces of
  `[1, Z²]` (round 694's `shat_le_sum_sig`) and the bound `σ ≤ sB` on them; `Z − 1 ≤ Q^{1/2}R^{−1/4}` gives
  `R²B(Z²) ≤ 3B(N)²` (`Bd_sq_le`).
* Case B, `1/2 ≤ N < min(N*, Q^{1+δ})`: the lengthening with `U = max(min(N*, Q^{1+δ})/N, U₀)` reaches Case A at `NU`
  and `2NU`, and `B(2NU) ≤ (2Q^δ + 2U₀ + 1)B(N)` (`Bd_len_le`).
* `σ(N) = 0` for `N < 1/2`. The factors `2^{ω(q)} ≤ d(q)`, `EQh(q) ≤ 4^{ω(q)} ≤ d(q)²` and `Q₀(q) ≤ πC_0d(q)³` keep
  the dependence on `q` explicit.

Plain statements, with `q ≥ 1` where `[NeZero q]`, `R` the number of points and `Q = q(1 + 2T)`.
* `le_of_le_sqrt`, `sup_arg`: for `x ≥ 0` with `x ≤ a√x + b`, `x ≤ a² + 2b`; and if `F ≥ 0`, `B > 0` and `F ≤ s₀B` on
  `N > 0`, and for every `s ≥ 0` the bound `F ≤ sB` there gives `F ≤ (a√s + b)B` there, then `F ≤ (a² + 2b)B` there.
* `dyad_eq_empty`, `sig_eq_zero`, `card_dyad_le`, `norm_famA_le`, `rpow_neg_half_sq`, `sig_le_triv`: for `N < 1/2`,
  `(N, 2N]` holds no integer and `σ(N) = 0`; for `N ≥ 0` it holds at most `N + 1`; for `n ≥ 1`, `|χ_r(n)n^{it_r}| ≤ 1`;
  for `x ≥ 0`, `(x^{−1/2})² = x⁻¹`; and for `N > 0`, `σ(N) ≤ (R + 4)(RN + R²)`.
* `Bd`, `Bd_pos`, `Bd_mono`, `RN_le_Bd`, `Rsq_le_Bd`, `rpow_quarter`: `B(N) = RN + R² + R^{5/4}Q^{1/2}` is positive
  for `R ≥ 1` and `Q, N ≥ 0`, nondecreasing in `N` for `R ≥ 0`, and at least `RN` and `R²` for `R, Q, N ≥ 0`; for
  `R ≥ 0`, `(R^{1/4})⁴ = R` and `(R^{1/4})⁵ = R^{5/4}`.
* `Bd_sq_le`: for `R ≥ 1`, `Q, N ≥ 0`, `Z ≥ 1` and `Z − 1 ≤ Q^{1/2}R^{−1/4}`, `R²B(Z²) ≤ 3B(N)²`.
* `Bd_len_le`: for `R, Q, N, U₀, Qδ ≥ 0` and `M ≤ QδQ^{1/2}R^{1/4} + U₀N`, `B(2M) ≤ (2Qδ + 2U₀ + 1)B(N)`.
* `two_pow_le_card_divisors`, `EQh_le`, `EQh_le_sq`, `Q0_le`: for `n ≠ 0`, `2^{ω(n)} ≤ d(n)`; `EQh(q) ≤ 4^{ω(q)}`; and
  for `q ≠ 0`, `EQh(q) ≤ d(q)²` and `Q₀(q) ≤ πC_0d(q)³`.
* `ctail`, `ctail_nonneg`, `TT_nonneg`, `TT_le`: with `c_K = 2πC_KI_K ≥ 0`, round 698's `T_K(N, Z, T) ≥ 0` for
  `N, T ≥ 0`, and for `q ≠ 0`, `T ≥ 0`, `Kδ ≥ 1` and `NZ ≥ Q^{1+δ}`, `T_K(N, Z, T) ≤ c_Kd(q)³`.
* `Qq`, `Jm`, `U0`, `Nst`, `Lm`, `A1`, `B1`, `MB`, `one_le_Qq`, `one_le_card_divisors`: the parameters `Q`,
  `J = log₂⌊4Q⌋`, `U₀ = 12d(q)² + 4`, `N* = Q^{1/2+δ}R^{1/4}`, `L = 4(1 + U₀)Q^{1+δ}`, `A₁ = C(1 + 2c_K²d(q)⁶)`,
  `B₁ = 2CQ₀(q)²D(J + 1)` and `M_B = 36d(q)D²(2Q^δ + 2U₀ + 1)`; for `T ≥ 0`, `Q ≥ 1`; and `d(q) ≥ 1`.
* `caseA`, `caseB`, `step`: the two cases and their union, for `R ≥ 1` and `T ≥ 1`, with round 698's reflected bound
  at `K` and its constant `C ≥ 0` and `Kδ ≥ 1` in Case A, `0 < δ` in Case B, and `D ≥ 0` bounding `d(m)` on `1 ≤ m ≤ L`
  (on `1 ≤ m ≤ 4Q` in Case A): if `σ ≤ sB` on `N > 0` with `s ≥ 0`, then `σ(N) ≤ (A₁ + B₁√s)B(N)` in Case A,
  `σ(N) ≤ M_BFB(N)` in Case B for `F ≥ 0` a bound of Case A, and `σ(N) ≤ (M_BB₁√s + M_BA₁)B(N)` for every `N > 0`.
* `sig_le_iter`, `sig_bound`: for `T ≥ 1`, `0 < δ`, `Kδ ≥ 1`, `C, D ≥ 0` as above, `σ(N) ≤ ((M_BB₁)² + 2M_BA₁)B(N)`
  for every `N > 0`; and for `0 < δ` there is `C ≥ 0` such that this holds, with `K = ⌈1/δ⌉`, for every `q ≥ 1`,
  `T ≥ 1`, points with `|t_r| ≤ T` and the points with the same character `1`-separated, and `D ≥ 0` as above.

The file imports `LinnikCGLHBRefl.lean` and `LinnikCGLHBLen.lean`.
-/

import LinnikCGLHBRefl
import LinnikCGLHBLen

open Complex Set Real Filter Topology MeasureTheory
open scoped ComplexConjugate Classical

noncomputable section

namespace LinnikCGLHBIter

open LinnikCGLMat LinnikCGLReflect LinnikCGLPair LinnikCGLHBPos LinnikCGLHBLen LinnikCGLHBRefl LinnikCGLT101
  LinnikPower

/-! ### The supremum argument -/

/-- For `x ≥ 0` with `x ≤ a√x + b`, `x ≤ a² + 2b`. -/
lemma le_of_le_sqrt {x a b : ℝ} (hx : 0 ≤ x) (h : x ≤ a * √x + b) : x ≤ a ^ 2 + 2 * b := by
  have h1 : a * √x ≤ (a ^ 2 + x) / 2 := by nlinarith [sq_nonneg (a - √x), Real.sq_sqrt hx]
  linarith

/-- **The supremum argument**: let `F(N) ≥ 0` and `B(N) > 0` for `N > 0`, with `F ≤ s₀B` there. If for every `s ≥ 0`
the bound `F ≤ sB` on `N > 0` gives `F ≤ (a√s + b)B` there, then `F ≤ (a² + 2b)B` on `N > 0`. -/
lemma sup_arg {F B : ℝ → ℝ} (hB : ∀ N, 0 < N → 0 < B N) (hF : ∀ N, 0 < N → 0 ≤ F N) {s₀ a b : ℝ}
    (h0 : ∀ N, 0 < N → F N ≤ s₀ * B N)
    (hstep : ∀ s : ℝ, 0 ≤ s → (∀ N, 0 < N → F N ≤ s * B N) → ∀ N, 0 < N → F N ≤ (a * √s + b) * B N) :
    ∀ N, 0 < N → F N ≤ (a ^ 2 + 2 * b) * B N := by
  set S := (fun N => F N / B N) '' Set.Ioi 0 with hS
  have h1 : (1 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.2 one_pos
  have hne : S.Nonempty := ⟨_, Set.mem_image_of_mem _ h1⟩
  have hbdd : BddAbove S := by
    refine ⟨s₀, ?_⟩
    rintro _ ⟨N, hN, rfl⟩
    exact (div_le_iff₀ (hB N hN)).2 (h0 N hN)
  have hle : ∀ N, 0 < N → F N ≤ sSup S * B N := fun N hN =>
    (div_le_iff₀ (hB N hN)).1 (le_csSup hbdd ⟨N, hN, rfl⟩)
  have hs0 : 0 ≤ sSup S :=
    (div_nonneg (hF 1 one_pos) (hB 1 one_pos).le).trans (le_csSup hbdd ⟨1, h1, rfl⟩)
  have h2 := hstep (sSup S) hs0 hle
  have hss : sSup S ≤ a * √(sSup S) + b := by
    refine csSup_le hne ?_
    rintro _ ⟨N, hN, rfl⟩
    exact (div_le_iff₀ (hB N hN)).2 (h2 N hN)
  have hfin := le_of_le_sqrt hs0 hss
  intro N hN
  exact (hle N hN).trans (mul_le_mul_of_nonneg_right hfin (hB N hN).le)

/-! ### Short lengths and the trivial bound -/

variable {ι : Type*}

/-- For `N < 1/2`, `(N, 2N]` holds no integer. -/
lemma dyad_eq_empty {N : ℝ} (h : N < 1 / 2) : dyad N = ∅ := by
  unfold dyad
  have h1 : ⌊2 * N⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
  rw [h1]
  simp

/-- For `N < 1/2`, `σ(N) = 0`. -/
lemma sig_eq_zero {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {N : ℝ} (h : N < 1 / 2) :
    sig P χ t N = 0 := by
  unfold sig dsum
  rw [dyad_eq_empty h]
  simp

/-- For `N ≥ 0`, `(N, 2N]` holds at most `N + 1` integers. -/
lemma card_dyad_le {N : ℝ} (hN : 0 ≤ N) : ((dyad N).card : ℝ) ≤ N + 1 := by
  unfold dyad
  rw [Nat.card_Ioc]
  have h1 : (⌊2 * N⌋₊ : ℝ) ≤ 2 * N := Nat.floor_le (by positivity)
  have h2 : N < ⌊N⌋₊ + 1 := Nat.lt_floor_add_one N
  have h3 : ⌊N⌋₊ ≤ ⌊2 * N⌋₊ := Nat.floor_le_floor (by linarith)
  rw [Nat.cast_sub h3]
  linarith

/-- For `n ≥ 1`, `|χ_r(n)n^{it_r}| ≤ 1`. -/
lemma norm_famA_le {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (r : ι) {n : ℕ} (hn : 0 < n) :
    ‖famA χ t r n‖ ≤ 1 := by
  unfold famA
  rw [norm_mul, norm_cpow_I hn, mul_one]
  exact (χ r).norm_le_one _

/-- For `x ≥ 0`, `(x^{−1/2})² = x⁻¹`. -/
lemma rpow_neg_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num [Real.rpow_neg_one]

/-- **The trivial bound**: for `N > 0`, `σ(N) ≤ (R + 4)(RN + R²)`. -/
lemma sig_le_triv {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {N : ℝ} (hN : 0 < N) :
    sig P χ t N ≤ ((P.card : ℝ) + 4) * ((P.card : ℝ) * N + (P.card : ℝ) ^ 2) := by
  have hR : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  rcases lt_or_ge N (1 / 2) with h | h
  · rw [sig_eq_zero P χ t h]
    positivity
  have hterm : ∀ r s, ‖∑ n ∈ dyad N, wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2 ≤ N + 4 := by
    intro r s
    have hb : ‖∑ n ∈ dyad N, wh n * famA χ t r n * conj (famA χ t s n)‖ ≤ (N + 1) * N ^ (-(1 / 2 : ℝ)) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ n ∈ dyad N, ‖wh n * famA χ t r n * conj (famA χ t s n)‖
          ≤ ∑ n ∈ dyad N, N ^ (-(1 / 2 : ℝ)) := by
            refine Finset.sum_le_sum fun n hn => ?_
            obtain ⟨hn1, _⟩ := (mem_dyad hN.le).1 hn
            have hn0 : 0 < n := by exact_mod_cast lt_trans hN hn1
            rw [norm_mul, norm_mul, Complex.norm_conj, norm_wh]
            have h1 := norm_famA_le χ t r hn0
            have h2 := norm_famA_le χ t s hn0
            have h3 : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ N ^ (-(1 / 2 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos hN hn1.le (by norm_num)
            have h4 : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
            calc (n : ℝ) ^ (-(1 / 2 : ℝ)) * ‖famA χ t r n‖ * ‖famA χ t s n‖
                ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * 1 * 1 := by gcongr
              _ ≤ N ^ (-(1 / 2 : ℝ)) := by rw [mul_one, mul_one]; exact h3
        _ = (dyad N).card * N ^ (-(1 / 2 : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N + 1) * N ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (card_dyad_le hN.le) (by positivity)
    have hsq : ((N + 1) * N ^ (-(1 / 2 : ℝ))) ^ 2 = (N + 1) ^ 2 / N := by
      rw [mul_pow, rpow_neg_half_sq hN.le, div_eq_mul_inv]
    calc ‖∑ n ∈ dyad N, wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2
        ≤ ((N + 1) * N ^ (-(1 / 2 : ℝ))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = (N + 1) ^ 2 / N := hsq
      _ ≤ N + 4 := by
          rw [div_le_iff₀ hN]
          nlinarith
  calc sig P χ t N = ∑ r ∈ P, ∑ s ∈ P, ‖∑ n ∈ dyad N, wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2 := rfl
    _ ≤ ∑ r ∈ P, ∑ s ∈ P, (N + 4) := Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => hterm r s
    _ = (P.card : ℝ) ^ 2 * (N + 4) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ((P.card : ℝ) + 4) * ((P.card : ℝ) * N + (P.card : ℝ) ^ 2) := by
        nlinarith [mul_nonneg hR hN.le, pow_nonneg hR 3]

/-! ### The bound `B(N) = RN + R² + R^{5/4}Q^{1/2}` -/

/-- `B(N) = RN + R² + R^{5/4}Q^{1/2}`. -/
def Bd (R Q N : ℝ) : ℝ := R * N + R ^ 2 + R ^ (5 / 4 : ℝ) * Q ^ (1 / 2 : ℝ)

lemma Bd_pos {R Q N : ℝ} (hR : 1 ≤ R) (hQ : 0 ≤ Q) (hN : 0 ≤ N) : 0 < Bd R Q N := by
  unfold Bd
  have : 0 < R := by linarith
  positivity

lemma Bd_mono {R Q N N' : ℝ} (hR : 0 ≤ R) (h : N ≤ N') : Bd R Q N ≤ Bd R Q N' := by
  unfold Bd
  gcongr

lemma RN_le_Bd {R Q N : ℝ} (hR : 0 ≤ R) (hQ : 0 ≤ Q) : R * N ≤ Bd R Q N := by
  unfold Bd
  have : 0 ≤ R ^ (5 / 4 : ℝ) * Q ^ (1 / 2 : ℝ) := by positivity
  nlinarith [sq_nonneg R]

lemma Rsq_le_Bd {R Q N : ℝ} (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hN : 0 ≤ N) : R ^ 2 ≤ Bd R Q N := by
  unfold Bd
  have : 0 ≤ R ^ (5 / 4 : ℝ) * Q ^ (1 / 2 : ℝ) := by positivity
  nlinarith [mul_nonneg hR hN]

/-- For `R ≥ 0`, `(R^{1/4})⁴ = R` and `(R^{1/4})⁵ = R^{5/4}`. -/
lemma rpow_quarter {R : ℝ} (hR : 0 ≤ R) : (R ^ (1 / 4 : ℝ)) ^ 4 = R ∧ (R ^ (1 / 4 : ℝ)) ^ 5 = R ^ (5 / 4 : ℝ) := by
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hR]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hR]
    norm_num

/-- **The squared bound**: for `R ≥ 1`, `Q, N ≥ 0`, `Z ≥ 1` and `Z − 1 ≤ Q^{1/2}R^{−1/4}`, `R²B(Z²) ≤ 3B(N)²`. -/
lemma Bd_sq_le {R Q N Z : ℝ} (hR : 1 ≤ R) (hQ : 0 ≤ Q) (hN : 0 ≤ N) (hZ : 1 ≤ Z)
    (hZb : Z - 1 ≤ Q ^ (1 / 2 : ℝ) * R ^ (-(1 / 4 : ℝ))) : R ^ 2 * Bd R Q (Z ^ 2) ≤ 3 * Bd R Q N ^ 2 := by
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨hx4, hx5⟩ := rpow_quarter hR0
  set x := R ^ (1 / 4 : ℝ) with hx
  set y := Q ^ (1 / 2 : ℝ) with hy
  have hx1 : 1 ≤ x := Real.one_le_rpow hR (by norm_num)
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by positivity
  have hxinv : R ^ (-(1 / 4 : ℝ)) = x⁻¹ := by rw [Real.rpow_neg hR0, hx]
  rw [hxinv] at hZb
  have h1 : x * Z ≤ x + y := by
    have h2 : x * (Z - 1) ≤ x * (y * x⁻¹) := mul_le_mul_of_nonneg_left hZb hx0
    have h3 : x * (y * x⁻¹) = y := by field_simp
    nlinarith
  have h2 : (x * Z) ^ 2 ≤ (x + y) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  unfold Bd
  rw [← hx5, ← hx4]
  have hx12 : x ^ 12 ≤ x ^ 16 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx11 : x ^ 11 * y ≤ x ^ 13 * y := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hx1 (by norm_num)) hy0
  have hN4 : 0 ≤ x ^ 4 * N := by positivity
  have h10 : x ^ 10 * (x * Z) ^ 2 ≤ x ^ 10 * (x + y) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith [mul_nonneg hN4 (by positivity : (0 : ℝ) ≤ x ^ 8 + x ^ 5 * y), sq_nonneg (x ^ 4 * N),
    sq_nonneg y, mul_nonneg (pow_nonneg hx0 10) (sq_nonneg y)]

/-- **The lengthened bound**: for `R, Q, N, U₀, Qδ ≥ 0` and `M ≤ QδQ^{1/2}R^{1/4} + U₀N`,
`B(2M) ≤ (2Qδ + 2U₀ + 1)B(N)`. -/
lemma Bd_len_le {R Q N M U₀ Qδ : ℝ} (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hN : 0 ≤ N) (hU₀ : 0 ≤ U₀) (hQδ : 0 ≤ Qδ)
    (hM : M ≤ Qδ * Q ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ) + U₀ * N) :
    Bd R Q (2 * M) ≤ (2 * Qδ + 2 * U₀ + 1) * Bd R Q N := by
  have h54 : R * R ^ (1 / 4 : ℝ) = R ^ (5 / 4 : ℝ) := by
    rw [← Real.rpow_one_add' hR (by norm_num)]
    norm_num
  have hRM : R * (2 * M) ≤ 2 * Qδ * (R ^ (5 / 4 : ℝ) * Q ^ (1 / 2 : ℝ)) + 2 * U₀ * (R * N) := by
    have h1 := mul_le_mul_of_nonneg_left hM hR
    calc R * (2 * M) = 2 * (R * M) := by ring
      _ ≤ 2 * (R * (Qδ * Q ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ) + U₀ * N)) := by linarith
      _ = 2 * Qδ * (R * R ^ (1 / 4 : ℝ) * Q ^ (1 / 2 : ℝ)) + 2 * U₀ * (R * N) := by ring
      _ = 2 * Qδ * (R ^ (5 / 4 : ℝ) * Q ^ (1 / 2 : ℝ)) + 2 * U₀ * (R * N) := by rw [h54]
  unfold Bd
  have h1 : 0 ≤ R * N := mul_nonneg hR hN
  have h2 : 0 ≤ R ^ 2 := sq_nonneg R
  have h3 : 0 ≤ R ^ (5 / 4 : ℝ) * Q ^ (1 / 2 : ℝ) := by positivity
  nlinarith [mul_nonneg hQδ h1, mul_nonneg hQδ h2, mul_nonneg hU₀ h2, mul_nonneg hU₀ h3]

/-! ### The factors `2^{ω(q)}`, `EQh(q)`, `Q₀(q)` and the tail -/

/-- For `n ≠ 0`, `2^{ω(n)} ≤ d(n)`. -/
lemma two_pow_le_card_divisors {n : ℕ} (hn : n ≠ 0) : 2 ^ n.primeFactors.card ≤ n.divisors.card := by
  rw [Nat.card_divisors hn, ← Finset.prod_const]
  refine Finset.prod_le_prod fun p hp => ?_
  have : n.factorization p ≠ 0 := Finsupp.mem_support_iff.1 (by rwa [Nat.support_factorization])
  omega

/-- `EQh(q) ≤ 4^{ω(q)}`: each factor `(1 − p^{−1/2})⁻¹` is at most `4`. -/
lemma EQh_le (q : ℕ) : EQh q ≤ 4 ^ q.primeFactors.card := by
  unfold EQh
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
  all_goals
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (p : ℝ)⁻¹ := rpow_neg_half_sq (by linarith)
    have h2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h3 : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have h4 : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by nlinarith
  · exact inv_nonneg.2 (by linarith)
  · have h5 : (1 : ℝ) / 4 ≤ 1 - (p : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
    calc (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ ≤ (1 / 4)⁻¹ := inv_anti₀ (by norm_num) h5
      _ = 4 := by norm_num

/-- For `q ≠ 0`, `EQh(q) ≤ d(q)²`. -/
lemma EQh_le_sq {q : ℕ} (hq : q ≠ 0) : EQh q ≤ (q.divisors.card : ℝ) ^ 2 := by
  have h2 : (2 : ℝ) ^ q.primeFactors.card ≤ q.divisors.card := by exact_mod_cast two_pow_le_card_divisors hq
  calc EQh q ≤ 4 ^ q.primeFactors.card := EQh_le q
    _ = ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
    _ ≤ (q.divisors.card : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2

/-- For `q ≠ 0`, `Q₀(q) ≤ πC_0d(q)³`. -/
lemma Q0_le {q : ℕ} (hq : q ≠ 0) : Q0 q ≤ Real.pi * CGK 0 * (q.divisors.card : ℝ) ^ 3 := by
  unfold Q0
  have h2 : (2 : ℝ) ^ q.primeFactors.card ≤ q.divisors.card := by exact_mod_cast two_pow_le_card_divisors hq
  have h4 := EQh_le_sq hq
  have hC := CGK_pos 0
  have hE := EQh_pos q
  calc 2 ^ q.primeFactors.card * (Real.pi * CGK 0) * EQh q
      ≤ (q.divisors.card : ℝ) * (Real.pi * CGK 0) * (q.divisors.card : ℝ) ^ 2 := by gcongr
    _ = Real.pi * CGK 0 * (q.divisors.card : ℝ) ^ 3 := by ring

/-- The constant `2πC_KI_K` of the tail. -/
def ctail (K : ℕ) : ℝ := 2 * Real.pi * CGK K * IK K

lemma ctail_nonneg (K : ℕ) : 0 ≤ ctail K := by
  unfold ctail
  have := CGK_pos K
  have := IK_nonneg K
  positivity

lemma TT_nonneg (q K : ℕ) {N : ℝ} (Z : ℕ) {T : ℝ} (hN : 0 ≤ N) (hT : 0 ≤ T) : 0 ≤ TT q K N Z T := by
  unfold TT
  have := CGK_pos K
  have := EQh_pos q
  have := IK_nonneg K
  positivity

/-- **The tail factor**: for `q ≠ 0`, `T ≥ 0`, `Kδ ≥ 1` and `NZ ≥ (q(1 + 2T))^{1+δ}`,
`T_K(N, Z, T) ≤ 2πC_KI_Kd(q)³`. -/
lemma TT_le {q K : ℕ} (hq : q ≠ 0) {N T δ : ℝ} {Z : ℕ} (hT : 0 ≤ T) (hK : 1 ≤ K * δ)
    (hNZ : ((q : ℝ) * (1 + 2 * T)) ^ (1 + δ) ≤ N * Z) :
    TT q K N Z T ≤ ctail K * (q.divisors.card : ℝ) ^ 3 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq
  have hT1 : (1 : ℝ) ≤ 1 + 2 * T := by linarith
  have hQ1 : (1 : ℝ) ≤ (q : ℝ) * (1 + 2 * T) := by nlinarith
  have hQ0 : (0 : ℝ) < (q : ℝ) * (1 + 2 * T) := by linarith
  have h1 : (N * Z) ^ (-(K : ℝ)) ≤ (((q : ℝ) * (1 + 2 * T)) ^ (1 + δ)) ^ (-(K : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hNZ (by simp)
  have h2 : (((q : ℝ) * (1 + 2 * T)) ^ (1 + δ)) ^ (-(K : ℝ)) =
      (q : ℝ) ^ ((1 + δ) * -(K : ℝ)) * (1 + 2 * T) ^ ((1 + δ) * -(K : ℝ)) := by
    rw [← Real.rpow_mul hQ0.le, Real.mul_rpow (by positivity) (by positivity)]
  have h3 : (q : ℝ) ^ ((K : ℝ) + 1 / 2) * (q : ℝ) ^ ((1 + δ) * -(K : ℝ)) ≤ 1 := by
    rw [← Real.rpow_add (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hq1 (by nlinarith)
  have h4 : (1 + 2 * T) ^ (K + 1) * (1 + 2 * T) ^ ((1 + δ) * -(K : ℝ)) ≤ 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hT1 (by push_cast; nlinarith)
  have hCK := CGK_pos K
  have hEQ := EQh_pos q
  have hI := IK_nonneg K
  have h2w : (2 : ℝ) ^ q.primeFactors.card ≤ q.divisors.card := by exact_mod_cast two_pow_le_card_divisors hq
  have hE2 := EQh_le_sq hq
  unfold TT ctail
  calc 2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
        (N * Z) ^ (-(K : ℝ)) * (1 + 2 * T) ^ (K + 1) * IK K
      ≤ 2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
        ((q : ℝ) ^ ((1 + δ) * -(K : ℝ)) * (1 + 2 * T) ^ ((1 + δ) * -(K : ℝ))) * (1 + 2 * T) ^ (K + 1) * IK K := by
        gcongr
        exact h1.trans h2.le
    _ = 2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * IK K *
        (((q : ℝ) ^ ((K : ℝ) + 1 / 2) * (q : ℝ) ^ ((1 + δ) * -(K : ℝ))) *
          ((1 + 2 * T) ^ (K + 1) * (1 + 2 * T) ^ ((1 + δ) * -(K : ℝ)))) := by ring
    _ ≤ 2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * IK K * (1 * 1) := by
        gcongr
    _ = 2 * (2 ^ q.primeFactors.card * EQh q) * (Real.pi * CGK K * IK K) := by ring
    _ ≤ 2 * ((q.divisors.card : ℝ) * (q.divisors.card : ℝ) ^ 2) * (Real.pi * CGK K * IK K) := by gcongr
    _ = 2 * Real.pi * CGK K * IK K * (q.divisors.card : ℝ) ^ 3 := by ring

/-! ### Kerr's two cases -/

/-- `Q = q(1 + 2T)`. -/
def Qq (q : ℕ) (T : ℝ) : ℝ := q * (1 + 2 * T)

/-- `J = log₂⌊4Q⌋`. -/
def Jm (q : ℕ) (T : ℝ) : ℕ := Nat.log 2 ⌊4 * Qq q T⌋₊

/-- `U₀ = 12d(q)² + 4`. -/
def U0 (q : ℕ) : ℝ := 12 * (q.divisors.card : ℝ) ^ 2 + 4

/-- `N* = Q^{1/2+δ}R^{1/4}`. -/
def Nst (q : ℕ) (T δ R : ℝ) : ℝ := Qq q T ^ (1 / 2 + δ) * R ^ (1 / 4 : ℝ)

/-- The range of the divisor bound, `L = 4(1 + U₀)Q^{1+δ}`. -/
def Lm (q : ℕ) (T δ : ℝ) : ℝ := 4 * (1 + U0 q) * Qq q T ^ (1 + δ)

/-- `A₁ = C(1 + 2c_K²d(q)⁶)`, with `c_K = 2πC_KI_K`. -/
def A1 (C : ℝ) (K q : ℕ) : ℝ := C * (1 + 2 * ctail K ^ 2 * (q.divisors.card : ℝ) ^ 6)

/-- `B₁ = 2CQ₀(q)²D(J + 1)`. -/
def B1 (C D : ℝ) (q : ℕ) (T : ℝ) : ℝ := 2 * C * Q0 q ^ 2 * D * ((Jm q T : ℝ) + 1)

/-- `M_B = 36d(q)D²(2Q^δ + 2U₀ + 1)`. -/
def MB (D : ℝ) (q : ℕ) (T δ : ℝ) : ℝ := 36 * (q.divisors.card : ℝ) * D ^ 2 * (2 * Qq q T ^ δ + 2 * U0 q + 1)

lemma one_le_Qq {q : ℕ} [NeZero q] {T : ℝ} (hT : 0 ≤ T) : 1 ≤ Qq q T := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  unfold Qq
  nlinarith

lemma one_le_card_divisors {q : ℕ} [NeZero q] : (1 : ℝ) ≤ q.divisors.card := by
  have h : 0 < q.divisors.card := Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 (NeZero.ne q)⟩
  exact_mod_cast h

/-- **Case A** (Kerr's case `N ≥ ∆^{2/3}`, here `N ≥ min(N*, Q^{1+δ})`): for `R ≥ 1`, `T ≥ 1`, `Kδ ≥ 1`,
`C, D, s ≥ 0`, the reflected bound `hrefl`, `d(m) ≤ D` for `1 ≤ m ≤ 4Q`, `σ ≤ sB` on `N > 0`, `N ≥ 1/2` and
`N ≥ N*` or `N ≥ Q^{1+δ}`: `σ(N) ≤ (A₁ + B₁√s)B(N)`. The dual length is `Z = ⌈Q^{1+δ}/N⌉`. -/
theorem caseA {q : ℕ} [NeZero q] (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {T δ C D s : ℝ}
    {K : ℕ} (hR : 1 ≤ (P.card : ℝ)) (hT : 1 ≤ T) (hKδ : 1 ≤ K * δ) (hC : 0 ≤ C) (hD0 : 0 ≤ D)
    (hrefl : ∀ (N : ℝ) (Z : ℕ), 0 < N → 1 ≤ Z → sig P χ t N ≤
      C * (N * P.card + Q0 q ^ 2 * shat P χ t Z + TT q K N Z T ^ 2 * (P.card : ℝ) ^ 2 / N))
    (hD : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ 4 * Qq q T → (m.divisors.card : ℝ) ≤ D)
    (hs : 0 ≤ s) (hσ : ∀ N, 0 < N → sig P χ t N ≤ s * Bd P.card (Qq q T) N)
    {N : ℝ} (hN : 1 / 2 ≤ N) (hN1 : Nst q T δ P.card ≤ N ∨ Qq q T ^ (1 + δ) ≤ N) :
    sig P χ t N ≤ (A1 C K q + B1 C D q T * √s) * Bd P.card (Qq q T) N := by
  have hq : q ≠ 0 := NeZero.ne q
  have hQ1 : 1 ≤ Qq q T := one_le_Qq (by linarith)
  set R : ℝ := (P.card : ℝ) with hRdef
  set Q := Qq q T with hQdef
  have hQ0 : 0 ≤ Q := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hN0 : 0 < N := by linarith
  have hT0 : 0 ≤ T := by linarith
  -- the dual length
  have hpos : 0 < Q ^ (1 + δ) / N := by positivity
  set Z : ℕ := ⌈Q ^ (1 + δ) / N⌉₊ with hZdef
  have hZ1 : 1 ≤ Z := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hpos).ne'
  have hZ1r : (1 : ℝ) ≤ Z := by exact_mod_cast hZ1
  have hNZ : Q ^ (1 + δ) ≤ N * Z := by
    have h := Nat.le_ceil (Q ^ (1 + δ) / N)
    rw [div_le_iff₀ hN0] at h
    linarith
  have hZb : (Z : ℝ) - 1 ≤ Q ^ (1 / 2 : ℝ) * R ^ (-(1 / 4 : ℝ)) := by
    have hy : 0 ≤ Q ^ (1 / 2 : ℝ) * R ^ (-(1 / 4 : ℝ)) := by positivity
    rcases hN1 with h | h
    · have hlt : (Z : ℝ) < Q ^ (1 + δ) / N + 1 := Nat.ceil_lt_add_one hpos.le
      have e1 : Q ^ (1 / 2 : ℝ) * Q ^ (1 / 2 + δ) = Q ^ (1 + δ) := by
        rw [← Real.rpow_add (by positivity)]
        ring_nf
      have e2 : R ^ (-(1 / 4 : ℝ)) * R ^ (1 / 4 : ℝ) = 1 := by
        rw [← Real.rpow_add (by positivity)]
        simp
      have h2 : Q ^ (1 + δ) / N ≤ Q ^ (1 / 2 : ℝ) * R ^ (-(1 / 4 : ℝ)) := by
        rw [div_le_iff₀ hN0]
        unfold Nst at h
        calc Q ^ (1 + δ) = Q ^ (1 / 2 : ℝ) * R ^ (-(1 / 4 : ℝ)) * (Q ^ (1 / 2 + δ) * R ^ (1 / 4 : ℝ)) := by
              rw [show Q ^ (1 / 2 : ℝ) * R ^ (-(1 / 4 : ℝ)) * (Q ^ (1 / 2 + δ) * R ^ (1 / 4 : ℝ)) =
                (Q ^ (1 / 2 : ℝ) * Q ^ (1 / 2 + δ)) * (R ^ (-(1 / 4 : ℝ)) * R ^ (1 / 4 : ℝ)) by ring, e1, e2,
                mul_one]
          _ ≤ Q ^ (1 / 2 : ℝ) * R ^ (-(1 / 4 : ℝ)) * N := mul_le_mul_of_nonneg_left h hy
      linarith
    · have hle : Q ^ (1 + δ) / N ≤ 1 := (div_le_one hN0).2 h
      have hZle : Z ≤ 1 := Nat.ceil_le.2 (by exact_mod_cast hle)
      have : (Z : ℝ) ≤ 1 := by exact_mod_cast hZle
      linarith
  -- `Z² ≤ 4Q`
  have hZ4 : (Z : ℝ) ^ 2 ≤ 4 * Q := by
    have hRi : R ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num)
    have hy1 : 1 ≤ Q ^ (1 / 2 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
    have hy0 : 0 ≤ Q ^ (1 / 2 : ℝ) := by positivity
    have h1 : Q ^ (1 / 2 : ℝ) * R ^ (-(1 / 4 : ℝ)) ≤ Q ^ (1 / 2 : ℝ) := by
      calc Q ^ (1 / 2 : ℝ) * R ^ (-(1 / 4 : ℝ)) ≤ Q ^ (1 / 2 : ℝ) * 1 := mul_le_mul_of_nonneg_left hRi hy0
        _ = Q ^ (1 / 2 : ℝ) := mul_one _
    have hZ' : (Z : ℝ) ≤ 2 * Q ^ (1 / 2 : ℝ) := by linarith
    have hysq : (Q ^ (1 / 2 : ℝ)) ^ 2 = Q := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0]
      norm_num
    calc (Z : ℝ) ^ 2 ≤ (2 * Q ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hZ' 2
      _ = 4 * Q := by rw [mul_pow, hysq]; norm_num
  -- squaring
  have hdivZ : ∀ m ∈ Finset.Icc 1 ⌊(Z : ℝ) ^ 2⌋₊, (m.divisors.card : ℝ) ≤ D := fun m hm => by
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.1 hm
    refine hD m hm1 ?_
    have h1 : (m : ℝ) ≤ ⌊(Z : ℝ) ^ 2⌋₊ := by exact_mod_cast hm2
    have h2 : (⌊(Z : ℝ) ^ 2⌋₊ : ℝ) ≤ (Z : ℝ) ^ 2 := Nat.floor_le (by positivity)
    linarith
  have hsq := shat_sq_le P χ t (Y := (Z : ℝ)) (by positivity) hD0 hdivZ
  -- the dyadic pieces of `[1, Z²]`
  set J' : ℕ := Nat.log 2 (Z ^ 2) with hJ'
  have hJlt : (Z : ℝ) ^ 2 < 2 ^ (J' + 1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Z ^ 2)
    exact_mod_cast h
  have hdy := shat_le_sum_sig P χ t (Y := (Z : ℝ) ^ 2) (by positivity) hJlt
  have hJle : J' ≤ Jm q T := by
    unfold Jm
    apply Nat.log_mono_right
    have h : ((Z ^ 2 : ℕ) : ℝ) ≤ 4 * Qq q T := by push_cast; exact hZ4
    exact Nat.le_floor h
  have hJ1 : (J' : ℝ) + 1 ≤ (Jm q T : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hJle 1
  have hterm : ∀ j ∈ Finset.range (J' + 1), sig P χ t ((Z : ℝ) ^ 2 / 2 ^ (j + 1)) ≤ s * Bd R Q ((Z : ℝ) ^ 2) :=
    fun j _ => (hσ _ (by positivity)).trans
      (mul_le_mul_of_nonneg_left (Bd_mono hR0 (div_le_self (by positivity) (one_le_pow₀ (by norm_num)))) hs)
  have hBZ : 0 ≤ s * Bd R Q ((Z : ℝ) ^ 2) := mul_nonneg hs (Bd_pos hR hQ0 (by positivity)).le
  have hS2 : shat P χ t ((Z : ℝ) ^ 2) ≤ ((Jm q T : ℝ) + 1) ^ 2 * s * Bd R Q ((Z : ℝ) ^ 2) := by
    calc shat P χ t ((Z : ℝ) ^ 2)
        ≤ (J' + 1) * ∑ j ∈ Finset.range (J' + 1), sig P χ t ((Z : ℝ) ^ 2 / 2 ^ (j + 1)) := hdy
      _ ≤ (J' + 1) * ∑ j ∈ Finset.range (J' + 1), s * Bd R Q ((Z : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
      _ = ((J' : ℝ) + 1) ^ 2 * (s * Bd R Q ((Z : ℝ) ^ 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ((Jm q T : ℝ) + 1) ^ 2 * (s * Bd R Q ((Z : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hJ1 2) hBZ
      _ = ((Jm q T : ℝ) + 1) ^ 2 * s * Bd R Q ((Z : ℝ) ^ 2) := by ring
  -- `Ŝ(Z) ≤ 2D(J + 1)√s B(N)`
  have hB := Bd_sq_le hR hQ0 hN0.le hZ1r hZb
  have hSZ0 : 0 ≤ shat P χ t Z := dsum_nonneg _ _ _ _
  have hBN := (Bd_pos hR hQ0 hN0.le).le
  have hS : shat P χ t Z ≤ 2 * D * ((Jm q T : ℝ) + 1) * √s * Bd R Q N := by
    have h1 : shat P χ t Z ^ 2 ≤ (2 * D * ((Jm q T : ℝ) + 1) * √s * Bd R Q N) ^ 2 := by
      calc shat P χ t Z ^ 2 ≤ R ^ 2 * D ^ 2 * shat P χ t ((Z : ℝ) ^ 2) := hsq
        _ ≤ R ^ 2 * D ^ 2 * (((Jm q T : ℝ) + 1) ^ 2 * s * Bd R Q ((Z : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hS2 (by positivity)
        _ = D ^ 2 * ((Jm q T : ℝ) + 1) ^ 2 * s * (R ^ 2 * Bd R Q ((Z : ℝ) ^ 2)) := by ring
        _ ≤ D ^ 2 * ((Jm q T : ℝ) + 1) ^ 2 * s * (3 * Bd R Q N ^ 2) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
        _ ≤ (2 * D * ((Jm q T : ℝ) + 1) * √s * Bd R Q N) ^ 2 := by
            rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hs]
            have hX : 0 ≤ D ^ 2 * ((Jm q T : ℝ) + 1) ^ 2 * s * Bd R Q N ^ 2 := by positivity
            nlinarith
    exact (pow_le_pow_iff_left₀ hSZ0 (by positivity) two_ne_zero).1 h1
  -- the tail
  have hTT := TT_le (K := K) hq hT0 hKδ (N := N) (Z := Z) hNZ
  have hTT0 := TT_nonneg q K Z hN0.le hT0
  have hct := ctail_nonneg K
  have hTT2 : TT q K N Z T ^ 2 * R ^ 2 / N ≤ 2 * ctail K ^ 2 * (q.divisors.card : ℝ) ^ 6 * R ^ 2 := by
    have h1 : TT q K N Z T ^ 2 ≤ (ctail K * (q.divisors.card : ℝ) ^ 3) ^ 2 := pow_le_pow_left₀ hTT0 hTT 2
    have h2 : R ^ 2 / N ≤ 2 * R ^ 2 := by
      rw [div_le_iff₀ hN0]
      nlinarith [sq_nonneg R]
    calc TT q K N Z T ^ 2 * R ^ 2 / N = TT q K N Z T ^ 2 * (R ^ 2 / N) := by ring
      _ ≤ (ctail K * (q.divisors.card : ℝ) ^ 3) ^ 2 * (2 * R ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * ctail K ^ 2 * (q.divisors.card : ℝ) ^ 6 * R ^ 2 := by ring
  -- the reflection
  have hr := hrefl N Z hN0 hZ1
  have h1 : N * R ≤ Bd R Q N := by rw [mul_comm]; exact RN_le_Bd hR0 hQ0
  have h2 : Q0 q ^ 2 * shat P χ t Z ≤ Q0 q ^ 2 * (2 * D * ((Jm q T : ℝ) + 1) * √s * Bd R Q N) :=
    mul_le_mul_of_nonneg_left hS (sq_nonneg _)
  have h3 : TT q K N Z T ^ 2 * R ^ 2 / N ≤ 2 * ctail K ^ 2 * (q.divisors.card : ℝ) ^ 6 * Bd R Q N :=
    hTT2.trans (mul_le_mul_of_nonneg_left (Rsq_le_Bd hR0 hQ0 hN0.le) (by positivity))
  unfold A1 B1
  calc sig P χ t N ≤ C * (N * R + Q0 q ^ 2 * shat P χ t Z + TT q K N Z T ^ 2 * R ^ 2 / N) := hr
    _ ≤ C * (Bd R Q N + Q0 q ^ 2 * (2 * D * ((Jm q T : ℝ) + 1) * √s * Bd R Q N) +
          2 * ctail K ^ 2 * (q.divisors.card : ℝ) ^ 6 * Bd R Q N) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ = (C * (1 + 2 * ctail K ^ 2 * (q.divisors.card : ℝ) ^ 6) +
          2 * C * Q0 q ^ 2 * D * ((Jm q T : ℝ) + 1) * √s) * Bd R Q N := by ring

/-- **Case B** (Kerr's lengthening): for `R ≥ 1`, `T ≥ 1`, `0 < δ`, `D, F ≥ 0`, `d(m) ≤ D` for `1 ≤ m ≤ L`, the bound
`σ ≤ FB` at every `M ≥ 1/2` with `M ≥ N*` or `M ≥ Q^{1+δ}`, and `1/2 ≤ N < min(N*, Q^{1+δ})`: `σ(N) ≤ M_BFB(N)`.
The lengthening is round 696's `sig_le_lengthen` at `U = max(min(N*, Q^{1+δ})/N, U₀)`. -/
theorem caseB {q : ℕ} [NeZero q] (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {T δ D F : ℝ}
    (hR : 1 ≤ (P.card : ℝ)) (hT : 1 ≤ T) (hδ : 0 < δ) (hD0 : 0 ≤ D) (hF : 0 ≤ F)
    (hD : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ Lm q T δ → (m.divisors.card : ℝ) ≤ D)
    (hA : ∀ M, 1 / 2 ≤ M → (Nst q T δ P.card ≤ M ∨ Qq q T ^ (1 + δ) ≤ M) →
      sig P χ t M ≤ F * Bd P.card (Qq q T) M)
    {N : ℝ} (hN : 1 / 2 ≤ N) (hN1 : N < Nst q T δ P.card) (hN2 : N < Qq q T ^ (1 + δ)) :
    sig P χ t N ≤ MB D q T δ * F * Bd P.card (Qq q T) N := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hQ1 : 1 ≤ Qq q T := one_le_Qq (by linarith)
  set R : ℝ := (P.card : ℝ) with hRdef
  set Q := Qq q T with hQdef
  have hQ0 : 0 ≤ Q := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hN0 : 0 < N := by linarith
  have hd1 := one_le_card_divisors (q := q)
  have hU04 : (4 : ℝ) ≤ U0 q := by
    unfold U0
    nlinarith
  have hNst1 : 1 ≤ Nst q T δ R := by
    unfold Nst
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hQ1 (by linarith)) (Real.one_le_rpow hR (by norm_num))
  have hQd1 : 1 ≤ Q ^ (1 + δ) := Real.one_le_rpow hQ1 (by linarith)
  set N₁ := min (Nst q T δ R) (Q ^ (1 + δ)) with hN₁
  have hN₁h : 1 / 2 ≤ N₁ := le_min (by linarith) (by linarith)
  have hN₁Q : N₁ ≤ Q ^ (1 + δ) := min_le_right _ _
  have hN₁N : N₁ ≤ Nst q T δ R := min_le_left _ _
  set U := max (N₁ / N) (U0 q) with hU
  have hUU : U0 q ≤ U := le_max_right _ _
  have hU0 : 12 * (q.divisors.card : ℝ) ^ 2 + 4 ≤ U := hUU
  have hNU1 : N₁ ≤ N * U := by
    have h : N₁ / N ≤ U := le_max_left _ _
    rw [div_le_iff₀ hN0] at h
    linarith
  have hNU2 : N * U ≤ N₁ + U0 q * N := by
    rcases le_total (N₁ / N) (U0 q) with h | h
    · rw [hU, max_eq_right h]
      nlinarith
    · rw [hU, max_eq_left h, mul_div_cancel₀ _ hN0.ne']
      nlinarith
  have hU0' : 0 ≤ U := by linarith
  -- the divisor range
  have hdiv : ∀ m ∈ Finset.Icc 1 ⌊4 * N * U⌋₊, (m.divisors.card : ℝ) ≤ D := fun m hm => by
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.1 hm
    refine hD m hm1 ?_
    have h1 : (m : ℝ) ≤ ⌊4 * N * U⌋₊ := by exact_mod_cast hm2
    have h2 : (⌊4 * N * U⌋₊ : ℝ) ≤ 4 * N * U := Nat.floor_le (by positivity)
    have h3 : N * U ≤ (1 + U0 q) * Q ^ (1 + δ) := by nlinarith
    unfold Lm
    linarith
  have hlen := sig_le_lengthen P χ t hq0 hN0.le hU0 hD0 hdiv
  have hσ1 := hA (N * U) (by linarith) (min_le_iff.1 hNU1)
  have hσ2 := hA (2 * N * U) (by linarith) (min_le_iff.1 (by linarith))
  -- `B(2NU) ≤ (2Q^δ + 2U₀ + 1)B(N)`
  have hNst : Nst q T δ R = Q ^ δ * Q ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ) := by
    unfold Nst
    rw [← hQdef, ← Real.rpow_add (by positivity)]
    ring_nf
  have hM : N * U ≤ Q ^ δ * Q ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ) + U0 q * N := by
    rw [← hNst]
    linarith
  have hlenB := Bd_len_le hR0 hQ0 hN0.le (by linarith) (by positivity) hM
  have e2 : 2 * N * U = 2 * (N * U) := by ring
  have hB1 : Bd R Q (N * U) ≤ Bd R Q (2 * (N * U)) := Bd_mono hR0 (by nlinarith)
  rw [e2] at hlen hσ2
  have hd0 : (0 : ℝ) ≤ q.divisors.card := by linarith
  calc sig P χ t N ≤ 18 * q.divisors.card * D ^ 2 * (sig P χ t (N * U) + sig P χ t (2 * (N * U))) := hlen
    _ ≤ 18 * q.divisors.card * D ^ 2 * (F * Bd R Q (2 * (N * U)) + F * Bd R Q (2 * (N * U))) := by
        have h1 : sig P χ t (N * U) ≤ F * Bd R Q (2 * (N * U)) :=
          hσ1.trans (mul_le_mul_of_nonneg_left hB1 hF)
        gcongr
    _ = 36 * q.divisors.card * D ^ 2 * F * Bd R Q (2 * (N * U)) := by ring
    _ ≤ 36 * q.divisors.card * D ^ 2 * F * ((2 * Q ^ δ + 2 * U0 q + 1) * Bd R Q N) :=
        mul_le_mul_of_nonneg_left hlenB (by positivity)
    _ = MB D q T δ * F * Bd R Q N := by
        unfold MB
        ring

/-- **One step of the iteration**: for `R ≥ 1`, `T ≥ 1`, `0 < δ`, `Kδ ≥ 1`, `C, D, s ≥ 0`, the reflected bound `hrefl`,
`d(m) ≤ D` for `1 ≤ m ≤ L` and `σ ≤ sB` on `N > 0`, `σ(N) ≤ (M_BB₁√s + M_BA₁)B(N)` for every `N > 0`. -/
theorem step {q : ℕ} [NeZero q] (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {T δ C D s : ℝ}
    {K : ℕ} (hR : 1 ≤ (P.card : ℝ)) (hT : 1 ≤ T) (hδ : 0 < δ) (hKδ : 1 ≤ K * δ) (hC : 0 ≤ C) (hD0 : 0 ≤ D)
    (hrefl : ∀ (N : ℝ) (Z : ℕ), 0 < N → 1 ≤ Z → sig P χ t N ≤
      C * (N * P.card + Q0 q ^ 2 * shat P χ t Z + TT q K N Z T ^ 2 * (P.card : ℝ) ^ 2 / N))
    (hD : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ Lm q T δ → (m.divisors.card : ℝ) ≤ D)
    (hs : 0 ≤ s) (hσ : ∀ N, 0 < N → sig P χ t N ≤ s * Bd P.card (Qq q T) N) :
    ∀ N, 0 < N → sig P χ t N ≤
      (MB D q T δ * B1 C D q T * √s + MB D q T δ * A1 C K q) * Bd P.card (Qq q T) N := by
  have hQ1 : 1 ≤ Qq q T := one_le_Qq (by linarith)
  have hd1 := one_le_card_divisors (q := q)
  have hU04 : (4 : ℝ) ≤ U0 q := by
    unfold U0
    nlinarith
  have h4L : 4 * Qq q T ≤ Lm q T δ := by
    have h1 : Qq q T ≤ Qq q T ^ (1 + δ) := by
      calc Qq q T = Qq q T ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ Qq q T ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
    unfold Lm
    nlinarith
  have hD4 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ 4 * Qq q T → (m.divisors.card : ℝ) ≤ D :=
    fun m hm1 hm2 => hD m hm1 (hm2.trans h4L)
  have hD1 : 1 ≤ D := by
    have h := hD 1 le_rfl (by norm_num; linarith)
    simpa using h
  have hMB : 1 ≤ MB D q T δ := by
    unfold MB
    have h1 : 1 ≤ 2 * Qq q T ^ δ + 2 * U0 q + 1 := by
      have : 0 ≤ Qq q T ^ δ := by positivity
      linarith
    have h2 : 1 ≤ D ^ 2 := one_le_pow₀ hD1
    have h3 : (1 : ℝ) ≤ 36 * (q.divisors.card : ℝ) := by linarith
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ 36 * (q.divisors.card : ℝ) * D ^ 2 * (2 * Qq q T ^ δ + 2 * U0 q + 1) := by gcongr
  have hA1 : 0 ≤ A1 C K q := by
    unfold A1
    have := ctail_nonneg K
    positivity
  have hB1 : 0 ≤ B1 C D q T := by
    unfold B1
    positivity
  have hF : 0 ≤ A1 C K q + B1 C D q T * √s := by positivity
  have hQ0 : 0 ≤ Qq q T := by linarith
  intro N hN
  have hBN := (Bd_pos hR hQ0 hN.le).le
  have hfin : (A1 C K q + B1 C D q T * √s) * Bd P.card (Qq q T) N ≤
      (MB D q T δ * B1 C D q T * √s + MB D q T δ * A1 C K q) * Bd P.card (Qq q T) N := by
    have : A1 C K q + B1 C D q T * √s ≤ MB D q T δ * B1 C D q T * √s + MB D q T δ * A1 C K q := by
      nlinarith [mul_nonneg hB1 (Real.sqrt_nonneg s)]
    exact mul_le_mul_of_nonneg_right this hBN
  have hcaseA : ∀ M, 1 / 2 ≤ M → (Nst q T δ P.card ≤ M ∨ Qq q T ^ (1 + δ) ≤ M) →
      sig P χ t M ≤ (A1 C K q + B1 C D q T * √s) * Bd P.card (Qq q T) M :=
    fun M hM hM1 => caseA P χ t hR hT hKδ hC hD0 hrefl hD4 hs hσ hM hM1
  rcases lt_or_ge N (1 / 2) with h | h
  · rw [sig_eq_zero P χ t h]
    have hMB0 : 0 ≤ MB D q T δ := by linarith
    positivity
  by_cases hc : Nst q T δ P.card ≤ N ∨ Qq q T ^ (1 + δ) ≤ N
  · exact (hcaseA N h hc).trans hfin
  · rw [not_or, not_le, not_le] at hc
    calc sig P χ t N ≤ MB D q T δ * (A1 C K q + B1 C D q T * √s) * Bd P.card (Qq q T) N :=
          caseB P χ t hR hT hδ hD0 hF hD hcaseA h hc.1 hc.2
      _ = (MB D q T δ * B1 C D q T * √s + MB D q T δ * A1 C K q) * Bd P.card (Qq q T) N := by ring

/-- **The iteration**: for `T ≥ 1`, `0 < δ`, `Kδ ≥ 1`, `C, D ≥ 0`, the reflected bound `hrefl` and `d(m) ≤ D` for
`1 ≤ m ≤ L`, `σ(N) ≤ ((M_BB₁)² + 2M_BA₁)B(N)` for every `N > 0` (the supremum argument, with the trivial bound to
start). -/
theorem sig_le_iter {q : ℕ} [NeZero q] (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {T δ C D : ℝ}
    {K : ℕ} (hT : 1 ≤ T) (hδ : 0 < δ) (hKδ : 1 ≤ K * δ) (hC : 0 ≤ C) (hD0 : 0 ≤ D)
    (hrefl : ∀ (N : ℝ) (Z : ℕ), 0 < N → 1 ≤ Z → sig P χ t N ≤
      C * (N * P.card + Q0 q ^ 2 * shat P χ t Z + TT q K N Z T ^ 2 * (P.card : ℝ) ^ 2 / N))
    (hD : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ Lm q T δ → (m.divisors.card : ℝ) ≤ D) :
    ∀ N, 0 < N → sig P χ t N ≤
      ((MB D q T δ * B1 C D q T) ^ 2 + 2 * (MB D q T δ * A1 C K q)) * Bd P.card (Qq q T) N := by
  by_cases hP : P = ∅
  · intro N _
    subst hP
    have h0 : sig (∅ : Finset ι) χ t N = 0 := by
      unfold sig dsum
      simp
    have hB0 : Bd ((∅ : Finset ι).card : ℝ) (Qq q T) N = 0 := by
      unfold Bd
      simp
    rw [h0, hB0, mul_zero]
  have hR : 1 ≤ (P.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hP)
  have hQ0 : 0 ≤ Qq q T := zero_le_one.trans (one_le_Qq (q := q) (by linarith))
  refine sup_arg (F := sig P χ t) (B := Bd P.card (Qq q T)) (fun N hN => Bd_pos hR hQ0 hN.le)
    (fun N _ => dsum_nonneg _ _ _ _) (s₀ := (P.card : ℝ) + 4) (fun N hN => ?_)
    (fun s hs hσ => step P χ t hR hT hδ hKδ hC hD0 hrefl hD hs hσ)
  have h1 := sig_le_triv P χ t hN
  have h2 : (P.card : ℝ) * N + (P.card : ℝ) ^ 2 ≤ Bd P.card (Qq q T) N := by
    unfold Bd
    have : 0 ≤ (P.card : ℝ) ^ (5 / 4 : ℝ) * Qq q T ^ (1 / 2 : ℝ) := by positivity
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))

/-- **Kerr's iteration with characters**: for `0 < δ` there is `C ≥ 0` such that, for `q ≥ 1`, `T ≥ 1`, points with
`|t_r| ≤ T` and the separation, and `D ≥ 0` with `d(m) ≤ D` for `1 ≤ m ≤ L`,
`σ(N) ≤ ((M_BB₁)² + 2M_BA₁)B(N)` for every `N > 0`, with `K = ⌈1/δ⌉`. -/
theorem sig_bound {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} (P : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {T D : ℝ}, 1 ≤ T → (∀ i ∈ P, |t i| ≤ T) →
    (∀ i ∈ P, ∀ j ∈ P, i ≠ j → χ i ≠ χ j ∨ 1 ≤ |t i - t j|) → 0 ≤ D →
    (∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ Lm q T δ → (m.divisors.card : ℝ) ≤ D) →
    ∀ N, 0 < N → sig P χ t N ≤
      ((MB D q T δ * B1 C D q T) ^ 2 + 2 * (MB D q T δ * A1 C ⌈1 / δ⌉₊ q)) * Bd P.card (Qq q T) N := by
  have hK : 1 ≤ ⌈1 / δ⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hKδ : 1 ≤ (⌈1 / δ⌉₊ : ℝ) * δ := by
    have h := Nat.le_ceil (1 / δ)
    rw [div_le_iff₀ hδ] at h
    linarith
  obtain ⟨C, hC, hrefl⟩ := sig_le_refl hK
  refine ⟨C, hC, ?_⟩
  intro q _ ι P χ t T D hT ht hsep hD0 hD
  exact sig_le_iter P χ t hT hδ hKδ hC hD0 (fun N Z hN hZ => hrefl q P χ t hN hZ ht hsep) hD

end LinnikCGLHBIter

#print axioms LinnikCGLHBIter.sup_arg
#print axioms LinnikCGLHBIter.sig_le_triv
#print axioms LinnikCGLHBIter.caseA
#print axioms LinnikCGLHBIter.caseB
#print axioms LinnikCGLHBIter.sig_bound
