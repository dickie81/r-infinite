/-
# Round 694: positivity, and the double sums of Heath-Brown's bound (the CGL plan's stage M5)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Stage M5 is round 670's displayed hypothesis `CGLT101`, their Theorem 10.1 (Heath-Brown's bound for double sums with
characters). Its source, their [6], has not been read. The route here follows Kerr's proof for `q = 1`
(arXiv:1909.12075, §§5–6: his Lemmas 18–20 and 22–27, Corollaries 21 and 28, and Theorem 16), with two inputs that
carry characters, both from Jutila (Acta Arith. 32 (1977), 55–62, read from its scanned pages), and both quoted by
Heath-Brown in Canad. J. Math. 31 (1979), 231–240:
* his Lemma 1, the reflection of a smoothed sum `Σ_nb(n)χ(n)n^{−s}` for a character `χ` mod `q`, imprimitive ones
  included and the principal one at `|t| ≥ h²`, with the dual sum over `χ̄` itself at the cost of a factor `q^ε`; for
  `χ ≠ 1` with round 638's weight `w(n/N)²`, round 642's `norm_gram_le` is a form of it;
* his Lemma 2, positivity: this file's `dsum_le`.
Since the dual sum of the pair `(r, s)` carries `χ̄_rχ_s`, the reflected double sum is again one of the same family,
the form in which Kerr's §6 iterates.

This file is the algebra of the double sums.

The stack's form.
* `dsum P A S a` is `Σ_{r,s∈P}|Σ_{n∈S}a_nA_r(n)Ā_s(n)|²` for any functions `A_r`, and `kern` is its kernel
  `K(n, m) = Σ_rA_r(n)Ā_r(m)`. Expanding the square gives `Σ_{n,m∈S}a_nā_m|K(n, m)|²` (`dsum_eq_kern`), whose
  factors `|K|²` are nonnegative, so `|a_n| ≤ b_n` gives the bound (`dsum_le`). Kerr's Lemma 18 also restricts the
  pairs to `|t_r − t_s| ≤ Δ`, through Fejér's kernel; `CGLT101` sums over all pairs, and this file has no such
  restriction.
* The family is `A_r(n) = χ_r(n)n^{it_r}` (`famA`), multiplicative in `n` (`famA_mul`), with
  `A_r(n)Ā_s(n) = χ_r(n)χ̄_s(n)n^{i(t_r−t_s)}` for `n ≥ 1` (`famA_mul_conj`), the summand of `CGLT101`.
* With the weight `n^{−1/2}` (`wh`), `σ(N)` (`sig`) is the double sum over `N < n ≤ 2N` (round 670's `dyad`), and
  `Ŝ(Y)` (`shat`) the one over `1 ≤ n ≤ Y`. Positivity makes `Ŝ` monotone in `Y` (`shat_mono`).
* Squaring (Kerr's Lemma 22, here for `Ŝ`): `(Σ_{n≤Y}…)²` is a sum over `m = n₁n₂ ≤ Y²`, whose coefficients count
  the factorizations, at most `d(m)` of them.

Plain statements, with `R = |P|`.
* `dsum_nonneg`: `0 ≤ dsum P A S a`.
* `sum4_comm`: four finite sums commute.
* `dsum_eq_kern`: `dsum P A S a = Σ_{n,m∈S}a_nā_m|K(n, m)|²`.
* `dsum_le`: for `S ⊆ S'`, `|a_n| ≤ b_n` on `S` and `b_n ≥ 0` on `S'`, `dsum P A S a ≤ dsum P A S' b`.
* `dsum_const_mul`, `dsum_conj`: `dsum P A S (ca) = |c|²·dsum P A S a`; and the family `Ā_r` with the weights `a`
  has the double sum of the family `A_r` with the weights `ā`.
* `famA_mul_conj`, `famA_mul`, `norm_wh`: as above, and `|n^{−1/2}| = n^{−1/2}`.
* `shat_mono`, `sig_le_shat`: for `Y ≤ Y'`, `Ŝ(Y) ≤ Ŝ(Y')`; and `σ(N) ≤ Ŝ(2N)`.
* `dsum_twist_le`: for real `u`, the weights `n^{−1/2+iu}` give at most what `n^{−1/2}` gives.
* `sum_Ioc_pieces`, `shat_le_sum_sig`: for `Y ≥ 0`, `(Y/2^{J+1}, Y]` is the union of the pieces
  `(Y/2^{j+1}, Y/2^j]`, `j ≤ J`; and for `0 ≤ Y < 2^{J+1}`, `Ŝ(Y) ≤ (J + 1)Σ_{j≤J}σ(Y/2^{j+1})`.
* `card_fiber_le`: for `m ≥ 1`, at most `d(m)` pairs `(n₁, n₂)` have `n₁n₂ = m`.
* `shat_sq_le`: for `Y ≥ 0` and `D ≥ 0` with `d(m) ≤ D` for `1 ≤ m ≤ Y²`, `Ŝ(Y)² ≤ R²D²Ŝ(Y²)`.

The file imports `LinnikCGLT101.lean`.
-/

import LinnikCGLT101

open Complex Set Real Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace LinnikCGLHBPos

open LinnikCGLT101

variable {ι : Type*}

/-! ### The double sum, its kernel and positivity -/

/-- The double sum `Σ_{r,s∈P}|Σ_{n∈S}a_nA_r(n)Ā_s(n)|²`. -/
def dsum (P : Finset ι) (A : ι → ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ r ∈ P, ∑ s ∈ P, ‖∑ n ∈ S, a n * A r n * conj (A s n)‖ ^ 2

/-- The kernel `K(n, m) = Σ_{r∈P}A_r(n)Ā_r(m)`. -/
def kern (P : Finset ι) (A : ι → ℕ → ℂ) (n m : ℕ) : ℂ := ∑ r ∈ P, A r n * conj (A r m)

lemma dsum_nonneg (P : Finset ι) (A : ι → ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) : 0 ≤ dsum P A S a :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Four finite sums in another order: `Σ_rΣ_sΣ_nΣ_m = Σ_nΣ_mΣ_rΣ_s`. -/
lemma sum4_comm {α β : Type*} (P : Finset α) (S : Finset β) (g : α → α → β → β → ℂ) :
    ∑ r ∈ P, ∑ s ∈ P, ∑ n ∈ S, ∑ m ∈ S, g r s n m = ∑ n ∈ S, ∑ m ∈ S, ∑ r ∈ P, ∑ s ∈ P, g r s n m := by
  calc ∑ r ∈ P, ∑ s ∈ P, ∑ n ∈ S, ∑ m ∈ S, g r s n m = ∑ r ∈ P, ∑ n ∈ S, ∑ s ∈ P, ∑ m ∈ S, g r s n m :=
        Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = ∑ n ∈ S, ∑ r ∈ P, ∑ s ∈ P, ∑ m ∈ S, g r s n m := Finset.sum_comm
    _ = ∑ n ∈ S, ∑ r ∈ P, ∑ m ∈ S, ∑ s ∈ P, g r s n m :=
        Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = ∑ n ∈ S, ∑ m ∈ S, ∑ r ∈ P, ∑ s ∈ P, g r s n m := Finset.sum_congr rfl fun n _ => Finset.sum_comm

/-- **The duality**: `Σ_{r,s}|Σ_{n∈S}a_nA_r(n)Ā_s(n)|² = Σ_{n,m∈S}a_nā_m|K(n, m)|²`. -/
lemma dsum_eq_kern (P : Finset ι) (A : ι → ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) :
    (dsum P A S a : ℂ) = ∑ n ∈ S, ∑ m ∈ S, a n * conj (a m) * ((‖kern P A n m‖ ^ 2 : ℝ) : ℂ) := by
  have hsq : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * conj z := fun z => by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  unfold dsum kern
  push_cast
  simp only [hsq, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  -- both sides are `Σ_{n,m}Σ_{r,s}a_nā_mA_r(n)Ā_r(m)Ā_s(n)A_s(m)`, in different orders
  rw [sum4_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

/-- **Positivity** (Jutila's Lemma 2, Heath-Brown's use of it): for `S ⊆ S'`, `|a_n| ≤ b_n` on `S` and `b_n ≥ 0` on
`S'`, `Σ_{r,s}|Σ_{n∈S}a_nA_r(n)Ā_s(n)|² ≤ Σ_{r,s}|Σ_{n∈S'}b_nA_r(n)Ā_s(n)|²`, for any functions `A_r`. -/
theorem dsum_le (P : Finset ι) (A : ι → ℕ → ℂ) {S S' : Finset ℕ} (hSS : S ⊆ S') {a : ℕ → ℂ} {b : ℕ → ℝ}
    (hab : ∀ n ∈ S, ‖a n‖ ≤ b n) (hb : ∀ n ∈ S', 0 ≤ b n) :
    dsum P A S a ≤ dsum P A S' (fun n => (b n : ℂ)) := by
  have hK : ∀ n m, 0 ≤ ‖kern P A n m‖ ^ 2 := fun _ _ => sq_nonneg _
  have e1 : dsum P A S a = (∑ n ∈ S, ∑ m ∈ S, a n * conj (a m) * ((‖kern P A n m‖ ^ 2 : ℝ) : ℂ)).re := by
    rw [← dsum_eq_kern, Complex.ofReal_re]
  have e2 : dsum P A S' (fun n => (b n : ℂ)) = ∑ n ∈ S', ∑ m ∈ S', b n * b m * ‖kern P A n m‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [dsum_eq_kern]
    push_cast
    simp only [Complex.conj_ofReal]
  rw [e1, e2]
  calc (∑ n ∈ S, ∑ m ∈ S, a n * conj (a m) * ((‖kern P A n m‖ ^ 2 : ℝ) : ℂ)).re
      ≤ ‖∑ n ∈ S, ∑ m ∈ S, a n * conj (a m) * ((‖kern P A n m‖ ^ 2 : ℝ) : ℂ)‖ := Complex.re_le_norm _
    _ ≤ ∑ n ∈ S, ∑ m ∈ S, ‖a n‖ * ‖a m‖ * ‖kern P A n m‖ ^ 2 := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans ?_)
        refine le_of_eq (Finset.sum_congr rfl fun m _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hK n m)]
    _ ≤ ∑ n ∈ S, ∑ m ∈ S, b n * b m * ‖kern P A n m‖ ^ 2 :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm =>
          mul_le_mul_of_nonneg_right (mul_le_mul (hab n hn) (hab m hm) (norm_nonneg _) (hb n (hSS hn))) (hK n m)
    _ ≤ ∑ n ∈ S', ∑ m ∈ S', b n * b m * ‖kern P A n m‖ ^ 2 := by
        refine (Finset.sum_le_sum fun n hn => Finset.sum_le_sum_of_subset_of_nonneg hSS ?_).trans
          (Finset.sum_le_sum_of_subset_of_nonneg hSS ?_)
        · intro m hm _
          exact mul_nonneg (mul_nonneg (hb n (hSS hn)) (hb m hm)) (hK n m)
        · intro n hn _
          exact Finset.sum_nonneg fun m hm => mul_nonneg (mul_nonneg (hb n hn) (hb m hm)) (hK n m)

/-- A constant factor: `Σ_{r,s}|Σ_n ca_nA_r(n)Ā_s(n)|² = |c|²Σ_{r,s}|Σ_n a_nA_r(n)Ā_s(n)|²`. -/
lemma dsum_const_mul (P : Finset ι) (A : ι → ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) (c : ℂ) :
    dsum P A S (fun n => c * a n) = ‖c‖ ^ 2 * dsum P A S a := by
  unfold dsum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : ∑ n ∈ S, c * a n * A r n * conj (A s n) = c * ∑ n ∈ S, a n * A r n * conj (A s n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [e, norm_mul, mul_pow]

/-- The conjugate family: `Σ_{r,s}|Σ_n a_nĀ_r(n)A_s(n)|² = Σ_{r,s}|Σ_n ā_nA_r(n)Ā_s(n)|²`. -/
lemma dsum_conj (P : Finset ι) (A : ι → ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) :
    dsum P (fun r n => conj (A r n)) S a = dsum P A S (fun n => conj (a n)) := by
  unfold dsum
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [← Complex.norm_conj (∑ n ∈ S, conj (a n) * A r n * conj (A s n))]
  congr 2
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _ => by simp only [map_mul, Complex.conj_conj]

/-! ### The family `χ_r(n)n^{it_r}` and its double sums -/

/-- `A_r(n) = χ_r(n)n^{it_r}`. -/
def famA {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (r : ι) (n : ℕ) : ℂ :=
  χ r n * (n : ℂ) ^ ((t r : ℂ) * I)

/-- The weight `n^{−1/2}`. -/
def wh (n : ℕ) : ℂ := (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

lemma norm_wh (n : ℕ) : ‖wh n‖ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [wh, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- For `n ≥ 1`, `A_r(n)Ā_s(n) = χ_r(n)χ̄_s(n)n^{i(t_r−t_s)}`. -/
lemma famA_mul_conj {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (r s : ι) {n : ℕ} (hn : 0 < n) :
    famA χ t r n * conj (famA χ t s n) = χ r n * conj (χ s n) * (n : ℂ) ^ (((t r - t s : ℝ) : ℂ) * I) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hl : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  have hc : conj ((n : ℂ) ^ ((t s : ℂ) * I)) = (n : ℂ) ^ (-((t s : ℂ) * I)) := by
    rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_conj, hl]
    congr 1
    rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  unfold famA
  rw [map_mul, hc]
  have e : (n : ℂ) ^ (((t r - t s : ℝ) : ℂ) * I) = (n : ℂ) ^ ((t r : ℂ) * I) * (n : ℂ) ^ (-((t s : ℂ) * I)) := by
    rw [← Complex.cpow_add _ _ hn0]
    congr 1
    push_cast
    ring
  rw [e]
  ring

/-- `A_r(nm) = A_r(n)A_r(m)`. -/
lemma famA_mul {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (r : ι) (n m : ℕ) :
    famA χ t r (n * m) = famA χ t r n * famA χ t r m := by
  unfold famA
  simp only [Nat.cast_mul, map_mul]
  rw [Complex.natCast_mul_natCast_cpow]
  ring

/-- `σ(N) = Σ_{r,s}|Σ_{N<n≤2N}χ_r(n)χ̄_s(n)n^{−1/2+i(t_r−t_s)}|²`. -/
def sig {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (N : ℝ) : ℝ :=
  dsum P (famA χ t) (dyad N) wh

/-- `Ŝ(Y) = Σ_{r,s}|Σ_{1≤n≤Y}χ_r(n)χ̄_s(n)n^{−1/2+i(t_r−t_s)}|²`. -/
def shat {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Y : ℝ) : ℝ :=
  dsum P (famA χ t) (Finset.Icc 1 ⌊Y⌋₊) wh

/-- **Monotonicity**: for `Y ≤ Y'`, `Ŝ(Y) ≤ Ŝ(Y')`. -/
lemma shat_mono {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {Y Y' : ℝ} (h : Y ≤ Y') :
    shat P χ t Y ≤ shat P χ t Y' :=
  dsum_le P (famA χ t) (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor h))
    (b := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (fun n _ => (norm_wh n).le) (fun n _ => by positivity)

/-- `σ(N) ≤ Ŝ(2N)`. -/
lemma sig_le_shat {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (N : ℝ) :
    sig P χ t N ≤ shat P χ t (2 * N) := by
  refine dsum_le P (famA χ t) ?_ (b := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (fun n _ => (norm_wh n).le)
    (fun n _ => by positivity)
  intro n hn
  rw [dyad, Finset.mem_Ioc] at hn
  rw [Finset.mem_Icc]
  omega

/-- A unimodular twist `n^{iu}` does not raise the double sum: `Σ_{r,s}|Σ_n n^{−1/2+iu}A_r(n)Ā_s(n)|²` over `S` is at
most the same sum without `n^{iu}`. -/
lemma dsum_twist_le (P : Finset ι) (A : ι → ℕ → ℂ) (S : Finset ℕ) (u : ℝ) :
    dsum P A S (fun n => wh n * (n : ℂ) ^ ((u : ℂ) * I)) ≤ dsum P A S wh := by
  refine dsum_le P A le_rfl (b := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (fun n _ => ?_) (fun n _ => by positivity)
  rw [norm_mul, norm_wh]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero]
    rw [Real.zero_rpow (by norm_num), zero_mul]
  · rw [Complex.norm_natCast_cpow_of_pos hn]
    simp

/-! ### The dyadic decomposition -/

/-- For `Y ≥ 0`, the pieces `(Y/2^{j+1}, Y/2^j]`, `j ≤ J`, of `(Y/2^{J+1}, Y]`. -/
lemma sum_Ioc_pieces (f : ℕ → ℂ) {Y : ℝ} (hY : 0 ≤ Y) (J : ℕ) :
    ∑ n ∈ Finset.Ioc ⌊Y / 2 ^ (J + 1)⌋₊ ⌊Y⌋₊, f n =
      ∑ j ∈ Finset.range (J + 1), ∑ n ∈ dyad (Y / 2 ^ (j + 1)), f n := by
  have hd : ∀ j : ℕ, dyad (Y / 2 ^ (j + 1)) = Finset.Ioc ⌊Y / 2 ^ (j + 1)⌋₊ ⌊Y / 2 ^ j⌋₊ := fun j => by
    rw [dyad]
    congr 2
    rw [pow_succ]
    field_simp
  have hmono : ∀ j : ℕ, ⌊Y / 2 ^ (j + 1)⌋₊ ≤ ⌊Y / 2 ^ j⌋₊ := fun j =>
    Nat.floor_le_floor (div_le_div_of_nonneg_left hY (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  induction J with
  | zero => simp [hd]
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih, hd (J + 1)]
    have hle : ⌊Y / 2 ^ (J + 1)⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_le_floor (div_le_self hY (one_le_pow₀ (by norm_num)))
    rw [← Finset.Ioc_union_Ioc_eq_Ioc (hmono (J + 1)) hle, Finset.sum_union (Finset.disjoint_left.2 fun n h1 h2 => by
      rw [Finset.mem_Ioc] at h1 h2; omega)]
    ring

/-- **The dyadic decomposition**: for `0 ≤ Y < 2^{J+1}`, `Ŝ(Y) ≤ (J + 1)Σ_{j≤J}σ(Y/2^{j+1})`. -/
theorem shat_le_sum_sig {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {Y : ℝ} (hY : 0 ≤ Y)
    {J : ℕ} (hJ : Y < 2 ^ (J + 1)) :
    shat P χ t Y ≤ (J + 1) * ∑ j ∈ Finset.range (J + 1), sig P χ t (Y / 2 ^ (j + 1)) := by
  have h0 : ⌊Y / 2 ^ (J + 1)⌋₊ = 0 := Nat.floor_eq_zero.2 ((div_lt_one (by positivity)).2 hJ)
  have hI : Finset.Icc 1 ⌊Y⌋₊ = Finset.Ioc ⌊Y / 2 ^ (J + 1)⌋₊ ⌊Y⌋₊ := by
    rw [h0]
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hcard : ((Finset.range (J + 1)).card : ℝ) = J + 1 := by simp
  set f : ι → ι → ℕ → ℝ := fun r s j =>
    ‖∑ n ∈ dyad (Y / 2 ^ (j + 1)), wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2 with hf
  have hpair : ∀ r s, ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2 ≤
      (J + 1) * ∑ j ∈ Finset.range (J + 1), f r s j := by
    intro r s
    rw [hI, sum_Ioc_pieces _ hY J]
    calc ‖∑ j ∈ Finset.range (J + 1), ∑ n ∈ dyad (Y / 2 ^ (j + 1)), wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2
        ≤ (∑ j ∈ Finset.range (J + 1),
            ‖∑ n ∈ dyad (Y / 2 ^ (j + 1)), wh n * famA χ t r n * conj (famA χ t s n)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ ((Finset.range (J + 1)).card : ℝ) * ∑ j ∈ Finset.range (J + 1), f r s j := sq_sum_le_card_mul_sum_sq
      _ = (J + 1) * ∑ j ∈ Finset.range (J + 1), f r s j := by rw [hcard]
  unfold shat sig dsum
  calc ∑ r ∈ P, ∑ s ∈ P, ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, wh n * famA χ t r n * conj (famA χ t s n)‖ ^ 2
      ≤ ∑ r ∈ P, ∑ s ∈ P, (J + 1) * ∑ j ∈ Finset.range (J + 1), f r s j :=
        Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => hpair r s
    _ = (J + 1) * ∑ j ∈ Finset.range (J + 1), ∑ r ∈ P, ∑ s ∈ P, f r s j := by
        simp_rw [← Finset.mul_sum]
        congr 1
        calc ∑ r ∈ P, ∑ s ∈ P, ∑ j ∈ Finset.range (J + 1), f r s j
            = ∑ r ∈ P, ∑ j ∈ Finset.range (J + 1), ∑ s ∈ P, f r s j :=
              Finset.sum_congr rfl fun r _ => Finset.sum_comm
          _ = ∑ j ∈ Finset.range (J + 1), ∑ r ∈ P, ∑ s ∈ P, f r s j := Finset.sum_comm

/-! ### Squaring -/

/-- The fiber of `(n₁, n₂) ↦ n₁n₂` over `m ≥ 1` has at most `d(m)` points. -/
lemma card_fiber_le (S : Finset ℕ) {m : ℕ} (hm : 0 < m) :
    ((S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 * p.2 = m)).card ≤ m.divisors.card := by
  refine Finset.card_le_card_of_injOn (fun p => p.1) (fun p hp => ?_) (fun p hp p' hp' h => ?_)
  · rw [Finset.mem_coe, Finset.mem_filter] at hp
    rw [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨⟨p.2, hp.2.symm⟩, hm.ne'⟩
  · rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
    simp only at h
    have h1 : p.1 * p.2 = p'.1 * p'.2 := hp.2.trans hp'.2.symm
    rw [h] at h1
    have hp1 : 0 < p'.1 := by
      rcases Nat.eq_zero_or_pos p'.1 with h0 | h0
      · rw [h0, zero_mul] at hp'
        exact absurd hp'.2 hm.ne
      · exact h0
    have h2 : p.2 = p'.2 := Nat.eq_of_mul_eq_mul_left hp1 h1
    exact Prod.ext h h2

/-- **Squaring**: for `Y ≥ 0` and `D ≥ 0` with `d(m) ≤ D` for `1 ≤ m ≤ Y²`, `Ŝ(Y)² ≤ |P|²D²Ŝ(Y²)`. -/
theorem shat_sq_le {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {Y : ℝ} (hY : 0 ≤ Y)
    {D : ℝ} (hD : 0 ≤ D) (hdiv : ∀ m ∈ Finset.Icc 1 ⌊Y ^ 2⌋₊, (m.divisors.card : ℝ) ≤ D) :
    shat P χ t Y ^ 2 ≤ (P.card : ℝ) ^ 2 * D ^ 2 * shat P χ t (Y ^ 2) := by
  set S := Finset.Icc 1 ⌊Y⌋₊ with hS
  set T := Finset.Icc 1 ⌊Y ^ 2⌋₊ with hT
  set A := famA χ t with hA
  -- the square of each inner sum is a sum over `m = n₁n₂`
  set c : ℕ → ℂ := fun m => (((S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 * p.2 = m)).card : ℂ) with hc
  have hmaps : ∀ p ∈ S ×ˢ S, p.1 * p.2 ∈ T := by
    intro p hp
    rw [Finset.mem_product, hS, Finset.mem_Icc, Finset.mem_Icc] at hp
    rw [hT, Finset.mem_Icc]
    refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    rw [Nat.le_floor_iff (by positivity)]
    have h1 : (p.1 : ℝ) ≤ Y := (Nat.le_floor_iff hY).1 hp.1.2
    have h2 : (p.2 : ℝ) ≤ Y := (Nat.le_floor_iff hY).1 hp.2.2
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) p.1, Nat.cast_nonneg (α := ℝ) p.2]
  have hsq : ∀ r s, (∑ n ∈ S, wh n * A r n * conj (A s n)) ^ 2 =
      ∑ m ∈ T, c m * wh m * A r m * conj (A s m) := by
    intro r s
    have hw : ∀ n₁ n₂ : ℕ, wh n₁ * wh n₂ = wh (n₁ * n₂) := fun n₁ n₂ => by
      unfold wh
      rw [← Complex.ofReal_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    have e : ∀ p ∈ S ×ˢ S, wh p.1 * A r p.1 * conj (A s p.1) * (wh p.2 * A r p.2 * conj (A s p.2)) =
        (fun m => wh m * A r m * conj (A s m)) (p.1 * p.2) := by
      intro p _
      simp only [hA, famA_mul, map_mul, ← hw]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2]), Finset.sum_const, nsmul_eq_mul, hc]
    ring
  -- Cauchy–Schwarz over the pairs
  have hcs : shat P χ t Y ^ 2 ≤ (P.card : ℝ) ^ 2 * ∑ r ∈ P, ∑ s ∈ P, ‖∑ n ∈ S, wh n * A r n * conj (A s n)‖ ^ 4 := by
    unfold shat dsum
    rw [← hS, ← hA, ← Finset.sum_product' (f := fun r s => ‖∑ n ∈ S, wh n * A r n * conj (A s n)‖ ^ 2),
      ← Finset.sum_product' (f := fun r s => ‖∑ n ∈ S, wh n * A r n * conj (A s n)‖ ^ 4)]
    have hcard : ((P ×ˢ P).card : ℝ) = (P.card : ℝ) ^ 2 := by rw [Finset.card_product]; push_cast; ring
    rw [← hcard]
    refine (sq_sum_le_card_mul_sum_sq).trans (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun p _ => by ring
  -- positivity with `|c_mm^{−1/2}| ≤ Dm^{−1/2}`
  have hpos : ∑ r ∈ P, ∑ s ∈ P, ‖∑ n ∈ S, wh n * A r n * conj (A s n)‖ ^ 4 ≤ D ^ 2 * shat P χ t (Y ^ 2) := by
    have e4 : ∀ r s, ‖∑ n ∈ S, wh n * A r n * conj (A s n)‖ ^ 4 =
        ‖∑ m ∈ T, (c m * wh m) * A r m * conj (A s m)‖ ^ 2 := by
      intro r s
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← norm_pow, hsq]
    simp_rw [e4]
    have h1 : dsum P A T (fun m => c m * wh m) ≤
        dsum P A T (fun m => ((D * (m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
      refine dsum_le P A le_rfl (fun m hm => ?_) (fun m _ => by positivity)
      rw [norm_mul, norm_wh, hc, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hm0 : 0 < m := by rw [hT, Finset.mem_Icc] at hm; omega
      exact (Nat.cast_le.2 (card_fiber_le S hm0)).trans (hdiv m hm)
    have h2 : dsum P A T (fun m => ((D * (m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = D ^ 2 * dsum P A T wh := by
      have e : (fun m : ℕ => ((D * (m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = fun m => (D : ℂ) * wh m := by
        funext m; unfold wh; push_cast; ring
      rw [e, dsum_const_mul, Complex.norm_real, Real.norm_of_nonneg hD]
    have h3 := h1.trans (le_of_eq h2)
    unfold dsum at h3
    unfold shat
    rw [← hT, ← hA]
    exact h3
  calc shat P χ t Y ^ 2 ≤ (P.card : ℝ) ^ 2 * ∑ r ∈ P, ∑ s ∈ P, ‖∑ n ∈ S, wh n * A r n * conj (A s n)‖ ^ 4 := hcs
    _ ≤ (P.card : ℝ) ^ 2 * (D ^ 2 * shat P χ t (Y ^ 2)) :=
        mul_le_mul_of_nonneg_left hpos (by positivity)
    _ = (P.card : ℝ) ^ 2 * D ^ 2 * shat P χ t (Y ^ 2) := by ring

end LinnikCGLHBPos

#print axioms LinnikCGLHBPos.dsum_le
#print axioms LinnikCGLHBPos.shat_le_sum_sig
#print axioms LinnikCGLHBPos.shat_sq_le
