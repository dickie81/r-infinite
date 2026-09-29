/-
# Layer II, step (E): shift and Taylor (round 205)

Plain statements.
* `shift_avg`: for any `f` with `|f| ≤ 1` and any interval `(A, B]`,
  `|Σ_{A<n≤B} f(n)| ≤ M^{−2} Σ_{A<n≤B} |Σ_{a,b≤M} f(n+ab)| + 2M²`.
  Shifting `n` by `ab ≤ M²` moves at most `2ab` terms.
* `phase_taylor`: for `x > 0`, `0 ≤ h ≤ x/2` and `K ≥ 0`,
  `−(t/2π)·log(x+h) = −(t/2π)·log x + Σ_{j<K} α_j h^{j+1} + ρ` with
  `α_j = (t/2π)(−1)^{j+1}/((j+1)x^{j+1})` and `|ρ| ≤ (|t|/π)(h/x)^{K+1}`.
  This uses Mathlib's `Real.abs_log_sub_add_sum_range_le`.
* `per_n`: for `2M² ≤ n`,
  `|Σ_{a,b≤M} e(−(t/2π) log(n+ab))| ≤ |Σ_{a,b≤M} e(Σ_j α_j(n)(ab)^{j+1})| + 2|t|M²(M²/n)^{K+1}`.
  The right-hand double sum is exactly the `bilinear_bound` sum.
-/
import ExpSum2

open Finset Complex

namespace ExpSum

open Vinogradov VinoHolder

lemma sum_shift (f : ℕ → ℂ) (A B h : ℕ) :
    ∑ n ∈ Ioc A B, f (n + h) = ∑ m ∈ Ioc (A + h) (B + h), f m := by
  apply Finset.sum_nbij' (fun n => n + h) (fun m => m - h)
  · intro n hn; simp only [mem_Ioc] at hn ⊢; omega
  · intro m hm; simp only [mem_Ioc] at hm ⊢; omega
  · intro n _; simp
  · intro m hm; simp only [mem_Ioc] at hm; omega
  · intro n _; rfl

lemma norm_sum_Ioc_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (A B : ℕ) :
    ‖∑ n ∈ Ioc A B, f n‖ ≤ (B - A : ℕ) := by
  calc ‖∑ n ∈ Ioc A B, f n‖ ≤ ∑ n ∈ Ioc A B, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc A B, (1 : ℝ) := sum_le_sum fun n _ => hf n
    _ = (B - A : ℕ) := by rw [sum_const, Nat.card_Ioc, nsmul_one]

/-- Shifting an interval sum by `h` changes it by at most `2h`. -/
lemma shift_diff (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (A B h : ℕ) (hAB : A ≤ B) :
    ‖∑ n ∈ Ioc A B, f n - ∑ n ∈ Ioc A B, f (n + h)‖ ≤ 2 * h := by
  rw [sum_shift]
  rcases le_or_gt (A + h) B with hle | hlt
  · rw [← sum_Ioc_consecutive f (show A ≤ A + h by omega) hle,
      ← sum_Ioc_consecutive f hle (show B ≤ B + h by omega)]
    have e : ∑ n ∈ Ioc A (A + h), f n + ∑ n ∈ Ioc (A + h) B, f n -
        (∑ n ∈ Ioc (A + h) B, f n + ∑ n ∈ Ioc B (B + h), f n) =
        ∑ n ∈ Ioc A (A + h), f n - ∑ n ∈ Ioc B (B + h), f n := by ring
    rw [e]
    have h1 := norm_sum_Ioc_le f hf A (A + h)
    have h2 := norm_sum_Ioc_le f hf B (B + h)
    rw [show A + h - A = h by omega] at h1
    rw [show B + h - B = h by omega] at h2
    calc _ ≤ ‖∑ n ∈ Ioc A (A + h), f n‖ + ‖∑ n ∈ Ioc B (B + h), f n‖ := norm_sub_le _ _
      _ ≤ (h : ℝ) + h := add_le_add h1 h2
      _ = 2 * h := by ring
  · have h1 := norm_sum_Ioc_le f hf A B
    have h2 := norm_sum_Ioc_le f hf (A + h) (B + h)
    have e1 : ((B - A : ℕ) : ℝ) ≤ h := by exact_mod_cast (show B - A ≤ h by omega)
    have e2 : ((B + h - (A + h) : ℕ) : ℝ) ≤ h := by exact_mod_cast (show B + h - (A + h) ≤ h by omega)
    calc _ ≤ ‖∑ n ∈ Ioc A B, f n‖ + ‖∑ n ∈ Ioc (A + h) (B + h), f n‖ := norm_sub_le _ _
      _ ≤ (h : ℝ) + h := add_le_add (h1.trans e1) (h2.trans e2)
      _ = 2 * h := by ring

/-- **Shift-and-average.** -/
theorem shift_avg (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (A B M : ℕ) (hAB : A ≤ B) (hM : 1 ≤ M) :
    ‖∑ n ∈ Ioc A B, f n‖ ≤
      (1 / (M : ℝ) ^ 2) * ∑ n ∈ Ioc A B, ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b)‖ +
        2 * (M : ℝ) ^ 2 := by
  set S := ∑ n ∈ Ioc A B, f n
  have hMpos : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  have hcard : ((Icc 1 M ×ˢ Icc 1 M).card : ℝ) = (M : ℝ) ^ 2 := by
    rw [card_product, Nat.card_Icc]; push_cast; ring
  have key : ‖((M : ℝ) ^ 2 : ℂ) * S -
      ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, ∑ n ∈ Ioc A B, f (n + a * b)‖ ≤ 2 * (M : ℝ) ^ 4 := by
    have e : ((M : ℝ) ^ 2 : ℂ) * S = ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, S := by
      rw [sum_const, sum_const, Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
    rw [e, ← sum_sub_distrib]
    calc ‖∑ a ∈ Icc 1 M, (∑ b ∈ Icc 1 M, S - ∑ b ∈ Icc 1 M, ∑ n ∈ Ioc A B, f (n + a * b))‖
        ≤ ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, (2 * (M : ℝ) ^ 2) := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun a ha => ?_)
          rw [← sum_sub_distrib]
          refine (norm_sum_le _ _).trans (sum_le_sum fun b hb => ?_)
          have ha' := (mem_Icc.mp ha).2
          have hb' := (mem_Icc.mp hb).2
          have hab : ((a * b : ℕ) : ℝ) ≤ (M : ℝ) ^ 2 := by
            have : a * b ≤ M * M := Nat.mul_le_mul ha' hb'
            rw [sq]; exact_mod_cast this
          have := shift_diff f hf A B (a * b) hAB
          linarith
      _ = 2 * (M : ℝ) ^ 4 := by
          rw [sum_const, sum_const, Nat.card_Icc]; simp; ring
  have hswap : ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, ∑ n ∈ Ioc A B, f (n + a * b) =
      ∑ n ∈ Ioc A B, ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b) := by
    calc ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, ∑ n ∈ Ioc A B, f (n + a * b)
        = ∑ a ∈ Icc 1 M, ∑ n ∈ Ioc A B, ∑ b ∈ Icc 1 M, f (n + a * b) :=
          sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [hswap] at key
  have h1 : (M : ℝ) ^ 2 * ‖S‖ ≤
      ‖∑ n ∈ Ioc A B, ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b)‖ + 2 * (M : ℝ) ^ 4 := by
    have := norm_sub_norm_le (((M : ℝ) ^ 2 : ℂ) * S)
      (∑ n ∈ Ioc A B, ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b))
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_natCast] at this
    linarith
  have h2 : ‖∑ n ∈ Ioc A B, ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b)‖ ≤
      ∑ n ∈ Ioc A B, ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b)‖ := norm_sum_le _ _
  have e : (1 / (M : ℝ) ^ 2) * ∑ n ∈ Ioc A B, ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b)‖ +
      2 * (M : ℝ) ^ 2 = (∑ n ∈ Ioc A B, ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b)‖ +
        2 * (M : ℝ) ^ 4) / (M : ℝ) ^ 2 := by field_simp
  rw [e, le_div_iff₀ hMpos]
  linarith

/-- The Taylor coefficients of `−(t/2π) log(x + h)` in `h`. -/
noncomputable def alphaVec (t x : ℝ) (K : ℕ) : Fin K → ℝ :=
  fun j => t / (2 * Real.pi) * (-1) ^ (j.val + 1) / ((j.val + 1) * x ^ (j.val + 1))

/-- **Taylor for the phase.** -/
theorem phase_taylor (t x h : ℝ) (K : ℕ) (hx : 0 < x) (hh0 : 0 ≤ h) (hh : h ≤ x / 2) :
    |(-(t / (2 * Real.pi)) * Real.log (x + h)) - (-(t / (2 * Real.pi)) * Real.log x) -
        ∑ j : Fin K, alphaVec t x K j * h ^ (j.val + 1)| ≤ |t| / Real.pi * (h / x) ^ (K + 1) := by
  set y := h / x with hy
  have hy0 : 0 ≤ y := div_nonneg hh0 hx.le
  have hy2 : y ≤ 1 / 2 := by rw [hy, div_le_iff₀ hx]; linarith
  have hlog : Real.log (x + h) - Real.log x = Real.log (1 - -y) := by
    rw [← Real.log_div (by linarith) hx.ne', sub_neg_eq_add, hy]
    congr 1; field_simp
  have habs : |-y| < 1 := by rw [abs_neg, abs_of_nonneg hy0]; linarith
  have hT := Real.abs_log_sub_add_sum_range_le habs K
  rw [abs_neg, abs_of_nonneg hy0] at hT
  have hden : y ^ (K + 1) / (1 - y) ≤ 2 * y ^ (K + 1) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg hy0 (K + 1)]
  have hsum : ∑ j : Fin K, alphaVec t x K j * h ^ (j.val + 1) =
      t / (2 * Real.pi) * ∑ i ∈ range K, (-y) ^ (i + 1) / (i + 1) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (-y) ^ (i + 1) / ((i : ℝ) + 1)), Finset.mul_sum]
    apply sum_congr rfl; intro i _
    simp only [alphaVec]
    rw [hy, show -(h / x) = (-1) * (h / x) by ring, mul_pow, div_pow]
    field_simp
  have hπ : 0 < Real.pi := Real.pi_pos
  have e : (-(t / (2 * Real.pi)) * Real.log (x + h)) - (-(t / (2 * Real.pi)) * Real.log x) -
      ∑ j : Fin K, alphaVec t x K j * h ^ (j.val + 1) =
      -(t / (2 * Real.pi)) * ((∑ i ∈ range K, (-y) ^ (i + 1) / (i + 1)) + Real.log (1 - -y)) := by
    rw [hsum, ← hlog]; ring
  rw [e, abs_mul, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  calc |t| / (2 * Real.pi) * |(∑ i ∈ range K, (-y) ^ (i + 1) / (i + 1)) + Real.log (1 - -y)|
      ≤ |t| / (2 * Real.pi) * (2 * y ^ (K + 1)) :=
        mul_le_mul_of_nonneg_left (hT.trans hden) (by positivity)
    _ = |t| / Real.pi * y ^ (K + 1) := by field_simp

lemma norm_ee_sub_one_le (ρ : ℝ) : ‖ee ρ - 1‖ ≤ 2 * Real.pi * |ρ| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * ρ)
  have e : ee ρ = Complex.exp (Complex.I * ((2 * Real.pi * ρ : ℝ) : ℂ)) := by
    unfold ee; push_cast; ring_nf
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- The summand `n^{−it}` written as `e(−(t/2π) log n)`. -/
noncomputable def phaseF (t : ℝ) (n : ℕ) : ℂ := ee (-(t / (2 * Real.pi)) * Real.log n)

lemma norm_phaseF (t : ℝ) (n : ℕ) : ‖phaseF t n‖ ≤ 1 := (norm_ee _).le

/-- **Per-`n` comparison.** For `2M² ≤ n`, the shifted double sum is the bilinear sum up to
`2|t|M²(M²/n)^{K+1}`. -/
theorem per_n (t : ℝ) (n M K : ℕ) (hM : 1 ≤ M) (hn : 2 * M ^ 2 ≤ n) :
    ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, phaseF t (n + a * b)‖ ≤
      ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T (alphaVec t n K) (A K a) (A K b)‖ +
        2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / n) ^ (K + 1) := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by have := Nat.one_le_pow 2 M hM; omega
    exact_mod_cast this
  set φ0 := -(t / (2 * Real.pi)) * Real.log n
  set ρ : ℕ → ℕ → ℝ := fun a b => (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + (a * b : ℕ))) - φ0 -
    ∑ j : Fin K, alphaVec t n K j * ((a * b : ℕ) : ℝ) ^ (j.val + 1) with hρ
  have hsplit : ∀ a b, phaseF t (n + a * b) =
      ee φ0 * (T (alphaVec t n K) (A K a) (A K b) + T (alphaVec t n K) (A K a) (A K b) *
        (ee (ρ a b) - 1)) := by
    intro a b
    have hT : T (alphaVec t n K) (A K a) (A K b) =
        ee (∑ j : Fin K, alphaVec t n K j * ((a * b : ℕ) : ℝ) ^ (j.val + 1)) := by
      unfold T A; congr 1; apply sum_congr rfl; intro j _; push_cast; ring
    rw [hT, mul_sub, mul_one, add_sub_cancel, ← ee_add, ← ee_add]
    unfold phaseF
    congr 1
    simp only [hρ]; push_cast; ring
  have hρb : ∀ a ∈ Icc 1 M, ∀ b ∈ Icc 1 M,
      |ρ a b| ≤ |t| / Real.pi * ((M : ℝ) ^ 2 / n) ^ (K + 1) := by
    intro a ha b hb
    have hab : a * b ≤ M ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul (mem_Icc.mp ha).2 (mem_Icc.mp hb).2
    have habr : ((a * b : ℕ) : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hab
    have hh : ((a * b : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
      have : ((2 * M ^ 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at this; linarith
    have := phase_taylor t n ((a * b : ℕ) : ℝ) K hnpos (by positivity) hh
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right habr hnpos.le) _
  calc ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, phaseF t (n + a * b)‖
      = ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T (alphaVec t n K) (A K a) (A K b) +
          ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M,
            T (alphaVec t n K) (A K a) (A K b) * (ee (ρ a b) - 1)‖ := by
        simp_rw [hsplit, ← Finset.mul_sum, ← Finset.sum_add_distrib, norm_mul, norm_ee, one_mul]
    _ ≤ ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T (alphaVec t n K) (A K a) (A K b)‖ +
          ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, 2 * Real.pi * (|t| / Real.pi * ((M : ℝ) ^ 2 / n) ^ (K + 1)) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun a ha => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun b hb => ?_)
        rw [norm_mul, norm_T, one_mul]
        exact (norm_ee_sub_one_le _).trans
          (mul_le_mul_of_nonneg_left (hρb a ha b hb) (by positivity))
    _ = _ := by
        rw [sum_const, sum_const, Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul]
        have := Real.pi_pos
        field_simp
        push_cast; ring

/-- **Step (E), combined.** For `2M² ≤ N₁`, the sum `Σ_{N₁<n≤N₂} n^{−it}` is controlled by the
bilinear sums at each `n` plus explicit errors. -/
theorem stepE (t : ℝ) (N₁ N₂ M K : ℕ) (hN : N₁ ≤ N₂) (hM : 1 ≤ M) (hN₁ : 2 * M ^ 2 ≤ N₁) :
    ‖∑ n ∈ Ioc N₁ N₂, phaseF t n‖ ≤
      (1 / (M : ℝ) ^ 2) * ∑ n ∈ Ioc N₁ N₂,
        (‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T (alphaVec t n K) (A K a) (A K b)‖ +
          2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / n) ^ (K + 1)) + 2 * (M : ℝ) ^ 2 := by
  refine (shift_avg (phaseF t) (norm_phaseF t) N₁ N₂ M hN hM).trans ?_
  gcongr with n hn
  exact per_n t n M K hM (hN₁.trans (mem_Ioc.mp hn).1.le)

end ExpSum
