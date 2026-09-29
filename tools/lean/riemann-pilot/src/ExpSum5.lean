/-
# Layer II, steps (G2a) and (G2b): partial blocks and Abel summation (round 208)

Plain statements.
* `block_bound_partial`: `block_bound` for any partial block `(N, N']` with `N ≤ N' ≤ 2N`,
  with the same right-hand side.
* `abel_bound`: if every initial segment `Σ_{N<n≤m} aₙ` (`N ≤ m ≤ N'`) has size at most `B`,
  and the weights `wₙ ≥ 0` decrease on `(N, N']`, then `|Σ_{N<n≤N'} wₙ aₙ| ≤ w_{N+1}·B`.
  This turns bounds for `Σ n^{−it}` into bounds for `Σ n^{−σ−it}`.
-/
import ExpSum4

open Finset Complex

namespace ExpSum

open Vinogradov VinoHolder

/-- **Partial blocks.** -/
theorem block_bound_partial {t : ℝ} (ht : t ≠ 0) {N N' M K ℓ r : ℕ} {C η : ℝ} (hC : 0 < C)
    (hM : 1 ≤ M) (hℓ : 1 ≤ ℓ) (hr1 : 1 ≤ r) (hrK : r ≤ K) (hMN : 2 * M ^ 2 ≤ N)
    (hN1 : N ≤ N') (hN2 : N' ≤ 2 * N)
    (hJ : (J ℓ K M : ℝ) ≤ C * (M : ℝ) ^ (2 * (ℓ : ℝ) - (K : ℝ) * ((K : ℝ) + 1) / 2 + η))
    (hgood : |t| * ℓ * (M : ℝ) ^ r ≤ Real.pi * r * (N : ℝ) ^ r) :
    ‖∑ n ∈ Ioc N N', phaseF t n‖ ≤
      N * Phi t C η N M K ℓ r + 2 * |t| * N * ((M : ℝ) ^ 2 / N) ^ (K + 1) +
        2 * (M : ℝ) ^ 2 := by
  have hE := stepE t N N' M K hN1 hM hMN
  have hMpos : (0 : ℝ) < (M : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    positivity
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by have := Nat.one_le_pow 2 M hM; omega
    exact_mod_cast this
  set Y := (M : ℝ) ^ 2 * Phi t C η N M K ℓ r + 2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / N) ^ (K + 1)
  have hterm : ∀ n ∈ Ioc N N',
      ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T (alphaVec t n K) (A K a) (A K b)‖ +
        2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / n) ^ (K + 1) ≤ Y := by
    intro n hn
    have hn' := mem_Ioc.mp hn
    refine add_le_add (Bn_bound ht hC hM hℓ hr1 hrK hJ hn'.1 (hn'.2.trans hN2) hgood) ?_
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn'.1.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left hMpos.le hNpos hnN) _
  have hY0 : 0 ≤ Y := by
    have := hterm
    by_cases hne : (Ioc N N').Nonempty
    · obtain ⟨n, hn⟩ := hne
      exact le_trans (by positivity) (hterm n hn)
    · have hPhi : 0 ≤ Phi t C η N M K ℓ r := by unfold Phi; exact Real.rpow_nonneg (by
          have hW : 0 ≤ Wsave t N M ℓ r ∨ Wsave t N M ℓ r < 0 := le_or_gt 0 _
          rcases hW with hW | hW
          · positivity
          · exact absurd hW (by
              unfold Wsave
              push_neg
              have hlogL : 0 ≤ 1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ r) := by
                have h1 : (1 : ℝ) ≤ (ℓ : ℝ) * (M : ℝ) ^ r := by
                  have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
                  have : (1 : ℝ) ≤ (M : ℝ) ^ r := one_le_pow₀ (by exact_mod_cast hM)
                  nlinarith
                have := Real.log_nonneg h1; linarith
              exact add_nonneg (by positivity)
                (div_nonneg (mul_nonneg (by positivity) hlogL) (by positivity)))) _
      positivity
  have hsum := sum_le_sum hterm
  rw [sum_const, Nat.card_Ioc, nsmul_eq_mul] at hsum
  have hcard : ((N' - N : ℕ) : ℝ) ≤ N := by exact_mod_cast (show N' - N ≤ N by omega)
  refine hE.trans ?_
  have h1 : 1 / (M : ℝ) ^ 2 * ∑ n ∈ Ioc N N',
      (‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T (alphaVec t n K) (A K a) (A K b)‖ +
        2 * |t| * (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 / n) ^ (K + 1)) ≤ 1 / (M : ℝ) ^ 2 * (N * Y) :=
    mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_right hcard hY0)) (by positivity)
  have e : 1 / (M : ℝ) ^ 2 * (N * Y) =
      N * Phi t C η N M K ℓ r + 2 * |t| * N * ((M : ℝ) ^ 2 / N) ^ (K + 1) := by
    simp only [Y]; field_simp
  linarith

/-- **Abel summation with decreasing weights.** -/
theorem abel_bound (a : ℕ → ℂ) (w : ℕ → ℝ) (N N' : ℕ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ m, N ≤ m → m ≤ N' → ‖∑ n ∈ Ioc N m, a n‖ ≤ B)
    (hw0 : ∀ n, 0 ≤ w n) (hwd : ∀ n, N < n → n < N' → w (n + 1) ≤ w n) :
    ‖∑ n ∈ Ioc N N', (w n : ℂ) * a n‖ ≤ w (N + 1) * B := by
  rcases Nat.lt_or_ge N N' with hlt | hge
  · -- main claim by induction on `m ∈ [N+1, N']`
    have key : ∀ j, N + 1 + j ≤ N' →
        ‖∑ n ∈ Ioc N (N + 1 + j), (w n : ℂ) * a n -
          (w (N + 1 + j) : ℂ) * ∑ n ∈ Ioc N (N + 1 + j), a n‖ ≤ (w (N + 1) - w (N + 1 + j)) * B := by
      intro j
      induction j with
      | zero =>
        intro _
        simp [Nat.Ioc_succ_singleton]
      | succ j ih =>
        intro hj
        have hj' : N + 1 + j ≤ N' := by omega
        have ihj := ih hj'
        set m := N + 1 + j with hm
        have hIoc : Ioc N (m + 1) = insert (m + 1) (Ioc N m) := by
          ext x; simp only [mem_Ioc, mem_insert]; omega
        rw [show N + 1 + (j + 1) = m + 1 by omega, hIoc, sum_insert (by simp), sum_insert (by simp)]
        have e : (w (m + 1) : ℂ) * a (m + 1) + ∑ n ∈ Ioc N m, (w n : ℂ) * a n -
            (w (m + 1) : ℂ) * (a (m + 1) + ∑ n ∈ Ioc N m, a n) =
            (∑ n ∈ Ioc N m, (w n : ℂ) * a n - (w m : ℂ) * ∑ n ∈ Ioc N m, a n) +
              ((w m - w (m + 1) : ℝ) : ℂ) * ∑ n ∈ Ioc N m, a n := by
          push_cast; ring
        rw [e]
        have hwm : w (m + 1) ≤ w m := hwd m (by omega) (by omega)
        have hBm := hB m (by omega) hj'
        calc _ ≤ (w (N + 1) - w m) * B + (w m - w (m + 1)) * B := by
              refine (norm_add_le _ _).trans (add_le_add ihj ?_)
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
              exact mul_le_mul_of_nonneg_left hBm (by linarith)
          _ = (w (N + 1) - w (m + 1)) * B := by ring
    obtain ⟨j, hj⟩ : ∃ j, N' = N + 1 + j := ⟨N' - N - 1, by omega⟩
    have hk := key j (by omega)
    rw [← hj] at hk
    have hBN := hB N' hlt.le le_rfl
    calc ‖∑ n ∈ Ioc N N', (w n : ℂ) * a n‖
        ≤ ‖∑ n ∈ Ioc N N', (w n : ℂ) * a n - (w N' : ℂ) * ∑ n ∈ Ioc N N', a n‖ +
          ‖(w N' : ℂ) * ∑ n ∈ Ioc N N', a n‖ := by
          have := norm_add_le (∑ n ∈ Ioc N N', (w n : ℂ) * a n - (w N' : ℂ) * ∑ n ∈ Ioc N N', a n)
            ((w N' : ℂ) * ∑ n ∈ Ioc N N', a n)
          simpa using this
      _ ≤ (w (N + 1) - w N') * B + w N' * B := by
          refine add_le_add hk ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 _)]
          exact mul_le_mul_of_nonneg_left hBN (hw0 _)
      _ = w (N + 1) * B := by ring
  · have : Ioc N N' = ∅ := Finset.Ioc_eq_empty_of_le hge
    rw [this, sum_empty, norm_zero]
    exact mul_nonneg (hw0 _) hB0

end ExpSum
