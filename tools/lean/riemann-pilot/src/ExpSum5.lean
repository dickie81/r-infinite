/-
# Layer II, step (G2b): Abel summation (round 208)

`abel_bound`: if every initial segment `Σ_{N<n≤m} aₙ` (`N ≤ m ≤ N'`) has size at most `B`,
and the weights `wₙ ≥ 0` decrease on `(N, N']`, then `|Σ_{N<n≤N'} wₙ aₙ| ≤ w_{N+1}·B`.
This turns bounds for `Σ n^{−it}` into bounds for `Σ n^{−σ−it}`. (Round 208's `block_bound_partial`
fed only the superseded round-210 chain and was removed in round 218.)
-/
import ExpSum4

open Finset Complex

namespace ExpSum

open Vinogradov VinoHolder

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
