/-
# Round 705: the refined certificate, in the reals and over `Finset`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements about `SieveCert2Defs.lean`'s definitions, as `SieveCert.lean` and `SieveCertCols.lean` state them
for the certificate's.

* `total2_eq`, `rows2_eq`, `rowsJ2_eq`: the sums as double sums of `cost2` over `Finset` ranges.
* `rows2_eq_rowsJ2`, `rowsJ2_split`, `rows2_split`, `total2_eq_rows2_full`, `rows2_le_of_split`, `rowsJ2_le_of_split`,
  `rows2_le_of_rowsJ2`: the steps that assemble a bound on `total2` from its parts' bounds (`SieveCertCols.lean`'s, for
  `cost2`).
* `total2_div_lt`: `total2 < K` gives `total2/K < 1` in the reals.
* `cost2_of_dec`, `cost2_of_not_dec`, `cost2_of_not_cand`, `sub2_eq`: the refined cost by cases, and `sub2` as a
  `Finset` sum.
* `cost2_ge`: a dropped candidate cell's refined cost is at least its bound less `sub2`, in the reals.
* `keepK_le`: on a grid with `GridOK`, on a cell `k` that `keep` passes below a cell `(i, j)`, `keepK/K` is at most
  `H³·DEN/((e_i + H)(e_j + H)(e_k + H)(DEN − e_i − e_j − e_k))`, whose denominator is positive.

The file imports `SieveCert.lean` and `SieveCert2Defs.lean`.
-/
import SieveCert
import SieveCert2Defs

namespace SieveCert

section

variable [Grid]

/-! ### Sums -/

/-- The refined total is the double sum of the refined costs. -/
theorem total2_eq : total2 = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, cost2 i j := by
  simp [total2, sumTo_eq]

/-- `rows2 a b` is the double sum of the refined costs over `a ≤ i < b`. -/
theorem rows2_eq (a b : ℕ) : rows2 a b = ∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.range n, cost2 i j := by
  rw [rows2, sumTo_eq, Finset.sum_Ico_eq_sum_range]
  simp only [sumTo_eq]

/-- `rowsJ2 a b j₀ j₁` is the double sum of the refined costs over `a ≤ i < b` and `j₀ ≤ j < j₁`. -/
theorem rowsJ2_eq (a b j₀ j₁ : ℕ) :
    rowsJ2 a b j₀ j₁ = ∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico j₀ j₁, cost2 i j := by
  rw [rowsJ2, sumTo_eq, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sumTo_eq, Finset.sum_Ico_eq_sum_range]

/-- `rows2 a b` is `rowsJ2 a b 0 n`. -/
theorem rows2_eq_rowsJ2 (a b : ℕ) : rows2 a b = rowsJ2 a b 0 n := by
  rw [rows2_eq, rowsJ2_eq, Finset.range_eq_Ico]

/-- For `j₀ ≤ j₁ ≤ j₂` (`h₁`, `h₂`), `rowsJ2 a b j₀ j₂ = rowsJ2 a b j₀ j₁ + rowsJ2 a b j₁ j₂`. -/
theorem rowsJ2_split (a b : ℕ) {j₀ j₁ j₂ : ℕ} (h₁ : j₀ ≤ j₁) (h₂ : j₁ ≤ j₂) :
    rowsJ2 a b j₀ j₂ = rowsJ2 a b j₀ j₁ + rowsJ2 a b j₁ j₂ := by
  simp only [rowsJ2_eq, ← Finset.sum_add_distrib, Finset.sum_Ico_consecutive _ h₁ h₂]

/-- For `a ≤ b ≤ c` (`hab`, `hbc`), `rows2 a c = rows2 a b + rows2 b c`. -/
theorem rows2_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) : rows2 a c = rows2 a b + rows2 b c := by
  simp only [rows2_eq, Finset.sum_Ico_consecutive _ hab hbc]

/-- The refined total is `rows2 0 n`. -/
theorem total2_eq_rows2_full : total2 = rows2 0 n := by
  rw [total2_eq, rows2_eq, Finset.range_eq_Ico]

/-- A bound on `rows2 a c` from bounds on `rows2 a b` (`h₁`) and `rows2 b c` (`h₂`), for `a ≤ b ≤ c` (`hab`, `hbc`),
with the bounds' sum at most `B` (`hB`). -/
theorem rows2_le_of_split {a b c B₁ B₂ B : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (h₁ : rows2 a b ≤ B₁)
    (h₂ : rows2 b c ≤ B₂) (hB : B₁ + B₂ ≤ B) : rows2 a c ≤ B := by
  rw [rows2_split hab hbc]; exact (Nat.add_le_add h₁ h₂).trans hB

/-- A bound on `rowsJ2 a b j₀ j₂` from bounds on `rowsJ2 a b j₀ j₁` (`h₁`) and `rowsJ2 a b j₁ j₂` (`h₂`), for
`j₀ ≤ j₁ ≤ j₂` (`h₀₁`, `h₁₂`), with the bounds' sum at most `B` (`hB`). -/
theorem rowsJ2_le_of_split (a b : ℕ) {j₀ j₁ j₂ B₁ B₂ B : ℕ} (h₀₁ : j₀ ≤ j₁) (h₁₂ : j₁ ≤ j₂)
    (h₁ : rowsJ2 a b j₀ j₁ ≤ B₁) (h₂ : rowsJ2 a b j₁ j₂ ≤ B₂) (hB : B₁ + B₂ ≤ B) : rowsJ2 a b j₀ j₂ ≤ B := by
  rw [rowsJ2_split a b h₀₁ h₁₂]; exact (Nat.add_le_add h₁ h₂).trans hB

/-- A bound on `rows2 a b` from one on `rowsJ2 a b 0 n` (`h`). -/
theorem rows2_le_of_rowsJ2 (a b : ℕ) {B : ℕ} (h : rowsJ2 a b 0 n ≤ B) : rows2 a b ≤ B := by
  rw [rows2_eq_rowsJ2]; exact h

/-- If `total2 < K` in the natural numbers, then `total2/K < 1` in the reals. -/
theorem total2_div_lt (htot : total2 < K) : (total2 : ℝ) / K < 1 := by
  rw [div_lt_one K_pos']
  exact_mod_cast htot

/-! ### The refined costs -/

theorem cost2_of_dec {i j : ℕ} (hc : cand i j = true) (hd : dec i j = true) : cost2 i j = refcost i j := by
  simp [cost2, hc, hd]

theorem cost2_of_not_dec {i j : ℕ} (hc : cand i j = true) (hd : dec i j = false) :
    cost2 i j = bound2 (e i) (e j) - sub2 i j := by
  simp [cost2, hc, hd]

theorem cost2_of_not_cand {i j : ℕ} (hc : cand i j = false) : cost2 i j = 0 := by
  simp [cost2, hc]

/-- `sub2` as a `Finset` sum. -/
theorem sub2_eq (i j : ℕ) :
    sub2 i j = if reg2 i j then ∑ k ∈ Finset.range n, (if keep i j k then keepK i j k else 0) else 0 := by
  simp only [sub2, sumTo_eq]

/-- A dropped candidate cell's refined cost is at least its bound less `sub2`, in the reals. -/
theorem cost2_ge {i j : ℕ} (hc : cand i j = true) (hd : dec i j = false) :
    (bound2 (e i) (e j) : ℝ) - sub2 i j ≤ cost2 i j := by
  rw [cost2_of_not_dec hc hd]
  have h : bound2 (e i) (e j) ≤ bound2 (e i) (e j) - sub2 i j + sub2 i j := by omega
  have h' : ((bound2 (e i) (e j) : ℕ) : ℝ) ≤ ((bound2 (e i) (e j) - sub2 i j : ℕ) : ℝ) + sub2 i j := by
    exact_mod_cast h
  linarith

variable [GridOK]

/-- On a grid with `GridOK`, on a cell `k` that `keep` passes below `(i, j)`, `DEN − e_i − e_j − e_k` is positive, with
no truncation. -/
theorem keep_gamma {i j k : ℕ} (hk : keep i j k = true) :
    e i + e j + e k < DEN ∧ ((DEN - e i - e j - e k : ℕ) : ℝ) = (DEN : ℝ) - e i - e j - e k := by
  simp only [keep, Bool.and_eq_true, decide_eq_true_eq] at hk
  have hH := H_pos
  have h1 : e i + e j + e k < DEN := by have := hk.1.2; omega
  refine ⟨h1, ?_⟩
  have h2 : e i ≤ DEN := by omega
  have h3 : e j ≤ DEN - e i := by omega
  have h4 : e k ≤ DEN - e i - e j := by omega
  rw [Nat.cast_sub h4, Nat.cast_sub h3, Nat.cast_sub h2]

/-- **The kept share's bound.** On a grid with `GridOK`, on a cell `k` that `keep` passes below `(i, j)`, `keepK/K` is
at most
`H³·DEN/((e_i + H)(e_j + H)(e_k + H)(DEN − e_i − e_j − e_k))`. -/
theorem keepK_le {i j k : ℕ} (hk : keep i j k = true) :
    (keepK i j k : ℝ) / K ≤
      (H : ℝ) ^ 3 * DEN / (((e i : ℝ) + H) * ((e j : ℝ) + H) * ((e k : ℝ) + H) * ((DEN : ℝ) - e i - e j - e k)) := by
  obtain ⟨hlt, hcast⟩ := keep_gamma hk
  have hK := K_pos'
  have hg : (0 : ℝ) < (DEN : ℝ) - e i - e j - e k := by
    have : ((e i + e j + e k : ℕ) : ℝ) < DEN := by exact_mod_cast hlt
    push_cast at this
    linarith
  set d : ℕ := (e i + H) * (e j + H) * (e k + H) * (DEN - e i - e j - e k) with hd
  have hdR : (d : ℝ) = ((e i : ℝ) + H) * ((e j : ℝ) + H) * ((e k : ℝ) + H) * ((DEN : ℝ) - e i - e j - e k) := by
    rw [hd]; push_cast [hcast]; ring
  have hH' : (0 : ℝ) < H := by exact_mod_cast H_pos
  have hd0 : (0 : ℝ) < d := by
    rw [hdR]
    have a1 : (0 : ℝ) < (e i : ℝ) + H := by have : (0 : ℝ) ≤ e i := Nat.cast_nonneg _; linarith
    have a2 : (0 : ℝ) < (e j : ℝ) + H := by have : (0 : ℝ) ≤ e j := Nat.cast_nonneg _; linarith
    have a3 : (0 : ℝ) < (e k : ℝ) + H := by have : (0 : ℝ) ≤ e k := Nat.cast_nonneg _; linarith
    exact mul_pos (mul_pos (mul_pos a1 a2) a3) hg
  have hfl : ((K * H ^ 3 * DEN / d : ℕ) : ℝ) ≤ ((K * H ^ 3 * DEN : ℕ) : ℝ) / d := Nat.cast_div_le
  unfold keepK
  rw [← hd, div_le_iff₀ hK]
  calc ((K * H ^ 3 * DEN / d : ℕ) : ℝ) ≤ ((K * H ^ 3 * DEN : ℕ) : ℝ) / d := hfl
    _ = (H : ℝ) ^ 3 * DEN / (((e i : ℝ) + H) * ((e j : ℝ) + H) * ((e k : ℝ) + H) * ((DEN : ℝ) - e i - e j - e k)) *
          K := by rw [hdR]; push_cast; ring

end

end SieveCert

#print axioms SieveCert.total2_eq
#print axioms SieveCert.rows2_eq_rowsJ2
#print axioms SieveCert.total2_eq_rows2_full
#print axioms SieveCert.rows2_le_of_split
#print axioms SieveCert.rowsJ2_le_of_split
#print axioms SieveCert.rows2_le_of_rowsJ2
#print axioms SieveCert.total2_div_lt
#print axioms SieveCert.cost2_ge
#print axioms SieveCert.keepK_le
