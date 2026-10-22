/-
# Round 624: the certificate's rows cut by columns (the lemmas)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

`rowsJ_eq`: `rowsJ a b j₀ j₁` is the double sum of the costs over `a ≤ i < b` and `j₀ ≤ j < j₁` (as `rows_eq`);
`rows_eq_rowsJ`: `rows a b = rowsJ a b 0 n`; `rowsJ_split` and `rows_split`: for `j₀ ≤ j₁ ≤ j₂`, `rowsJ a b j₀ j₂` is
`rowsJ a b j₀ j₁ + rowsJ a b j₁ j₂`, and for `a ≤ b ≤ c`, `rows a c = rows a b + rows b c`; `total_eq_rows_full`:
`total = rows 0 n`. A certificate's bound then follows from its parts' bounds one step at a time, with no large term
(`rows_le_of_split`, `rowsJ_le_of_split`: a bound from two pieces' bounds whose sum is at most it; `rows_le_of_rowsJ`:
a bound on `rows a b` from one on `rowsJ a b 0 n`). (Round 632: it gave all three the first description, and the
imports' reason below omitted `total_eq`; review of round 625, F2.)

The file imports `SieveCert.lean` (for `sumTo_eq`, `rows_eq` and `total_eq`) and `SieveCertColsDefs.lean`.
-/
import SieveCert
import SieveCertColsDefs

namespace SieveCert

section

variable [Grid]

/-- `rowsJ a b j₀ j₁` is the double sum of the costs over `a ≤ i < b` and `j₀ ≤ j < j₁`. -/
theorem rowsJ_eq (a b j₀ j₁ : ℕ) :
    rowsJ a b j₀ j₁ = ∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico j₀ j₁, cost i j := by
  rw [rowsJ, sumTo_eq, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sumTo_eq, Finset.sum_Ico_eq_sum_range]

/-- `rows a b` is `rowsJ a b 0 n`. -/
theorem rows_eq_rowsJ (a b : ℕ) : rows a b = rowsJ a b 0 n := by
  rw [rows_eq, rowsJ_eq, Finset.range_eq_Ico]

/-- For `j₀ ≤ j₁ ≤ j₂` (`h₁`, `h₂`), `rowsJ a b j₀ j₂ = rowsJ a b j₀ j₁ + rowsJ a b j₁ j₂`. -/
theorem rowsJ_split (a b : ℕ) {j₀ j₁ j₂ : ℕ} (h₁ : j₀ ≤ j₁) (h₂ : j₁ ≤ j₂) :
    rowsJ a b j₀ j₂ = rowsJ a b j₀ j₁ + rowsJ a b j₁ j₂ := by
  simp only [rowsJ_eq, ← Finset.sum_add_distrib, Finset.sum_Ico_consecutive _ h₁ h₂]

/-- For `a ≤ b ≤ c` (`hab`, `hbc`), `rows a c = rows a b + rows b c`. -/
theorem rows_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) : rows a c = rows a b + rows b c := by
  simp only [rows_eq, Finset.sum_Ico_consecutive _ hab hbc]

/-- The total is `rows 0 n`. -/
theorem total_eq_rows_full : total = rows 0 n := by
  rw [total_eq, rows_eq, Finset.range_eq_Ico]

/-- A bound on `rows a c` from bounds on `rows a b` (`h₁`) and `rows b c` (`h₂`), for `a ≤ b ≤ c` (`hab`, `hbc`),
with the bounds' sum at most `B` (`hB`). -/
theorem rows_le_of_split {a b c B₁ B₂ B : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (h₁ : rows a b ≤ B₁) (h₂ : rows b c ≤ B₂)
    (hB : B₁ + B₂ ≤ B) : rows a c ≤ B := by
  rw [rows_split hab hbc]; exact (Nat.add_le_add h₁ h₂).trans hB

/-- A bound on `rowsJ a b j₀ j₂` from bounds on `rowsJ a b j₀ j₁` (`h₁`) and `rowsJ a b j₁ j₂` (`h₂`), for
`j₀ ≤ j₁ ≤ j₂` (`h₀₁`, `h₁₂`), with the bounds' sum at most `B` (`hB`). -/
theorem rowsJ_le_of_split (a b : ℕ) {j₀ j₁ j₂ B₁ B₂ B : ℕ} (h₀₁ : j₀ ≤ j₁) (h₁₂ : j₁ ≤ j₂)
    (h₁ : rowsJ a b j₀ j₁ ≤ B₁) (h₂ : rowsJ a b j₁ j₂ ≤ B₂) (hB : B₁ + B₂ ≤ B) : rowsJ a b j₀ j₂ ≤ B := by
  rw [rowsJ_split a b h₀₁ h₁₂]; exact (Nat.add_le_add h₁ h₂).trans hB

/-- A bound on `rows a b` from one on `rowsJ a b 0 n` (`h`). -/
theorem rows_le_of_rowsJ (a b : ℕ) {B : ℕ} (h : rowsJ a b 0 n ≤ B) : rows a b ≤ B := by
  rw [rows_eq_rowsJ]; exact h

end

end SieveCert

#print axioms SieveCert.rowsJ_eq
#print axioms SieveCert.rows_eq_rowsJ
#print axioms SieveCert.rowsJ_split
#print axioms SieveCert.rows_split
#print axioms SieveCert.total_eq_rows_full
#print axioms SieveCert.rows_le_of_split
#print axioms SieveCert.rowsJ_le_of_split
#print axioms SieveCert.rows_le_of_rowsJ
