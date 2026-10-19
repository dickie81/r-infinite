/-
# Round 604: comparisons of a family's primes (milestone M5)

Plain statements. A comparison `Cmp K` is `0 ≤ c(m) + Σ_i e_i log x_i`, or `0 <` when it is strict, with
coefficients at most `1` in absolute value and a pivot `i` with `e_i = ±1`. Each kind below comes with a lemma that
says what it means for `x_i ≥ 1` (the `_holds` lemmas):

* `gt`: `x_i > x_{i'}`; `ge`, `lt`: `x_i ≥ b` and `x_i < b`, for `b > 0`;
* `prodLe`, `prodGt`: `∏_{i∈s} x_i ≤ b` and `> b`, for `b > 0`, pivoted at `i₀ ∈ s`;
* `rough`: `x_i ≤ minFac m`, for `m ≥ 2`; `rangeLo`, `rangeHi`: `b < m∏_i x_i` and `m∏_i x_i ≤ b`, for `b > 0`, `m ≥ 1`;
* `lift`: a comparison of the first `j` coordinates, as one of `K ≥ j`.

These are the comparisons of `SieveFamily.typeII_sharp`'s families, `frontier/linnik/SIEVE-ROUTE.md` §13's M4, in
the kinds that Proposition 6's stops need. The file imports only Mathlib.
-/
import Mathlib

open Real Finset

namespace SieveCmp

/-- A comparison of a family: `0 ≤ c(m) + Σ_i e_i log x_i`, or `0 <` when `strict`, with a pivot `i` of coefficient
`±1` and coefficients at most `1` in absolute value. -/
structure Cmp (K : ℕ) where
  c : ℕ → ℝ
  e : Fin K → ℝ
  strict : Bool
  piv : Fin K
  hpiv : e piv = 1 ∨ e piv = -1
  he : ∀ i, |e i| ≤ 1

variable {K : ℕ}

/-- The comparison's form `c(m) + Σ_i e_i log x_i`. -/
noncomputable def Cmp.form (C : Cmp K) (m : ℕ) (x : Fin K → ℕ) : ℝ := C.c m + ∑ i, C.e i * Real.log (x i)

/-- The comparison holds: `0 < form` if strict, `0 ≤ form` otherwise. -/
def Cmp.holds (C : Cmp K) (m : ℕ) (x : Fin K → ℕ) : Prop :=
  if C.strict then 0 < C.form m x else 0 ≤ C.form m x

theorem Cmp.spec (C : Cmp K) (m : ℕ) (x : Fin K → ℕ) :
    (0 < C.form m x → C.holds m x) ∧ (C.holds m x → 0 ≤ C.form m x) := by
  unfold Cmp.holds
  split_ifs
  · exact ⟨id, le_of_lt⟩
  · exact ⟨le_of_lt, id⟩

/-! ### Sums of logarithms against indicator coefficients -/

theorem sum_single (i : Fin K) (x : Fin K → ℕ) :
    ∑ t, (if t = i then (1 : ℝ) else 0) * Real.log (x t) = Real.log (x i) := by
  simp [ite_mul]

theorem sum_set (s : Finset (Fin K)) (x : Fin K → ℕ) (hx : ∀ i, 1 ≤ x i) :
    ∑ t, (if t ∈ s then (1 : ℝ) else 0) * Real.log (x t) = Real.log (∏ t ∈ s, (x t : ℝ)) := by
  rw [Real.log_prod (fun t _ => by have := hx t; positivity)]
  simp [ite_mul, Finset.sum_ite_mem]

/-! ### The basic comparisons, and what they say on tuples of positive integers -/

/-- `x_i > x_{i'}`, for `i ≠ i'`. -/
noncomputable def gt (i i' : Fin K) (h : i ≠ i') : Cmp K where
  c := fun _ => 0
  e := fun t => (if t = i then 1 else 0) - (if t = i' then 1 else 0)
  strict := true
  piv := i
  hpiv := Or.inl (by simp [h])
  he := fun t => by
    by_cases h1 : t = i
    · subst h1; simp [h]
    · by_cases h2 : t = i'
      · subst h2; simp [h1]
      · simp [h1, h2]

theorem gt_holds {i i' : Fin K} (h : i ≠ i') (m : ℕ) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (gt i i' h).holds m x ↔ x i' < x i := by
  have hpos : ∀ t, (0 : ℝ) < x t := fun t => by exact_mod_cast hx t
  unfold Cmp.holds Cmp.form gt
  simp only [ite_true, zero_add, sub_mul, Finset.sum_sub_distrib, sum_single, sub_pos]
  rw [Real.log_lt_log_iff (hpos _) (hpos _), Nat.cast_lt]

/-- `x_i ≥ b` for a constant `b > 0`. -/
noncomputable def ge (i : Fin K) (b : ℝ) : Cmp K where
  c := fun _ => -Real.log b
  e := fun t => if t = i then 1 else 0
  strict := false
  piv := i
  hpiv := Or.inl (by simp)
  he := fun t => by split_ifs <;> simp

theorem ge_holds (i : Fin K) {b : ℝ} (hb : 0 < b) (m : ℕ) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (ge i b).holds m x ↔ b ≤ x i := by
  have hpos : (0 : ℝ) < x i := by exact_mod_cast hx i
  unfold Cmp.holds Cmp.form ge
  simp only [Bool.false_eq_true, ite_false, sum_single, neg_add_eq_sub, sub_nonneg]
  exact Real.log_le_log_iff hb hpos

/-- `x_i < b` for a constant `b > 0`. -/
noncomputable def lt (i : Fin K) (b : ℝ) : Cmp K where
  c := fun _ => Real.log b
  e := fun t => -(if t = i then 1 else 0)
  strict := true
  piv := i
  hpiv := Or.inr (by simp)
  he := fun t => by split_ifs <;> simp

theorem lt_holds (i : Fin K) {b : ℝ} (hb : 0 < b) (m : ℕ) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (lt i b).holds m x ↔ (x i : ℝ) < b := by
  have hpos : (0 : ℝ) < x i := by exact_mod_cast hx i
  unfold Cmp.holds Cmp.form lt
  simp only [ite_true, neg_mul, Finset.sum_neg_distrib, sum_single, ← sub_eq_add_neg, sub_pos]
  exact Real.log_lt_log_iff hpos hb

/-- `∏_{i∈s} x_i ≤ b` for a constant `b > 0`, with pivot `i₀ ∈ s`. -/
noncomputable def prodLe (s : Finset (Fin K)) {i₀ : Fin K} (hi₀ : i₀ ∈ s) (b : ℝ) : Cmp K where
  c := fun _ => Real.log b
  e := fun t => -(if t ∈ s then 1 else 0)
  strict := false
  piv := i₀
  hpiv := Or.inr (by simp [hi₀])
  he := fun t => by split_ifs <;> simp

theorem prodLe_holds (s : Finset (Fin K)) {i₀ : Fin K} (hi₀ : i₀ ∈ s) {b : ℝ} (hb : 0 < b) (m : ℕ)
    {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) : (prodLe s hi₀ b).holds m x ↔ ∏ t ∈ s, (x t : ℝ) ≤ b := by
  have hpos : (0 : ℝ) < ∏ t ∈ s, (x t : ℝ) := Finset.prod_pos fun t _ => by exact_mod_cast hx t
  unfold Cmp.holds Cmp.form prodLe
  simp only [Bool.false_eq_true, ite_false, neg_mul, Finset.sum_neg_distrib, sum_set s x hx, ← sub_eq_add_neg,
    sub_nonneg]
  exact Real.log_le_log_iff hpos hb

/-- `∏_{i∈s} x_i > b` for a constant `b > 0`, with pivot `i₀ ∈ s`. -/
noncomputable def prodGt (s : Finset (Fin K)) {i₀ : Fin K} (hi₀ : i₀ ∈ s) (b : ℝ) : Cmp K where
  c := fun _ => -Real.log b
  e := fun t => if t ∈ s then 1 else 0
  strict := true
  piv := i₀
  hpiv := Or.inl (by simp [hi₀])
  he := fun t => by split_ifs <;> simp

theorem prodGt_holds (s : Finset (Fin K)) {i₀ : Fin K} (hi₀ : i₀ ∈ s) {b : ℝ} (hb : 0 < b) (m : ℕ)
    {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) : (prodGt s hi₀ b).holds m x ↔ b < ∏ t ∈ s, (x t : ℝ) := by
  have hpos : (0 : ℝ) < ∏ t ∈ s, (x t : ℝ) := Finset.prod_pos fun t _ => by exact_mod_cast hx t
  unfold Cmp.holds Cmp.form prodGt
  simp only [ite_true, sum_set s x hx, neg_add_eq_sub, sub_pos]
  exact Real.log_lt_log_iff hb hpos

/-- `x_i ≤ minFac m`: no prime factor of `m` below `x_i`, for `m ≥ 2`. -/
noncomputable def rough (i : Fin K) : Cmp K where
  c := fun m => Real.log (Nat.minFac m)
  e := fun t => -(if t = i then 1 else 0)
  strict := false
  piv := i
  hpiv := Or.inr (by simp)
  he := fun t => by split_ifs <;> simp

theorem rough_holds (i : Fin K) (m : ℕ) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (rough i).holds m x ↔ x i ≤ Nat.minFac m := by
  have hpos : (0 : ℝ) < x i := by exact_mod_cast hx i
  have hmf : (0 : ℝ) < Nat.minFac m := by exact_mod_cast Nat.minFac_pos m
  unfold Cmp.holds Cmp.form rough
  simp only [Bool.false_eq_true, ite_false, neg_mul, Finset.sum_neg_distrib, sum_single, ← sub_eq_add_neg,
    sub_nonneg]
  rw [Real.log_le_log_iff hpos hmf, Nat.cast_le]

/-- `b < m∏_i x_i`, for a constant `b > 0` and at least one coordinate. -/
noncomputable def rangeLo (b : ℝ) : Cmp (K + 1) where
  c := fun m => Real.log m - Real.log b
  e := fun _ => 1
  strict := true
  piv := 0
  hpiv := Or.inl rfl
  he := fun _ => by simp

theorem rangeLo_holds {b : ℝ} (hb : 0 < b) {m : ℕ} (hm : 1 ≤ m) {x : Fin (K + 1) → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (rangeLo b).holds m x ↔ b < (m : ℝ) * ∏ t, (x t : ℝ) := by
  have hpos : (0 : ℝ) < ∏ t, (x t : ℝ) := Finset.prod_pos fun t _ => by exact_mod_cast hx t
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : ∑ t, (1 : ℝ) * Real.log (x t) = Real.log (∏ t, (x t : ℝ)) := by
    rw [Real.log_prod (fun t _ => by have := hx t; positivity)]
    simp
  unfold Cmp.holds Cmp.form rangeLo
  simp only [ite_true]
  rw [hlog, sub_add_eq_add_sub, ← Real.log_mul hm0.ne' hpos.ne', sub_pos]
  exact Real.log_lt_log_iff hb (mul_pos hm0 hpos)

/-- `m∏_i x_i ≤ b`, for a constant `b > 0` and at least one coordinate. -/
noncomputable def rangeHi (b : ℝ) : Cmp (K + 1) where
  c := fun m => Real.log b - Real.log m
  e := fun _ => -1
  strict := false
  piv := 0
  hpiv := Or.inr rfl
  he := fun _ => by simp

theorem rangeHi_holds {b : ℝ} (hb : 0 < b) {m : ℕ} (hm : 1 ≤ m) {x : Fin (K + 1) → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (rangeHi b).holds m x ↔ (m : ℝ) * ∏ t, (x t : ℝ) ≤ b := by
  have hpos : (0 : ℝ) < ∏ t, (x t : ℝ) := Finset.prod_pos fun t _ => by exact_mod_cast hx t
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : ∑ t, (-1 : ℝ) * Real.log (x t) = -Real.log (∏ t, (x t : ℝ)) := by
    rw [Real.log_prod (fun t _ => by have := hx t; positivity), ← Finset.sum_neg_distrib]
    simp
  unfold Cmp.holds Cmp.form rangeHi
  simp only [Bool.false_eq_true, ite_false]
  rw [hlog, ← sub_eq_add_neg, sub_sub, ← Real.log_mul hm0.ne' hpos.ne', sub_nonneg]
  exact Real.log_le_log_iff (mul_pos hm0 hpos) hb

/-- A comparison on the first `j` coordinates, as one on `K ≥ j`. -/
noncomputable def lift {j : ℕ} (C : Cmp j) (h : j ≤ K) : Cmp K where
  c := C.c
  e := fun t => if ht : (t : ℕ) < j then C.e ⟨t, ht⟩ else 0
  strict := C.strict
  piv := Fin.castLE h C.piv
  hpiv := by simp [C.piv.isLt, C.hpiv]
  he := fun t => by split_ifs <;> simp [C.he]

theorem lift_holds {j : ℕ} (C : Cmp j) (h : j ≤ K) (m : ℕ) (x : Fin K → ℕ) :
    (lift C h).holds m x ↔ C.holds m (fun i => x (Fin.castLE h i)) := by
  have hsum : ∑ t : Fin K, (if ht : (t : ℕ) < j then C.e ⟨t, ht⟩ else 0) * Real.log (x t) =
      ∑ i : Fin j, C.e i * Real.log (x (Fin.castLE h i)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t : Fin K => (t : ℕ) < j)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun t : Fin K => ¬ (t : ℕ) < j))
      (fun t ht => by simp [(Finset.mem_filter.1 ht).2]), add_zero]
    have himg : (Finset.univ.filter (fun t : Fin K => (t : ℕ) < j)) = Finset.univ.image (Fin.castLE h) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro ht
        exact ⟨⟨t, ht⟩, Fin.ext rfl⟩
      · rintro ⟨i, rfl⟩
        exact i.isLt
    rw [himg, Finset.sum_image (fun a _ b _ hab => Fin.castLE_injective h hab)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [i.isLt]
  unfold Cmp.holds Cmp.form lift
  rw [hsum]

end SieveCmp
