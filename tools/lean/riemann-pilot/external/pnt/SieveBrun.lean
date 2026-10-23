/-
# Round 604: Brun's sieve in product form, abstractly (milestone M5)

Plain statements. For a finite set `T` and weights `x`, `esym T x m` is the elementary symmetric sum
`e_m(T, x) = Σ_{s ⊆ T, |s| = m} ∏_{p∈s} x_p`, and `trunc T x k` is the truncated alternating sum
`F_k(T, x) = Σ_{i ≤ k} (−1)^i e_i(T, x)`.

* `bonferroni`: for `0 ≤ x_p ≤ 1` on `T`, `F_k` lies on the side `(−1)^k` of `∏_{p∈T} (1 − x_p)`, within `e_{k+1}`.
* `fundamental`: the fundamental lemma in product form. Sift a finite set `C` by finite families `T_j` of moduli,
  `j` in a finite type `ι`, truncating the inclusion–exclusion of `T_j` at the even level `k_j ≥ 1` for the upper
  sieve and at `k_j − 1` for the lower. If every count `#{n ∈ C : p ∣ n for p ∈ s_j}` with `s_j ⊆ T_j` is
  `X ∏_j ∏_{p∈s_j} g(p)` within `R`, where `X ≥ 0` and `0 ≤ g ≤ 1` on each `T_j`, then the sifted count is
  `X ∏_j ∏_{p∈T_j} (1 − g(p))` within `X Σ_j e_{k_j}(T_j, g) ∏_{i≠j} F_{k_i}(T_i, g)` plus
  `(#ι + 1)R ∏_j Σ_{i≤k_j} C(#T_j, i)`.
* `gap_le`: with `Σ_{T_j} g ≤ C₀` and `∏_{T_j} (1 − g) ≥ c₀ > 0`, that gap is at most `V` times
  `c₀⁻¹ Σ_j C₀^{k_j}/k_j!` times `∏_i (1 + C₀^{k_i+1}/((k_i + 1)! c₀))`, where `V = ∏_j ∏_{T_j} (1 − g)`.
* `sum_levels_le`: for `C ≥ 0` and `2C² ≤ (k + 1)(k + 2)`, `Σ_{j<J} C^{k+2j}/(k + 2j)! ≤ 2C^k/k!`, uniformly in `J`.

This is the fundamental lemma (T3) of `frontier/linnik/SIEVE-ROUTE.md` §13's M5, by Brun's sieve in product form.

The proof:

* `esym_insert`, `trunc_insert`, `bonferroni`: induction on `T`.
* `prod_lower`: if `lo_j ≤ ρ_j ≤ hi_j` and `ρ_j ≥ 0`, then `∏ hi − Σ_j (hi_j − lo_j) ∏_{i≠j} hi_i ≤ ∏ ρ`. The sifted
  indicator is `∏_j ρ_j`, with the upper truncation as `hi_j` and the lower as `lo_j`.
* `sum_prod_weights`, `sum_prod_weights_sub`: a product of weights `Σ_b c(b) ∏_{p∈S(b)} 1[p ∣ n]`, summed over `C`, is
  a sum of counts, and against the model `X ∏ g` its error is at most `R` times the sum of the `|c|`.
* `factorial_mul_esym_le`: `m!·e_m(T, x) ≤ (Σ_{p∈T} x_p)^m` for `x ≥ 0`, for `gap_le`.

The file imports only Mathlib.
-/
import Mathlib

open Finset

namespace SieveBrun

variable {α : Type*}

/-! ### Elementary symmetric sums and Bonferroni's inequalities -/

/-- The elementary symmetric sum `e_m(T, x) = Σ_{s ⊆ T, |s| = m} ∏_{p∈s} x_p`. -/
noncomputable def esym (T : Finset α) (x : α → ℝ) (m : ℕ) : ℝ :=
  ∑ s ∈ T.powersetCard m, ∏ p ∈ s, x p

/-- The truncated alternating sum `F_k(T, x) = Σ_{i ≤ k} (−1)^i e_i(T, x)`. -/
noncomputable def trunc (T : Finset α) (x : α → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), (-1) ^ i * esym T x i

theorem esym_zero (T : Finset α) (x : α → ℝ) : esym T x 0 = 1 := by
  simp [esym]

theorem esym_empty_succ (x : α → ℝ) (m : ℕ) : esym (∅ : Finset α) x (m + 1) = 0 := by
  rw [esym, Finset.powersetCard_eq_empty.2 (by simp), Finset.sum_empty]

theorem esym_nonneg {T : Finset α} {x : α → ℝ} (hx : ∀ p ∈ T, 0 ≤ x p) (m : ℕ) : 0 ≤ esym T x m :=
  Finset.sum_nonneg fun _ hs => Finset.prod_nonneg fun p hp =>
    hx p ((Finset.mem_powersetCard.1 hs).1 hp)

/-- `e_{m+1}(T ∪ {a}) = e_{m+1}(T) + x_a e_m(T)` for `a ∉ T`. -/
theorem esym_insert [DecidableEq α] {T : Finset α} {a : α} (ha : a ∉ T) (x : α → ℝ) (m : ℕ) :
    esym (insert a T) x (m + 1) = esym T x (m + 1) + x a * esym T x m := by
  rw [esym, Finset.powersetCard_succ_insert ha, Finset.sum_union]
  · rw [Finset.sum_image]
    · rw [esym, esym, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun s hs => ?_
      have has : a ∉ s := fun h => ha ((Finset.mem_powersetCard.1 hs).1 h)
      rw [Finset.prod_insert has]
    · intro s hs t ht hst
      have has : a ∉ s := fun h => ha ((Finset.mem_powersetCard.1 (Finset.mem_coe.1 hs)).1 h)
      have hat : a ∉ t := fun h => ha ((Finset.mem_powersetCard.1 (Finset.mem_coe.1 ht)).1 h)
      rw [← Finset.erase_insert has, ← Finset.erase_insert hat, hst]
  · rw [Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hs'
    exact ha ((Finset.mem_powersetCard.1 hs).1 (Finset.mem_insert_self a t))

theorem trunc_zero (T : Finset α) (x : α → ℝ) : trunc T x 0 = 1 := by
  simp [trunc, esym_zero]

theorem trunc_succ (T : Finset α) (x : α → ℝ) (k : ℕ) :
    trunc T x (k + 1) = trunc T x k + (-1) ^ (k + 1) * esym T x (k + 1) := by
  rw [trunc, Finset.sum_range_succ, ← trunc]

/-- `F_{k+1}(T ∪ {a}) = F_{k+1}(T) − x_a F_k(T)` for `a ∉ T`. -/
theorem trunc_insert [DecidableEq α] {T : Finset α} {a : α} (ha : a ∉ T) (x : α → ℝ) (k : ℕ) :
    trunc (insert a T) x (k + 1) = trunc T x (k + 1) - x a * trunc T x k := by
  induction k with
  | zero =>
    rw [trunc_succ, trunc_succ, trunc_zero, trunc_zero, esym_insert ha, esym_zero]
    ring
  | succ k ih =>
    rw [trunc_succ (insert a T), ih, esym_insert ha, trunc_succ T x (k + 1), trunc_succ T x k]
    ring

/-- **Bonferroni's inequalities** for `0 ≤ x_p ≤ 1`: the truncation `F_k` lies on the side `(−1)^k` of
`∏_{p∈T} (1 − x_p)`, within `e_{k+1}`. -/
theorem bonferroni [DecidableEq α] (T : Finset α) {x : α → ℝ} (hx0 : ∀ p ∈ T, 0 ≤ x p) (hx1 : ∀ p ∈ T, x p ≤ 1)
    (k : ℕ) :
    0 ≤ (-1) ^ k * (trunc T x k - ∏ p ∈ T, (1 - x p)) ∧
      (-1) ^ k * (trunc T x k - ∏ p ∈ T, (1 - x p)) ≤ esym T x (k + 1) := by
  induction T using Finset.induction_on generalizing k with
  | empty =>
    have ht : trunc (∅ : Finset α) x k = 1 := by
      induction k with
      | zero => exact trunc_zero _ _
      | succ k ih => rw [trunc_succ, ih, esym_empty_succ]; ring
    rw [ht, Finset.prod_empty, esym_empty_succ]
    simp
  | insert a T ha ih =>
    have hx0' : ∀ p ∈ T, 0 ≤ x p := fun p hp => hx0 p (Finset.mem_insert_of_mem hp)
    have hx1' : ∀ p ∈ T, x p ≤ 1 := fun p hp => hx1 p (Finset.mem_insert_of_mem hp)
    have ha0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self a T)
    have ha1 : x a ≤ 1 := hx1 a (Finset.mem_insert_self a T)
    obtain ⟨h1, h2⟩ := ih hx0' hx1' k
    have he := esym_nonneg hx0' k
    have he' := esym_nonneg hx0' (k + 1)
    -- `(−1)^k D(T ∪ {a}, k) = (1 − x_a)(−1)^k D(T, k) + x_a e_k(T)`
    have key : (-1) ^ k * (trunc (insert a T) x k - ∏ p ∈ insert a T, (1 - x p)) =
        (1 - x a) * ((-1) ^ k * (trunc T x k - ∏ p ∈ T, (1 - x p))) + x a * esym T x k := by
      rw [Finset.prod_insert ha]
      cases k with
      | zero =>
        rw [trunc_zero, trunc_zero, esym_zero]
        ring
      | succ k =>
        rw [trunc_insert ha, trunc_succ T x k]
        have hsq : ((-1 : ℝ) ^ (k + 1)) * (-1) ^ (k + 1) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; norm_num
        linear_combination (x a) * hsq * esym T x (k + 1)
    rw [key, esym_insert ha]
    constructor
    · have : 0 ≤ (1 - x a) * ((-1) ^ k * (trunc T x k - ∏ p ∈ T, (1 - x p))) :=
        mul_nonneg (by linarith) h1
      nlinarith [mul_nonneg ha0 he]
    · have : (1 - x a) * ((-1) ^ k * (trunc T x k - ∏ p ∈ T, (1 - x p))) ≤ esym T x (k + 1) := by
        calc (1 - x a) * ((-1) ^ k * (trunc T x k - ∏ p ∈ T, (1 - x p))) ≤ 1 * esym T x (k + 1) :=
              mul_le_mul (by linarith) h2 h1 zero_le_one
          _ = esym T x (k + 1) := one_mul _
      linarith

/-- `m!·e_m(T, x) ≤ (Σ_{p∈T} x_p)^m` for `x ≥ 0`. -/
theorem factorial_mul_esym_le [DecidableEq α] {T : Finset α} {x : α → ℝ} (hx : ∀ p ∈ T, 0 ≤ x p) (m : ℕ) :
    (m.factorial : ℝ) * esym T x m ≤ (∑ p ∈ T, x p) ^ m := by
  induction T using Finset.induction_on generalizing m with
  | empty =>
    cases m with
    | zero => simp [esym_zero]
    | succ m => rw [esym_empty_succ]; simp
  | insert a T ha ih =>
    have hx' : ∀ p ∈ T, 0 ≤ x p := fun p hp => hx p (Finset.mem_insert_of_mem hp)
    have ha0 : 0 ≤ x a := hx a (Finset.mem_insert_self a T)
    have hS : 0 ≤ ∑ p ∈ T, x p := Finset.sum_nonneg hx'
    rw [Finset.sum_insert ha]
    cases m with
    | zero => simp [esym_zero]
    | succ m =>
      rw [esym_insert ha]
      have h1 := ih hx' (m + 1)
      have h2 := ih hx' m
      -- `S^{m+1} + (m+1)x_aS^m ≤ (S + x_a)^{m+1}`
      have hbern : (∑ p ∈ T, x p) ^ (m + 1) + (m + 1) * x a * (∑ p ∈ T, x p) ^ m ≤
          (x a + ∑ p ∈ T, x p) ^ (m + 1) := by
        rw [add_comm (x a), add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
        simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
        have hrest : 0 ≤ ∑ i ∈ Finset.range m, (∑ p ∈ T, x p) ^ i * x a ^ (m + 1 - i) * ((m + 1).choose i : ℝ) :=
          Finset.sum_nonneg fun i _ => by positivity
        have hc : ((m + 1).choose m : ℝ) = m + 1 := by
          rw [Nat.choose_succ_self_right]; push_cast; ring
        rw [hc, show m + 1 - m = 1 by omega, pow_one]
        nlinarith
      have hfac : ((m + 1).factorial : ℝ) = (m + 1) * m.factorial := by
        rw [Nat.factorial_succ]; push_cast; ring
      calc ((m + 1).factorial : ℝ) * (esym T x (m + 1) + x a * esym T x m)
          = ((m + 1).factorial : ℝ) * esym T x (m + 1) + (m + 1) * x a * ((m.factorial : ℝ) * esym T x m) := by
            rw [hfac]; ring
        _ ≤ (∑ p ∈ T, x p) ^ (m + 1) + (m + 1) * x a * (∑ p ∈ T, x p) ^ m := by
            have : 0 ≤ ((m : ℝ) + 1) * x a := by positivity
            nlinarith [mul_le_mul_of_nonneg_left h2 this]
        _ ≤ (x a + ∑ p ∈ T, x p) ^ (m + 1) := hbern

/-! ### The product inequality -/

/-- If `lo_j ≤ ρ_j ≤ hi_j` and `ρ_j ≥ 0`, then `∏ hi − Σ_j (hi_j − lo_j) ∏_{i≠j} hi_i ≤ ∏ ρ`. -/
theorem prod_lower {ι : Type*} [DecidableEq ι] (s : Finset ι) (ρ lo hi : ι → ℝ) (h0 : ∀ j ∈ s, 0 ≤ ρ j)
    (hlo : ∀ j ∈ s, lo j ≤ ρ j) (hhi : ∀ j ∈ s, ρ j ≤ hi j) :
    ∏ j ∈ s, hi j - ∑ j ∈ s, (hi j - lo j) * ∏ i ∈ s.erase j, hi i ≤ ∏ j ∈ s, ρ j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h0' : ∀ j ∈ s, 0 ≤ ρ j := fun j hj => h0 j (Finset.mem_insert_of_mem hj)
    have hlo' : ∀ j ∈ s, lo j ≤ ρ j := fun j hj => hlo j (Finset.mem_insert_of_mem hj)
    have hhi' : ∀ j ∈ s, ρ j ≤ hi j := fun j hj => hhi j (Finset.mem_insert_of_mem hj)
    have IH := ih h0' hlo' hhi'
    have hhi0 : ∀ j ∈ s, 0 ≤ hi j := fun j hj => (h0' j hj).trans (hhi' j hj)
    have hP : 0 ≤ ∏ j ∈ s, hi j := Finset.prod_nonneg hhi0
    have hΔ : 0 ≤ ∑ j ∈ s, (hi j - lo j) * ∏ i ∈ s.erase j, hi i :=
      Finset.sum_nonneg fun j hj => mul_nonneg (by linarith [hlo' j hj, hhi' j hj])
        (Finset.prod_nonneg fun i hi' => hhi0 i (Finset.mem_of_mem_erase hi'))
    have hsum : ∑ j ∈ s, (hi j - lo j) * ∏ i ∈ (insert a s).erase j, hi i =
        hi a * ∑ j ∈ s, (hi j - lo j) * ∏ i ∈ s.erase j, hi i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hja : a ≠ j := fun h => ha (h ▸ hj)
      rw [Finset.erase_insert_of_ne hja, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha, hsum]
    have hρa := h0 a (Finset.mem_insert_self a s)
    have hloa := hlo a (Finset.mem_insert_self a s)
    have hhia := hhi a (Finset.mem_insert_self a s)
    have e1 : 0 ≤ ρ a * (∏ j ∈ s, ρ j - (∏ j ∈ s, hi j - ∑ j ∈ s, (hi j - lo j) * ∏ i ∈ s.erase j, hi i)) :=
      mul_nonneg hρa (by linarith)
    have e2 : 0 ≤ (ρ a - lo a) * ∏ j ∈ s, hi j := mul_nonneg (by linarith) hP
    have e3 : 0 ≤ (hi a - ρ a) * ∑ j ∈ s, (hi j - lo j) * ∏ i ∈ s.erase j, hi i := mul_nonneg (by linarith) hΔ
    nlinarith

/-! ### Sieve weights summed over a finite set -/

/-- The indicator `1[p ∣ n]`. -/
def ind (n p : ℕ) : ℝ := if p ∣ n then 1 else 0

theorem ind_nonneg (n p : ℕ) : 0 ≤ ind n p := by unfold ind; split_ifs <;> norm_num

theorem ind_le_one (n p : ℕ) : ind n p ≤ 1 := by unfold ind; split_ifs <;> norm_num

/-- **Product weights over a finite set.** For weights `w_j(n) = Σ_{b∈F_j} c_j(b) ∏_{p∈S_j(b)} 1[p ∣ n]`,
`Σ_{n∈C} ∏_j w_j(n) = Σ_σ (∏_j c_j(σ_j))·#{n ∈ C : p ∣ n for all p ∈ S_j(σ_j) and all j}`. -/
theorem sum_prod_weights {ι β : Type*} [Fintype ι] [DecidableEq ι] (C : Finset ℕ) (F : ι → Finset β)
    (S : ι → β → Finset ℕ) (c : ι → β → ℝ) :
    ∑ n ∈ C, ∏ j, ∑ b ∈ F j, c j b * ∏ p ∈ S j b, ind n p =
      ∑ σ ∈ Fintype.piFinset F, (∏ j, c j (σ j)) * ((C.filter fun n => ∀ j, ∀ p ∈ S j (σ j), p ∣ n).card : ℝ) := by
  simp_rw [Finset.prod_univ_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  have h1 : ∀ j, ∏ p ∈ S j (σ j), ind n p = if ∀ p ∈ S j (σ j), p ∣ n then 1 else 0 := fun j => by
    unfold ind; exact Finset.prod_boole
  simp_rw [h1]
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, true_imp_iff]
  split_ifs <;> simp

/-- The same, against a model `X ∏ g` of the counts with error at most `R`. -/
theorem sum_prod_weights_sub {ι β : Type*} [Fintype ι] [DecidableEq ι] (C : Finset ℕ) (F : ι → Finset β)
    (S : ι → β → Finset ℕ) (c : ι → β → ℝ) (X : ℝ) (g : ℕ → ℝ) {R : ℝ}
    (hR : ∀ σ ∈ Fintype.piFinset F,
      |((C.filter fun n => ∀ j, ∀ p ∈ S j (σ j), p ∣ n).card : ℝ) - X * ∏ j, ∏ p ∈ S j (σ j), g p| ≤ R) :
    |∑ n ∈ C, ∏ j, ∑ b ∈ F j, c j b * ∏ p ∈ S j b, ind n p - X * ∏ j, ∑ b ∈ F j, c j b * ∏ p ∈ S j b, g p| ≤
      R * ∏ j, ∑ b ∈ F j, |c j b| := by
  rw [sum_prod_weights, Finset.prod_univ_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.prod_univ_sum,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ hσ => ?_)
  have e : (∏ j, c j (σ j)) * ((C.filter fun n => ∀ j, ∀ p ∈ S j (σ j), p ∣ n).card : ℝ) -
      X * ∏ j, (c j (σ j) * ∏ p ∈ S j (σ j), g p) =
      (∏ j, c j (σ j)) * (((C.filter fun n => ∀ j, ∀ p ∈ S j (σ j), p ∣ n).card : ℝ) -
        X * ∏ j, ∏ p ∈ S j (σ j), g p) := by
    rw [Finset.prod_mul_distrib]; ring
  rw [e, abs_mul, Finset.abs_prod, mul_comm]
  exact mul_le_mul_of_nonneg_right (hR σ hσ) (Finset.prod_nonneg fun j _ => abs_nonneg _)

/-! ### The fundamental lemma, abstractly -/

theorem trunc_sub_pred {T : Finset α} {y : α → ℝ} {k : ℕ} (hk : Even k) (hk1 : 1 ≤ k) :
    trunc T y k - trunc T y (k - 1) = esym T y k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, trunc_succ, hk.neg_one_pow]
  ring

theorem trunc_bounds [DecidableEq α] {T : Finset α} {y : α → ℝ} (hy0 : ∀ p ∈ T, 0 ≤ y p) (hy1 : ∀ p ∈ T, y p ≤ 1)
    {k : ℕ} (hk : Even k) (hk1 : 1 ≤ k) :
    trunc T y (k - 1) ≤ ∏ p ∈ T, (1 - y p) ∧ ∏ p ∈ T, (1 - y p) ≤ trunc T y k := by
  have h1 := (bonferroni T hy0 hy1 k).1
  have h2 := (bonferroni T hy0 hy1 (k - 1)).1
  rw [hk.neg_one_pow] at h1
  have hodd : Odd (k - 1) := Nat.Even.sub_odd hk1 hk odd_one
  rw [hodd.neg_one_pow] at h2
  constructor <;> linarith

/-- The index set of the truncation `F_k`: pairs `(i, s)` with `i ≤ k` and `s ⊆ T`, `|s| = i`. -/
def Ftr (T : Finset ℕ) (k : ℕ) : Finset (Σ _ : ℕ, Finset ℕ) :=
  (Finset.range (k + 1)).sigma fun i => T.powersetCard i

/-- The index set of `e_k`. -/
def Fes (T : Finset ℕ) (k : ℕ) : Finset (Σ _ : ℕ, Finset ℕ) :=
  ({k} : Finset ℕ).sigma fun i => T.powersetCard i

theorem trunc_eq_weight (T : Finset ℕ) (y : ℕ → ℝ) (k : ℕ) :
    trunc T y k = ∑ b ∈ Ftr T k, (-1 : ℝ) ^ b.1 * ∏ p ∈ b.2, y p := by
  rw [trunc, Ftr, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [esym, Finset.mul_sum]

theorem esym_eq_weight (T : Finset ℕ) (y : ℕ → ℝ) (k : ℕ) :
    esym T y k = ∑ b ∈ Fes T k, (1 : ℝ) * ∏ p ∈ b.2, y p := by
  rw [Fes, Finset.sum_sigma, Finset.sum_singleton, esym]
  simp

theorem abs_Ftr (T : Finset ℕ) (k : ℕ) :
    ∑ b ∈ Ftr T k, |(-1 : ℝ) ^ b.1| = ∑ i ∈ Finset.range (k + 1), (T.card.choose i : ℝ) := by
  rw [Ftr, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Finset.card_powersetCard]

theorem abs_Fes (T : Finset ℕ) (k : ℕ) : ∑ _b ∈ Fes T k, |(1 : ℝ)| = (T.card.choose k : ℝ) := by
  rw [Fes, Finset.sum_sigma, Finset.sum_singleton]
  simp [Finset.card_powersetCard]

theorem mem_Ftr_sub {T : Finset ℕ} {k : ℕ} {b : Σ _ : ℕ, Finset ℕ} (hb : b ∈ Ftr T k) : b.2 ⊆ T := by
  rw [Ftr, Finset.mem_sigma] at hb
  exact (Finset.mem_powersetCard.1 hb.2).1

theorem mem_Fes_sub {T : Finset ℕ} {k : ℕ} {b : Σ _ : ℕ, Finset ℕ} (hb : b ∈ Fes T k) : b.2 ⊆ T := by
  rw [Fes, Finset.mem_sigma] at hb
  exact (Finset.mem_powersetCard.1 hb.2).1

theorem choose_le_sum_choose (n k : ℕ) :
    (n.choose k : ℝ) ≤ ∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ) :=
  Finset.single_le_sum (f := fun i => (n.choose i : ℝ)) (fun _ _ => Nat.cast_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_self k))

/-- **The fundamental lemma in product form, abstractly.** Sift a finite set `C` by finite families
`T_j` of moduli, truncating the inclusion–exclusion of `T_j` at the even level `k_j ≥ 1` for the upper sieve and at
`k_j − 1` for the lower. If every count `#{n ∈ C : p ∣ n for p ∈ s_j}` with `s_j ⊆ T_j` is `X ∏_j ∏_{p∈s_j} g(p)`
within `R`, where `X ≥ 0` and `0 ≤ g ≤ 1` on each `T_j`, then the sifted count is `X ∏_j ∏_{p∈T_j} (1 − g(p))` within
`X Σ_j e_{k_j}(T_j, g) ∏_{i≠j} F_{k_i}(T_i, g)` plus `(#ι + 1)R ∏_j Σ_{i≤k_j} C(#T_j, i)`. -/
theorem fundamental {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Finset ℕ) (T : ι → Finset ℕ) (k : ι → ℕ)
    (hk : ∀ j, Even (k j)) (hk1 : ∀ j, 1 ≤ k j) {X : ℝ} (hX : 0 ≤ X) {g : ℕ → ℝ}
    (hg0 : ∀ j, ∀ p ∈ T j, 0 ≤ g p) (hg1 : ∀ j, ∀ p ∈ T j, g p ≤ 1) {R : ℝ}
    (hR : ∀ s : ι → Finset ℕ, (∀ j, s j ⊆ T j) →
      |((C.filter fun n => ∀ j, ∀ p ∈ s j, p ∣ n).card : ℝ) - X * ∏ j, ∏ p ∈ s j, g p| ≤ R) :
    |((C.filter fun n => ∀ j, ∀ p ∈ T j, ¬ p ∣ n).card : ℝ) - X * ∏ j, ∏ p ∈ T j, (1 - g p)| ≤
      X * ∑ j, esym (T j) g (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T i) g (k i) +
        (Fintype.card ι + 1) * R * ∏ j, ∑ i ∈ Finset.range (k j + 1), ((T j).card.choose i : ℝ) := by
  set N := ∏ j, ∑ i ∈ Finset.range (k j + 1), ((T j).card.choose i : ℝ) with hN
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) (hR (fun _ => ∅) fun _ => Finset.empty_subset _)
  have hN0 : 0 ≤ N := Finset.prod_nonneg fun j _ => Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  -- the sifted count as a sum of products
  have hcard : ((C.filter fun n => ∀ j, ∀ p ∈ T j, ¬ p ∣ n).card : ℝ) =
      ∑ n ∈ C, ∏ j, ∏ p ∈ T j, (1 - ind n p) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h1 : ∀ j, ∏ p ∈ T j, (1 - ind n p) = if ∀ p ∈ T j, ¬ p ∣ n then 1 else 0 := fun j => by
      rw [← Finset.prod_boole]
      refine Finset.prod_congr rfl fun p _ => ?_
      unfold ind; split_ifs <;> norm_num
    simp_rw [h1]
    rw [Finset.prod_boole]
    simp only [Finset.mem_univ, true_imp_iff]
    split_ifs <;> simp
  -- pointwise bounds
  have hpt : ∀ n, ∀ j, 0 ≤ ∏ p ∈ T j, (1 - ind n p) ∧
      trunc (T j) (ind n) (k j - 1) ≤ ∏ p ∈ T j, (1 - ind n p) ∧
      ∏ p ∈ T j, (1 - ind n p) ≤ trunc (T j) (ind n) (k j) := fun n j => by
    obtain ⟨h1, h2⟩ := trunc_bounds (T := T j) (y := ind n) (fun p _ => ind_nonneg n p)
      (fun p _ => ind_le_one n p) (hk j) (hk1 j)
    exact ⟨Finset.prod_nonneg fun p _ => by linarith [ind_le_one n p], h1, h2⟩
  have hdiff : ∀ (y : ℕ → ℝ) j, trunc (T j) y (k j) - trunc (T j) y (k j - 1) = esym (T j) y (k j) :=
    fun y j => trunc_sub_pred (hk j) (hk1 j)
  -- the upper sum
  set U := ∑ n ∈ C, ∏ j, trunc (T j) (ind n) (k j) with hU
  have hUerr : |U - X * ∏ j, trunc (T j) g (k j)| ≤ R * N := by
    have h := sum_prod_weights_sub C (fun j => Ftr (T j) (k j)) (fun _ b => b.2) (fun _ b => (-1 : ℝ) ^ b.1) X g
      (R := R) (fun σ hσ => hR (fun j => (σ j).2) fun j => mem_Ftr_sub (Fintype.mem_piFinset.1 hσ j))
    simp only [← trunc_eq_weight, abs_Ftr] at h
    exact h
  -- the gap sums
  set Lg : ι → ℝ := fun j₀ => ∑ n ∈ C, esym (T j₀) (ind n) (k j₀) *
    ∏ i ∈ Finset.univ.erase j₀, trunc (T i) (ind n) (k i) with hLg
  have hLerr : ∀ j₀, |Lg j₀ - X * (esym (T j₀) g (k j₀) * ∏ i ∈ Finset.univ.erase j₀, trunc (T i) g (k i))| ≤
      R * N := by
    intro j₀
    have h := sum_prod_weights_sub C (fun j => if j = j₀ then Fes (T j) (k j) else Ftr (T j) (k j))
      (fun _ b => b.2) (fun j b => if j = j₀ then (1 : ℝ) else (-1 : ℝ) ^ b.1) X g (R := R)
      (fun σ hσ => hR (fun j => (σ j).2) fun j => by
        have := Fintype.mem_piFinset.1 hσ j
        split_ifs at this
        · exact mem_Fes_sub this
        · exact mem_Ftr_sub this)
    have hw : ∀ y : ℕ → ℝ, ∏ j, ∑ b ∈ (if j = j₀ then Fes (T j) (k j) else Ftr (T j) (k j)),
        (if j = j₀ then (1 : ℝ) else (-1 : ℝ) ^ b.1) * ∏ p ∈ b.2, y p =
        esym (T j₀) y (k j₀) * ∏ i ∈ Finset.univ.erase j₀, trunc (T i) y (k i) := by
      intro y
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
      congr 1
      · simp only [ite_true]; exact (esym_eq_weight _ _ _).symm
      · refine Finset.prod_congr rfl fun i hi => ?_
        have hij : i ≠ j₀ := Finset.ne_of_mem_erase hi
        simp only [hij, ite_false]
        exact (trunc_eq_weight _ _ _).symm
    have habs : ∏ j, ∑ b ∈ (if j = j₀ then Fes (T j) (k j) else Ftr (T j) (k j)),
        |(if j = j₀ then (1 : ℝ) else (-1 : ℝ) ^ b.1)| ≤ N := by
      rw [hN, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀),
        ← Finset.mul_prod_erase Finset.univ (fun j => ∑ i ∈ Finset.range (k j + 1), ((T j).card.choose i : ℝ))
          (Finset.mem_univ j₀)]
      simp only [ite_true]
      rw [abs_Fes]
      have hrest : ∏ i ∈ Finset.univ.erase j₀, ∑ b ∈ (if i = j₀ then Fes (T i) (k i) else Ftr (T i) (k i)),
          |(if i = j₀ then (1 : ℝ) else (-1 : ℝ) ^ b.1)| =
          ∏ i ∈ Finset.univ.erase j₀, ∑ i' ∈ Finset.range (k i + 1), ((T i).card.choose i' : ℝ) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hij : i ≠ j₀ := Finset.ne_of_mem_erase hi
        simp only [hij, ite_false]
        exact abs_Ftr _ _
      rw [hrest]
      exact mul_le_mul_of_nonneg_right (choose_le_sum_choose _ _)
        (Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun i' _ => Nat.cast_nonneg _)
    simp only [hw] at h
    exact h.trans (mul_le_mul_of_nonneg_left habs hR0)
  -- the count against the upper and lower sums
  have hup : ((C.filter fun n => ∀ j, ∀ p ∈ T j, ¬ p ∣ n).card : ℝ) ≤ U := by
    rw [hcard, hU]
    exact Finset.sum_le_sum fun n _ => Finset.prod_le_prod₀ (fun j _ => (hpt n j).1) fun j _ => (hpt n j).2.2
  have hlow : U - ∑ j, Lg j ≤ ((C.filter fun n => ∀ j, ∀ p ∈ T j, ¬ p ∣ n).card : ℝ) := by
    rw [hcard, hU, hLg]
    simp only
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    have h := prod_lower Finset.univ (fun j => ∏ p ∈ T j, (1 - ind n p)) (fun j => trunc (T j) (ind n) (k j - 1))
      (fun j => trunc (T j) (ind n) (k j)) (fun j _ => (hpt n j).1) (fun j _ => (hpt n j).2.1)
      (fun j _ => (hpt n j).2.2)
    simp only [hdiff] at h
    exact h
  -- the model against the same main terms
  have hV : ∀ j, trunc (T j) g (k j - 1) ≤ ∏ p ∈ T j, (1 - g p) ∧ ∏ p ∈ T j, (1 - g p) ≤ trunc (T j) g (k j) :=
    fun j => trunc_bounds (hg0 j) (hg1 j) (hk j) (hk1 j)
  have hV0 : ∀ j, 0 ≤ ∏ p ∈ T j, (1 - g p) := fun j =>
    Finset.prod_nonneg fun p hp => by linarith [hg1 j p hp]
  have hMup : ∏ j, ∏ p ∈ T j, (1 - g p) ≤ ∏ j, trunc (T j) g (k j) :=
    Finset.prod_le_prod₀ (fun j _ => hV0 j) fun j _ => (hV j).2
  have hMlow : ∏ j, trunc (T j) g (k j) - ∑ j, esym (T j) g (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T i) g (k i) ≤
      ∏ j, ∏ p ∈ T j, (1 - g p) := by
    have h := prod_lower Finset.univ (fun j => ∏ p ∈ T j, (1 - g p)) (fun j => trunc (T j) g (k j - 1))
      (fun j => trunc (T j) g (k j)) (fun j _ => hV0 j) (fun j _ => (hV j).1) (fun j _ => (hV j).2)
    simp only [hdiff] at h
    exact h
  -- combine
  set G := ∑ j, esym (T j) g (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T i) g (k i) with hG
  set P := ∏ j, trunc (T j) g (k j) with hP
  have hLsum : ∑ j, Lg j ≤ X * G + Fintype.card ι * (R * N) := by
    calc ∑ j, Lg j ≤ ∑ j, (X * (esym (T j) g (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T i) g (k i)) + R * N) :=
          Finset.sum_le_sum fun j _ => by linarith [(abs_le.1 (hLerr j)).2]
      _ = X * G + Fintype.card ι * (R * N) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hU1 := abs_le.1 hUerr
  have hXM1 : X * ∏ j, ∏ p ∈ T j, (1 - g p) ≤ X * P := mul_le_mul_of_nonneg_left hMup hX
  have hXM2 : X * P - X * G ≤ X * ∏ j, ∏ p ∈ T j, (1 - g p) := by
    rw [← mul_sub]; exact mul_le_mul_of_nonneg_left hMlow hX
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The relative error -/

/-- For even `k_j`, `0 ≤ g ≤ 1` on each `T_j`, `C₀ ≥ 0` with `Σ_{T_j} g ≤ C₀`, and `∏_{T_j} (1 − g) ≥ c₀ > 0`: the
fundamental lemma's gap is at most `V` times `c₀⁻¹ Σ_j C₀^{k_j}/k_j!` times `∏_i (1 + C₀^{k_i+1}/((k_i + 1)! c₀))`,
where `V = ∏_j ∏_{T_j} (1 − g)`. -/
theorem gap_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → Finset ℕ) (k : ι → ℕ) (hk : ∀ j, Even (k j))
    {g : ℕ → ℝ} (hg0 : ∀ j, ∀ p ∈ T j, 0 ≤ g p) (hg1 : ∀ j, ∀ p ∈ T j, g p ≤ 1) {C₀ c₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hc₀ : 0 < c₀) (hC : ∀ j, ∑ p ∈ T j, g p ≤ C₀) (hV : ∀ j, c₀ ≤ ∏ p ∈ T j, (1 - g p)) :
    ∑ j, esym (T j) g (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T i) g (k i) ≤
      (∏ j, ∏ p ∈ T j, (1 - g p)) * (c₀⁻¹ * ∑ j, C₀ ^ k j / (k j).factorial) *
        ∏ i, (1 + C₀ ^ (k i + 1) / ((k i + 1).factorial * c₀)) := by
  set V : ι → ℝ := fun j => ∏ p ∈ T j, (1 - g p) with hVdef
  set ε : ι → ℝ := fun i => C₀ ^ (k i + 1) / ((k i + 1).factorial * c₀) with hεdef
  have hV0 : ∀ j, 0 < V j := fun j => lt_of_lt_of_le hc₀ (hV j)
  have hs0 : ∀ j, 0 ≤ ∑ p ∈ T j, g p := fun j => Finset.sum_nonneg (hg0 j)
  have hε0 : ∀ i, 0 ≤ ε i := fun i => by positivity
  -- `e_k ≤ C₀^k/k!`
  have he : ∀ j (m : ℕ), esym (T j) g m ≤ C₀ ^ m / m.factorial := fun j m => by
    have h1 := factorial_mul_esym_le (hg0 j) m
    have h2 : (∑ p ∈ T j, g p) ^ m ≤ C₀ ^ m := pow_le_pow_left₀ (hs0 j) (hC j) m
    rw [le_div_iff₀ (by positivity)]
    linarith
  -- `F_k ≤ V(1 + ε)`
  have ht : ∀ i, trunc (T i) g (k i) ≤ V i * (1 + ε i) := fun i => by
    have h1 := (bonferroni (T i) (hg0 i) (hg1 i) (k i)).2
    rw [(hk i).neg_one_pow, one_mul] at h1
    have h2 := he i (k i + 1)
    have h3 : C₀ ^ (k i + 1) / (k i + 1).factorial ≤ V i * ε i := by
      rw [hεdef]
      simp only
      rw [show V i * (C₀ ^ (k i + 1) / ((k i + 1).factorial * c₀)) =
        (V i / c₀) * (C₀ ^ (k i + 1) / (k i + 1).factorial) by field_simp]
      have hVc : 1 ≤ V i / c₀ := by rw [le_div_iff₀ hc₀]; simpa using hV i
      have : 0 ≤ C₀ ^ (k i + 1) / (k i + 1).factorial := by positivity
      nlinarith
    linarith
  have ht0 : ∀ i, 0 ≤ trunc (T i) g (k i) := fun i => by
    have h1 := (bonferroni (T i) (hg0 i) (hg1 i) (k i)).1
    rw [(hk i).neg_one_pow, one_mul] at h1
    linarith [hV0 i]
  -- the products over `i ≠ j`
  have hprod : ∀ j, ∏ i ∈ Finset.univ.erase j, trunc (T i) g (k i) ≤
      ((∏ i, V i) / c₀) * ∏ i, (1 + ε i) := fun j => by
    have h1 : ∏ i ∈ Finset.univ.erase j, trunc (T i) g (k i) ≤ ∏ i ∈ Finset.univ.erase j, (V i * (1 + ε i)) :=
      Finset.prod_le_prod₀ (fun i _ => ht0 i) fun i _ => ht i
    rw [Finset.prod_mul_distrib] at h1
    have h2 : ∏ i ∈ Finset.univ.erase j, V i ≤ (∏ i, V i) / c₀ := by
      rw [← Finset.mul_prod_erase Finset.univ V (Finset.mem_univ j), le_div_iff₀ hc₀]
      have hpos : 0 ≤ ∏ i ∈ Finset.univ.erase j, V i := Finset.prod_nonneg fun i _ => (hV0 i).le
      nlinarith [hV j]
    have h3 : ∏ i ∈ Finset.univ.erase j, (1 + ε i) ≤ ∏ i, (1 + ε i) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => 1 + ε i) (Finset.mem_univ j)]
      have hpos : 0 ≤ ∏ i ∈ Finset.univ.erase j, (1 + ε i) := Finset.prod_nonneg fun i _ => by linarith [hε0 i]
      nlinarith [hε0 j]
    have h4 : 0 ≤ ∏ i ∈ Finset.univ.erase j, (1 + ε i) := Finset.prod_nonneg fun i _ => by linarith [hε0 i]
    have h5 : 0 ≤ (∏ i, V i) / c₀ := div_nonneg (Finset.prod_nonneg fun i _ => (hV0 i).le) hc₀.le
    calc _ ≤ (∏ i ∈ Finset.univ.erase j, V i) * ∏ i ∈ Finset.univ.erase j, (1 + ε i) := h1
      _ ≤ ((∏ i, V i) / c₀) * ∏ i, (1 + ε i) := mul_le_mul h2 h3 h4 h5
  have hP0 : 0 ≤ ((∏ i, V i) / c₀) * ∏ i, (1 + ε i) :=
    mul_nonneg (div_nonneg (Finset.prod_nonneg fun i _ => (hV0 i).le) hc₀.le)
      (Finset.prod_nonneg fun i _ => by linarith [hε0 i])
  calc ∑ j, esym (T j) g (k j) * ∏ i ∈ Finset.univ.erase j, trunc (T i) g (k i)
      ≤ ∑ j, C₀ ^ k j / (k j).factorial * (((∏ i, V i) / c₀) * ∏ i, (1 + ε i)) :=
        Finset.sum_le_sum fun j _ => mul_le_mul (he j (k j)) (hprod j)
          (Finset.prod_nonneg fun i _ => ht0 i) (by positivity)
    _ = (∏ i, V i) * (c₀⁻¹ * ∑ j, C₀ ^ k j / (k j).factorial) * ∏ i, (1 + ε i) := by
        rw [← Finset.sum_mul]; field_simp

/-! ### The levels `k + 2j` -/

/-- For `C ≥ 0` and `2C² ≤ (k + 1)(k + 2)`, `Σ_{j<J} C^{k+2j}/(k + 2j)! ≤ 2C^k/k!`, uniformly in `J`. -/
theorem sum_levels_le {C : ℝ} (hC : 0 ≤ C) {k : ℕ} (hk : 2 * C ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (J : ℕ) :
    ∑ j ∈ Finset.range J, C ^ (k + 2 * j) / (k + 2 * j).factorial ≤ 2 * (C ^ k / k.factorial) := by
  set a : ℕ → ℝ := fun j => C ^ (k + 2 * j) / (k + 2 * j).factorial with ha
  have ha0 : ∀ j, 0 ≤ a j := fun j => by positivity
  have hstep : ∀ j, a (j + 1) ≤ a j / 2 := fun j => by
    have hrec : a (j + 1) = a j * (C ^ 2 / ((((k + 2 * j : ℕ) : ℝ) + 1) * (((k + 2 * j : ℕ) : ℝ) + 2))) := by
      rw [ha]
      simp only
      rw [show k + 2 * (j + 1) = (k + 2 * j) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    have hfac : C ^ 2 / ((((k + 2 * j : ℕ) : ℝ) + 1) * (((k + 2 * j : ℕ) : ℝ) + 2)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      push_cast
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [hrec]
    nlinarith [ha0 j]
  have hgeom : ∀ j, a j ≤ a 0 * (1 / 2) ^ j := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      calc a (j + 1) ≤ a j / 2 := hstep j
        _ ≤ a 0 * (1 / 2) ^ j / 2 := by linarith
        _ = a 0 * (1 / 2) ^ (j + 1) := by rw [pow_succ]; ring
  calc ∑ j ∈ Finset.range J, a j ≤ ∑ j ∈ Finset.range J, a 0 * (1 / 2) ^ j := Finset.sum_le_sum fun j _ => hgeom j
    _ = a 0 * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
    _ ≤ a 0 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le J) (ha0 0)
    _ = 2 * (C ^ k / k.factorial) := by rw [ha]; simp; ring

/-- For `b_j ≥ 0`, `∏ (1 + b_j) ≤ exp(Σ b_j)`. -/
theorem prod_one_add_le_exp {ι : Type*} (s : Finset ι) (b : ι → ℝ) (hb : ∀ j ∈ s, 0 ≤ b j) :
    ∏ j ∈ s, (1 + b j) ≤ Real.exp (∑ j ∈ s, b j) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun j hj => by linarith [hb j hj]) fun j _ => by
    have := Real.add_one_le_exp (b j); linarith

end SieveBrun
