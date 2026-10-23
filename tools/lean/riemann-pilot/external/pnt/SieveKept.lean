/-
# Round 707: the kept parts of the dropped cells of depth 2

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. `P` is the decomposition's parameters (`SieveBuch.Par`) on a grid of the certificate
(`SieveCert.Grid`). A dropped term of depth 2, `S(A_{p₁p₂}, p₂)` for `(p₁, p₂)` in the cell `(i, j)`, counts the
`n = p₁p₂m ∈ (N₁, N₂]` whose cofactor `m` has no prime factor below `p₂`. Its kept part below the cell `k` counts the
`n = p₁p₂q₁q₂` with `q₁` a prime of the cell `k`, `q₂` a prime, `q₁ < q₂`, and `q₁, q₂ ≠ p₁`.

* `KC`, `keptAt`, `Kk`, `Kp2`: the condition on `(q₁, q₂)`, the kept part below `(p₁, p₂)`,
  `Σ_{q₁ ∈ cellP x k} Σ_{q₂ ≤ N₂ prime} g(p₁p₂q₁q₂)[KC]`, its sum over the cell's pairs `(p₁, p₂)` (the family
  `S2c i j`), and the kept parts below `(i, j)` over the cells `k` that `SieveCert.keep` passes.
* `prime_pair_eq`, `cell_unique`: two products of two primes `a < b` and `c < d` that agree have `a = c` and `b = d`;
  a prime in two cells of the grid has them equal.
* `Kp2_le`: for `x > 1` and `g ≥ 0`, `Kp2 g i j ≤ I g (S2c i j)`: the kept parts are terms of the dropped term, each
  counted once, since `n` and `(p₁, p₂)` determine `q₁ < q₂`, and `q₁` its cell.
* `KS`, `mem_KS`: the kept part's four primes sorted, `p₁` at `a`, `q₁` at `b`, `p₂` last, as a family of `14` atoms:
  strictly decreasing, `p₁ ∈ [z₀, z_top)` in the cell `i`, `p₂ ≥ z₀` in the cell `j`, `q₁` in the cell `k`, and
  `N₁ < ∏ ≤ N₂`.
* `Kk_eq`: for `x > 1` and a cell `k` above the cell `j` (`e_j + H ≤ e_k`), `Kk g i j k` is the sum of `famE g` over the
  three sorted families: `p₁ > q₂ > q₁ > p₂` (`KS 0 2`), `q₂ > p₁ > q₁ > p₂` (`KS 1 2`) and `q₂ > q₁ > p₁ > p₂`
  (`KS 2 1`).

This is the partition of a dropped term by the factorization of its rough part that `frontier/linnik/SIEVE-ROUTE.md`
§28 describes: the kept parts are disjoint subsets of the dropped term's `n`, so their `A`-count is at most the term's;
sorted, each is an exact product of a chain of four primes, which `SieveExact.T0_spec` evaluates when some subset of
its primes has its product in the window.

The file imports `SieveExact.lean` and `SieveCert2.lean`.
-/
import SieveExact
import SieveCert2

open Real Finset SieveFamily SieveChain SieveDecomp SieveExact
open SieveCert (V DEN H U1 U2 cand dec keep reg2 surelyEval cell)

namespace SieveBuch

namespace Par

open Classical

variable (P : Par) [SieveCert.Grid]

/-! ### The kept parts -/

/-- The condition on `(q₁, q₂)` below `(p₁, p₂)`: `q₁ < q₂`, both distinct from `p₁`, and `N₁ < p₁p₂q₁q₂ ≤ N₂`. -/
def KC (p₁ p₂ q₁ q₂ : ℕ) : Prop :=
  q₁ < q₂ ∧ q₁ ≠ p₁ ∧ q₂ ≠ p₁ ∧ P.N₁ < p₁ * p₂ * q₁ * q₂ ∧ p₁ * p₂ * q₁ * q₂ ≤ P.N₂

/-- The kept part below `(p₁, p₂)` of the cell `k`: `Σ_{q₁ ∈ cellP x k} Σ_{q₂ ≤ N₂ prime} g(p₁p₂q₁q₂)[KC]`. -/
noncomputable def keptAt (g : ℕ → ℝ) (k p₁ p₂ : ℕ) : ℝ :=
  ∑ q₁ ∈ SieveRough.cellP P.x k, ∑ q₂ ∈ SieveTypeIIU.primesLe P.N₂,
    if P.KC p₁ p₂ q₁ q₂ then g (p₁ * p₂ * q₁ * q₂) else 0

/-- The kept part of the cell `k` below the cell `(i, j)`. -/
noncomputable def Kk (g : ℕ → ℝ) (i j k : ℕ) : ℝ :=
  ∑ rt ∈ famSet 2 P.N₂ (P.S2c i j), P.keptAt g k (rt 0) (rt 1)

/-- The kept parts below the cell `(i, j)`: the cells `k` that `keep` passes. -/
noncomputable def Kp2 (g : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ k ∈ range SieveCert.n, if keep i j k = true then P.Kk g i j k else 0

theorem keptAt_nonneg {g : ℕ → ℝ} (hg : ∀ m, 0 ≤ g m) (k p₁ p₂ : ℕ) : 0 ≤ P.keptAt g k p₁ p₂ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> first | exact hg _ | exact le_rfl

theorem Kk_nonneg {g : ℕ → ℝ} (hg : ∀ m, 0 ≤ g m) (i j k : ℕ) : 0 ≤ P.Kk g i j k :=
  Finset.sum_nonneg fun _ _ => P.keptAt_nonneg hg _ _ _

theorem Kp2_nonneg {g : ℕ → ℝ} (hg : ∀ m, 0 ≤ g m) (i j : ℕ) : 0 ≤ P.Kp2 g i j :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> first | exact P.Kk_nonneg hg _ _ _ | exact le_rfl

/-! ### Two facts about primes -/

omit [SieveCert.Grid] in
/-- Two products of two primes `a < b` and `c < d` that agree have `a = c` and `b = d`. -/
theorem prime_pair_eq {a b c d : ℕ} (ha : a.Prime) (hc : c.Prime) (hd : d.Prime) (hab : a < b)
    (hcd : c < d) (h : a * b = c * d) : a = c ∧ b = d := by
  have hac : a = c ∨ a = d := by
    have : a ∣ c * d := ⟨b, h.symm⟩
    rcases (Nat.Prime.dvd_mul ha).1 this with h1 | h1
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq ha hc).1 h1)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq ha hd).1 h1)
  rcases hac with rfl | rfl
  · exact ⟨rfl, Nat.eq_of_mul_eq_mul_left ha.pos h⟩
  · exfalso
    have : b = c := by
      have h' : a * b = a * c := by rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left ha.pos h'
    omega

/-- For `x > 1`, a prime in the cells `k` and `k'` of the grid has `k = k'`. -/
theorem cell_unique {x : ℝ} (hx : 1 < x) {k k' p : ℕ} (h : InC x k p) (h' : InC x k' p) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := rpow_cell_le hx.le (e_add_H_le_of_lt hlt)
    linarith [h.2, h'.1]
  · have := rpow_cell_le hx.le (e_add_H_le_of_lt hlt)
    linarith [h'.2, h.1]

theorem mem_cellP_iff {x : ℝ} {k p : ℕ} : p ∈ SieveRough.cellP x k ↔ p.Prime ∧ InC x k p := by
  rw [SieveRough.cellP, SieveRough.mem_primesIn]
  rfl

/-! ### The kept parts are terms of the dropped term -/

/-- **One pair's kept parts.** For `x > 1`, `g ≥ 0` and primes `p₂ < p₁` with `p₂` in the cell `j`, the kept parts
below `(p₁, p₂)` over the cells that `keep` passes are at most `Σ_n g(n)[p₁p₂ ∣ n, n free of primes below p₂]`. -/
theorem keptAt_sum_le (hx : 1 < P.x) {g : ℕ → ℝ} (hg : ∀ m, 0 ≤ g m) {i j p₁ p₂ : ℕ} (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (h21 : p₂ < p₁) (hC₂ : InC P.x j p₂) :
    ∑ k ∈ range SieveCert.n, (if keep i j k = true then P.keptAt g k p₁ p₂ else 0) ≤
      ∑ m ∈ Ioc P.N₁ P.N₂, g m * (if p₁ * p₂ ∣ m ∧ SieveTree.rough p₂ m then 1 else 0) := by
  set D := ((range SieveCert.n).filter (fun k => keep i j k = true)).sigma
    (fun k => ((SieveRough.cellP P.x k) ×ˢ (SieveTypeIIU.primesLe P.N₂)).filter
      (fun pq => P.KC p₁ p₂ pq.1 pq.2)) with hD
  set E := (Ioc P.N₁ P.N₂).filter (fun m => p₁ * p₂ ∣ m ∧ SieveTree.rough p₂ m) with hE
  have hL : ∑ k ∈ range SieveCert.n, (if keep i j k = true then P.keptAt g k p₁ p₂ else 0) =
      ∑ t ∈ D, g (p₁ * p₂ * t.2.1 * t.2.2) := by
    rw [hD, Finset.sum_sigma, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · unfold keptAt
      rw [Finset.sum_filter, Finset.sum_product]
    · rfl
  have hR : ∑ m ∈ Ioc P.N₁ P.N₂, g m * (if p₁ * p₂ ∣ m ∧ SieveTree.rough p₂ m then 1 else 0) = ∑ m ∈ E, g m := by
    rw [hE, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  rw [hL, hR]
  have hinj : Set.InjOn (fun t : (Σ _ : ℕ, ℕ × ℕ) => p₁ * p₂ * t.2.1 * t.2.2) D := by
    rintro ⟨k, q₁, q₂⟩ ht ⟨k', q₁', q₂'⟩ ht' hft
    rw [Finset.mem_coe] at ht ht'
    simp only [hD, Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, Finset.mem_product] at ht ht'
    obtain ⟨-, ⟨hq₁, hq₂⟩, hK⟩ := ht
    obtain ⟨-, ⟨hq₁', hq₂'⟩, hK'⟩ := ht'
    rw [mem_cellP_iff] at hq₁ hq₁'
    have hp : 0 < p₁ * p₂ := Nat.mul_pos hp₁.pos hp₂.pos
    have h12 : q₁ * q₂ = q₁' * q₂' := by
      have hft' : p₁ * p₂ * q₁ * q₂ = p₁ * p₂ * q₁' * q₂' := hft
      have : p₁ * p₂ * (q₁ * q₂) = p₁ * p₂ * (q₁' * q₂') := by
        calc p₁ * p₂ * (q₁ * q₂) = p₁ * p₂ * q₁ * q₂ := by ring
          _ = p₁ * p₂ * q₁' * q₂' := hft'
          _ = p₁ * p₂ * (q₁' * q₂') := by ring
      exact Nat.eq_of_mul_eq_mul_left hp this
    obtain ⟨rfl, rfl⟩ := prime_pair_eq hq₁.1 hq₁'.1 (SieveTypeIIU.mem_primesLe.1 hq₂').2 hK.1 hK'.1 h12
    obtain rfl := cell_unique hx hq₁.2 hq₁'.2
    rfl
  calc ∑ t ∈ D, g (p₁ * p₂ * t.2.1 * t.2.2)
      = ∑ m ∈ D.image (fun t : (Σ _ : ℕ, ℕ × ℕ) => p₁ * p₂ * t.2.1 * t.2.2), g m := (Finset.sum_image hinj).symm
    _ ≤ ∑ m ∈ E, g m := Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hg m
  intro m hm
  obtain ⟨⟨k, q₁, q₂⟩, ht, rfl⟩ := Finset.mem_image.1 hm
  simp only [hD, Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, Finset.mem_product] at ht
  obtain ⟨⟨-, hkeep⟩, ⟨hq₁, hq₂⟩, hK⟩ := ht
  rw [mem_cellP_iff] at hq₁
  have hq₂p := (SieveTypeIIU.mem_primesLe.1 hq₂).2
  obtain ⟨h12, -, -, hlo, hhi⟩ := hK
  -- `q₁ > p₂`: the cell `k` lies above the cell `j`
  have hjk : SieveCert.e j + H ≤ SieveCert.e k := by
    simp only [keep, Bool.and_eq_true, decide_eq_true_eq] at hkeep
    exact hkeep.1.1
  have hq₁p₂ : p₂ < q₁ := by
    have : (p₂ : ℝ) < q₁ := lt_of_lt_of_le hC₂.2 ((rpow_cell_le hx.le hjk).trans hq₁.2.1)
    exact_mod_cast this
  rw [hE, Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨hlo, hhi⟩, ⟨q₁ * q₂, by ring⟩, fun r hr hrp hrd => ?_⟩
  -- every prime factor of `p₁p₂q₁q₂` is one of the four, each at least `p₂`
  rcases (Nat.Prime.dvd_mul hrp).1 hrd with h | h
  · rcases (Nat.Prime.dvd_mul hrp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hrp).1 h with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hrp hp₁).1 h] at hr; omega
      · rw [(Nat.prime_dvd_prime_iff_eq hrp hp₂).1 h] at hr; omega
    · rw [(Nat.prime_dvd_prime_iff_eq hrp hq₁.1).1 h] at hr; omega
  · rw [(Nat.prime_dvd_prime_iff_eq hrp hq₂p).1 h] at hr; omega

/-- **The kept parts are terms of the dropped term.** For `x > 1` and `g ≥ 0`, the kept parts below the cell `(i, j)`
are at most the dropped term `I g (S2c i j)`. -/
theorem Kp2_le (hx : 1 < P.x) {g : ℕ → ℝ} (hg : ∀ m, 0 ≤ g m) (i j : ℕ) : P.Kp2 g i j ≤ P.I g (P.S2c i j) := by
  unfold Kp2 Kk I famI
  have hswap : ∑ k ∈ range SieveCert.n, (if keep i j k = true then
        ∑ rt ∈ famSet 2 P.N₂ (P.S2c i j), P.keptAt g k (rt 0) (rt 1) else 0) =
      ∑ rt ∈ famSet 2 P.N₂ (P.S2c i j), ∑ k ∈ range SieveCert.n,
        (if keep i j k = true then P.keptAt g k (rt 0) (rt 1) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [hswap]
  refine Finset.sum_le_sum fun rt hrt => ?_
  obtain ⟨hc, -, hCj⟩ := P.facts_S2c hrt
  have hp : ∀ t, (rt t).Prime := fun t => ((mem_famSet.1 hrt).1 t).2
  have h10 : rt 1 < rt 0 := hc.1 (show (0 : Fin 2) < 1 by decide)
  have h := P.keptAt_sum_le hx hg (i := i) (hp 0) (hp 1) h10 hCj
  rw [Fin.prod_univ_two]
  exact h

/-! ### The kept parts sorted -/

/-- The kept part's four primes sorted, `p₁` at `a`, `q₁` at `b`, `p₂` last: strictly decreasing, `p₁ ∈ [z₀, z_top)`
in the cell `i`, `p₂ ≥ z₀` in the cell `j`, `q₁` in the cell `k`, and `N₁ < ∏ ≤ N₂`. -/
noncomputable def KS (a b : Fin 4) (i j k : ℕ) : List (Atom 4) :=
  [Atom.ltVar 0 1, Atom.ltVar 1 2, Atom.ltVar 2 3, Atom.ge a P.z₀, Atom.lt a P.ztop, Atom.ge 3 P.z₀,
    Atom.prodGt Finset.univ P.N₁, Atom.prodLe Finset.univ P.N₂] ++ cellA a P.x i ++ cellA 3 P.x j ++ cellA b P.x k

theorem mem_KS {a b : Fin 4} {i j k Y : ℕ} {rt : Fin 4 → ℕ} :
    rt ∈ famSet 4 Y (P.KS a b i j k) ↔ (∀ t, rt t ≤ Y ∧ (rt t).Prime) ∧ (rt 1 < rt 0 ∧ rt 2 < rt 1 ∧ rt 3 < rt 2) ∧
      (P.z₀ ≤ rt a ∧ rt a < P.ztop ∧ P.z₀ ≤ rt 3) ∧ (P.N₁ < ∏ t, rt t ∧ ∏ t, rt t ≤ P.N₂) ∧
      (InC P.x i (rt a) ∧ InC P.x j (rt 3) ∧ InC P.x k (rt b)) := by
  rw [mem_famSet]
  refine and_congr_right fun _ => ?_
  simp only [KS, List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true, Atom.sem_ltVar, Atom.sem_ge, Atom.sem_lt, Atom.sem_prodGt, Atom.sem_prodLe, cellA_sem, Nat.cast_le,
    Nat.cast_lt]
  have e1 : ((P.N₁ : ℕ) : ℝ) < ∏ t, ((rt t : ℕ) : ℝ) ↔ P.N₁ < ∏ t, rt t := by rw [← Nat.cast_prod, Nat.cast_lt]
  have e2 : ∏ t, ((rt t : ℕ) : ℝ) ≤ ((P.N₂ : ℕ) : ℝ) ↔ ∏ t, rt t ≤ P.N₂ := by rw [← Nat.cast_prod, Nat.cast_le]
  rw [e1, e2]
  unfold InC
  tauto

/-- A pair in the cells `i` and `j` with `z₀ ≤ p₂ < p₁ < z_top`, both primes at most `Y`, is in the family `S2c i j`. -/
theorem mem_S2c_of {i j Y p₁ p₂ : ℕ} (h₁ : p₁ ≤ Y ∧ p₁.Prime) (h₂ : p₂ ≤ Y ∧ p₂.Prime) (hz₁ : P.z₀ ≤ p₁)
    (ht₁ : p₁ < P.ztop) (hC₁ : InC P.x i p₁) (hz₂ : P.z₀ ≤ p₂) (h21 : p₂ < p₁) (hC₂ : InC P.x j p₂) :
    ![p₁, p₂] ∈ famSet 2 Y (P.S2c i j) := by
  rw [S2c, famSet_append, Finset.mem_filter, S2, mem_famSet_extS]
  refine ⟨⟨?_, by simpa using h₂.1, by simpa using h₂.2, by simpa using hz₂, by simpa using h21⟩, ?_⟩
  · rw [mem_famSet]
    refine ⟨fun t => by rw [Fin.fin_one_eq_zero t]; simpa [Fin.init] using h₁, ?_⟩
    simp only [S1c, S1, List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff, false_implies,
      implies_true, and_true, Atom.sem_ge, Atom.sem_lt, cellA_sem, Nat.cast_le, Nat.cast_lt]
    simp only [Fin.init]
    exact ⟨⟨by simpa using hz₁, by simpa using ht₁⟩, by simpa [InC] using hC₁⟩
  · rw [cellA_sem]
    simpa [InC] using hC₂

/-- **One sorted case.** Let `mk p₁ p₂ q₁ q₂` place `p₁, p₂, q₁, q₂` at the positions `a, 3, b, c` of a permutation of
`Fin 4`, strictly decreasing when `p₂ < p₁`, `p₂ < q₁ < q₂` and the case's order `ord p₁ q₁ q₂` hold, every strictly
decreasing `rt` having `ord (rt a) (rt b) (rt c)` and `rt b < rt c`. For `x > 1` and a cell `k` above the cell `j`, the
kept terms of the case are `famE g` of the family `KS a b i j k`. -/
theorem sum_case (hx : 1 < P.x) (g : ℕ → ℝ) {i j k : ℕ} (hjk : SieveCert.e j + H ≤ SieveCert.e k)
    {a b c : Fin 4} (hperm : ∀ u : Fin 4, u = a ∨ u = 3 ∨ u = b ∨ u = c) (ha3 : a < 3) (hb3 : b < 3)
    (mk : ℕ → ℕ → ℕ → ℕ → Fin 4 → ℕ) (ord : ℕ → ℕ → ℕ → Prop)
    (ha : ∀ p₁ p₂ q₁ q₂, mk p₁ p₂ q₁ q₂ a = p₁) (h3 : ∀ p₁ p₂ q₁ q₂, mk p₁ p₂ q₁ q₂ 3 = p₂)
    (hb : ∀ p₁ p₂ q₁ q₂, mk p₁ p₂ q₁ q₂ b = q₁) (hc : ∀ p₁ p₂ q₁ q₂, mk p₁ p₂ q₁ q₂ c = q₂)
    (hprod : ∀ p₁ p₂ q₁ q₂, ∏ t, mk p₁ p₂ q₁ q₂ t = p₁ * p₂ * q₁ * q₂)
    (hanti : ∀ p₁ p₂ q₁ q₂, p₂ < p₁ → p₂ < q₁ → q₁ < q₂ → ord p₁ q₁ q₂ → StrictAnti (mk p₁ p₂ q₁ q₂))
    (hinv : ∀ rt : Fin 4 → ℕ, mk (rt a) (rt 3) (rt b) (rt c) = rt)
    (hord : ∀ rt : Fin 4 → ℕ, StrictAnti rt → ord (rt a) (rt b) (rt c) ∧ rt b < rt c ∧ rt b ≠ rt a ∧ rt c ≠ rt a) :
    ∑ rt ∈ famSet 2 P.N₂ (P.S2c i j), ∑ q₁ ∈ SieveRough.cellP P.x k, ∑ q₂ ∈ SieveTypeIIU.primesLe P.N₂,
        (if P.KC (rt 0) (rt 1) q₁ q₂ ∧ ord (rt 0) q₁ q₂ then g (rt 0 * rt 1 * q₁ * q₂) else 0) =
      famE g P.N₁ P.N₂ (famSet 4 P.N₂ (P.KS a b i j k)) := by
  set R := (famSet 2 P.N₂ (P.S2c i j) ×ˢ (SieveRough.cellP P.x k ×ˢ SieveTypeIIU.primesLe P.N₂)).filter
    (fun t => P.KC (t.1 0) (t.1 1) t.2.1 t.2.2 ∧ ord (t.1 0) t.2.1 t.2.2) with hR
  have hL : ∑ rt ∈ famSet 2 P.N₂ (P.S2c i j), ∑ q₁ ∈ SieveRough.cellP P.x k, ∑ q₂ ∈ SieveTypeIIU.primesLe P.N₂,
      (if P.KC (rt 0) (rt 1) q₁ q₂ ∧ ord (rt 0) q₁ q₂ then g (rt 0 * rt 1 * q₁ * q₂) else 0) =
      ∑ t ∈ R, g (t.1 0 * t.1 1 * t.2.1 * t.2.2) := by
    rw [hR, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun rt _ => ?_
    rw [Finset.sum_product]
  rw [hL]
  unfold famE
  -- the facts of a kept term
  have hfacts : ∀ t ∈ R, (t.1 0 ≤ P.N₂ ∧ (t.1 0).Prime) ∧ (t.1 1 ≤ P.N₂ ∧ (t.1 1).Prime) ∧
      Chain P.z₀ P.ztop t.1 ∧ InC P.x i (t.1 0) ∧ InC P.x j (t.1 1) ∧ (t.2.1).Prime ∧ InC P.x k t.2.1 ∧
      (t.2.2 ≤ P.N₂ ∧ (t.2.2).Prime) ∧ P.KC (t.1 0) (t.1 1) t.2.1 t.2.2 ∧ ord (t.1 0) t.2.1 t.2.2 := by
    intro t ht
    rw [hR, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨⟨h1, h2, h3'⟩, hK, ho⟩ := ht
    obtain ⟨hch, hCi, hCj⟩ := P.facts_S2c h1
    have hp := (mem_famSet.1 h1).1
    rw [mem_cellP_iff] at h2
    exact ⟨hp 0, hp 1, hch, hCi, hCj, h2.1, h2.2, SieveTypeIIU.mem_primesLe.1 h3' |>.symm |> fun h => ⟨h.2, h.1⟩,
      hK, ho⟩
  refine Finset.sum_nbij' (fun t => mk (t.1 0) (t.1 1) t.2.1 t.2.2) (fun rt => (![rt a, rt 3], (rt b, rt c)))
    ?_ ?_ ?_ ?_ ?_
  · -- into the sorted family
    intro t ht
    obtain ⟨hp0, hp1, hch, hCi, hCj, hq1p, hq1C, hq2, hK, ho⟩ := hfacts t ht
    have h10 : t.1 1 < t.1 0 := hch.1 (show (0 : Fin 2) < 1 by decide)
    have hq1 : t.1 1 < t.2.1 := by
      have : ((t.1 1 : ℕ) : ℝ) < t.2.1 := lt_of_lt_of_le hCj.2 ((rpow_cell_le hx.le hjk).trans hq1C.1)
      exact_mod_cast this
    have hsa := hanti _ _ _ _ h10 hq1 hK.1 ho
    have hle1 : t.2.1 ≤ P.N₂ := by
      have h1 := hK.2.2.2.2
      have : t.2.1 ≤ t.1 0 * t.1 1 * t.2.1 * t.2.2 := by
        have := hp0.2.pos; have := hp1.2.pos; have := hq2.2.pos
        calc t.2.1 = 1 * 1 * t.2.1 * 1 := by ring
          _ ≤ t.1 0 * t.1 1 * t.2.1 * t.2.2 := by gcongr <;> omega
      omega
    rw [mem_KS, ha, h3, hb, hprod]
    refine ⟨fun u => ?_, ⟨hsa (show (0 : Fin 4) < 1 by decide), hsa (show (1 : Fin 4) < 2 by decide),
      by simpa only [h3] using hsa (show (2 : Fin 4) < 3 by decide)⟩, ⟨hch.2.1 0, hch.2.2 0, hch.2.1 1⟩,
      ⟨hK.2.2.2.1, hK.2.2.2.2⟩,
      ⟨hCi, hCj, hq1C⟩⟩
    -- each entry is one of the four primes
    have hu : mk (t.1 0) (t.1 1) t.2.1 t.2.2 u ∈ ({t.1 0, t.1 1, t.2.1, t.2.2} : Finset ℕ) := by
      rcases hperm u with rfl | rfl | rfl | rfl
      · rw [ha]; simp
      · rw [h3]; simp
      · rw [hb]; simp
      · rw [hc]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with h | h | h | h <;> rw [h]
    · exact hp0
    · exact hp1
    · exact ⟨hle1, hq1p⟩
    · exact hq2
  · -- back to the kept terms
    intro rt hrt
    rw [mem_KS] at hrt
    obtain ⟨hp, ⟨h01, h12, h23⟩, ⟨hz, htop, hz3⟩, ⟨hlo, hhi⟩, ⟨hCi, hCj, hCk⟩⟩ := hrt
    have hsa : StrictAnti rt := by
      rw [Fin.strictAnti_iff_succ_lt]
      intro u
      fin_cases u
      · exact h01
      · exact h12
      · exact h23
    obtain ⟨ho, hbc, hba, hca⟩ := hord rt hsa
    have h3a : rt 3 < rt a := hsa ha3
    have hprod' : rt a * rt 3 * rt b * rt c = ∏ t, rt t := by
      have := hprod (rt a) (rt 3) (rt b) (rt c)
      rw [hinv] at this
      exact this.symm
    rw [hR, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨⟨P.mem_S2c_of (hp a) (hp 3) hz htop hCi hz3 h3a hCj, mem_cellP_iff.2 ⟨(hp b).2, hCk⟩,
      SieveTypeIIU.mem_primesLe.2 ⟨(hp c).1, (hp c).2⟩⟩, ⟨hbc, hba, hca, by rw [hprod']; exact hlo,
      by rw [hprod']; exact hhi⟩, ho⟩
  · -- left inverse
    intro t ht
    obtain ⟨hp0, hp1, -⟩ := hfacts t ht
    simp only [ha, h3, hb, hc]
    obtain ⟨rt', q₁, q₂⟩ := t
    simp only [Prod.mk.injEq, and_true]
    funext u
    fin_cases u <;> rfl
  · -- right inverse
    intro rt _
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hinv rt
  · -- the summands
    intro t ht
    obtain ⟨-, -, -, -, -, -, -, -, hK, -⟩ := hfacts t ht
    rw [hprod, ite_eq_left ⟨hK.2.2.2.1, hK.2.2.2.2⟩]

/-- **The kept part as three sorted families.** For `x > 1` and a cell `k` above the cell `j`, `Kk g i j k` is the sum
of `famE g` over the three sorted families: `p₁ > q₂ > q₁ > p₂` (`KS 0 2`), `q₂ > p₁ > q₁ > p₂` (`KS 1 2`) and
`q₂ > q₁ > p₁ > p₂` (`KS 2 1`). -/
theorem Kk_eq (hx : 1 < P.x) (g : ℕ → ℝ) {i j k : ℕ} (hjk : SieveCert.e j + H ≤ SieveCert.e k) :
    P.Kk g i j k = famE g P.N₁ P.N₂ (famSet 4 P.N₂ (P.KS 0 2 i j k)) +
      famE g P.N₁ P.N₂ (famSet 4 P.N₂ (P.KS 1 2 i j k)) + famE g P.N₁ P.N₂ (famSet 4 P.N₂ (P.KS 2 1 i j k)) := by
  have hA := P.sum_case hx g (i := i) hjk (a := 0) (b := 2) (c := 1) (by decide) (by decide) (by decide)
    (fun p₁ p₂ q₁ q₂ => ![p₁, q₂, q₁, p₂]) (fun p₁ _ q₂ => q₂ < p₁) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun p₁ p₂ q₁ q₂ => by simp [Fin.prod_univ_four]; ring)
    (fun p₁ p₂ q₁ q₂ h1 h2 h3 h4 => by
      rw [Fin.strictAnti_iff_succ_lt]; intro u; fin_cases u <;> simp <;> omega)
    (fun rt => by funext u; fin_cases u <;> rfl)
    (fun rt hsa => ⟨hsa (show (0 : Fin 4) < 1 by decide), hsa (show (1 : Fin 4) < 2 by decide),
      (hsa (show (0 : Fin 4) < 2 by decide)).ne, (hsa (show (0 : Fin 4) < 1 by decide)).ne⟩)
  have hB := P.sum_case hx g (i := i) hjk (a := 1) (b := 2) (c := 0) (by decide) (by decide) (by decide)
    (fun p₁ p₂ q₁ q₂ => ![q₂, p₁, q₁, p₂]) (fun p₁ q₁ q₂ => q₁ < p₁ ∧ p₁ < q₂) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun p₁ p₂ q₁ q₂ => by simp [Fin.prod_univ_four]; ring)
    (fun p₁ p₂ q₁ q₂ h1 h2 h3 h4 => by
      rw [Fin.strictAnti_iff_succ_lt]; intro u; fin_cases u <;> simp <;> omega)
    (fun rt => by funext u; fin_cases u <;> rfl)
    (fun rt hsa => ⟨⟨hsa (show (1 : Fin 4) < 2 by decide), hsa (show (0 : Fin 4) < 1 by decide)⟩,
      hsa (show (0 : Fin 4) < 2 by decide), (hsa (show (1 : Fin 4) < 2 by decide)).ne,
      (hsa (show (0 : Fin 4) < 1 by decide)).ne'⟩)
  have hC := P.sum_case hx g (i := i) hjk (a := 2) (b := 1) (c := 0) (by decide) (by decide) (by decide)
    (fun p₁ p₂ q₁ q₂ => ![q₂, q₁, p₁, p₂]) (fun p₁ q₁ _ => p₁ < q₁) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun p₁ p₂ q₁ q₂ => by simp [Fin.prod_univ_four]; ring)
    (fun p₁ p₂ q₁ q₂ h1 h2 h3 h4 => by
      rw [Fin.strictAnti_iff_succ_lt]; intro u; fin_cases u <;> simp <;> omega)
    (fun rt => by funext u; fin_cases u <;> rfl)
    (fun rt hsa => ⟨hsa (show (1 : Fin 4) < 2 by decide), hsa (show (0 : Fin 4) < 1 by decide),
      (hsa (show (1 : Fin 4) < 2 by decide)).ne', (hsa (show (0 : Fin 4) < 2 by decide)).ne'⟩)
  rw [← hA, ← hB, ← hC]
  unfold Kk keptAt
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun rt _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q₁ _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q₂ _ => ?_
  by_cases hK : P.KC (rt 0) (rt 1) q₁ q₂
  · have hK' := hK
    obtain ⟨h12, h1, h2, -, -⟩ := hK'
    simp only [hK, true_and]
    by_cases hA' : q₂ < rt 0
    · have hB' : ¬ (q₁ < rt 0 ∧ rt 0 < q₂) := fun h => by omega
      have hC' : ¬ rt 0 < q₁ := fun h => by omega
      simp [hA', hB', hC']
    · by_cases hB0 : q₁ < rt 0
      · have hB' : q₁ < rt 0 ∧ rt 0 < q₂ := ⟨hB0, by omega⟩
        have hC' : ¬ rt 0 < q₁ := by omega
        simp [hA', hB', hC']
      · have hB' : ¬ (q₁ < rt 0 ∧ rt 0 < q₂) := fun h => hB0 h.1
        have hC' : rt 0 < q₁ := by omega
        simp [hA', hB', hC']
  · simp [hK]

end Par

end SieveBuch

#print axioms SieveBuch.Par.Kp2_le
#print axioms SieveBuch.Par.Kk_eq
