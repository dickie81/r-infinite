/-
# Round 604: Type II for chains of primes (milestone M8)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. A `GCmp` is a comparison `0 ≤ c(m) + Σ_i e_i log x_i` (or `0 <`) with coefficients in `{−1, 0, 1}`
and no designated pivot. `RTg k Y Ω` is the set of `k`-tuples of primes up to `Y` that satisfy the comparisons `Ω` at
`m = 0`. `L = 2.333`, `N₁ = ⌊q^L⌋` and `N₂ = ⌊2q^L⌋`.

* `typeII_gcmp`, `typeII_gcmp'`: `SieveStops2.typeII_cmp` for `GCmp`s: those with a nonzero coefficient are pivoted,
  and those without one become conditions on `m`.
* `chainTU_bound` (the upper window): fix `e₀ > 0`, `k′`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for
  `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over `RTg (k′ + 1) N₂ Ω` with at most `J₀` comparisons, whose
  `m`-parts at `m = 0` are at most `Λ₁ log q`, each such tuple having its entries at least `q^{e₀}`, its last entry
  least, and `W₀ < ∏rt ≤ W₁`. Let `W₁ ≤ N₁`, `q^{0.401L} ≤ ⌊N₁/W₁⌋` and `⌊N₂/(W₀ + 1)⌋ ≤ q^{0.485L}`. Then the
  multiples `n ∈ (N₁, N₂]` of `∏rt` with no prime factor below `rt`'s last entry, summed over `rt`, have
  `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`.
* `chainTL_bound` (the lower window): the same for `rt` strictly decreasing, with entries at least `q^{e₀}` and
  `P₁ < ∏_{i∈S} rt_i ≤ P₂` for a set `S` of indices, where `q^{0.401L} ≤ P₁` and `P₂ ≤ q^{0.485L}`.

These evaluate the terms of `frontier/linnik/SIEVE-ROUTE.md` §6 that are evaluable: a chain `p₁ > ⋯ > p_k` of
primes, and the rough rest of `n`. In the upper window the chain's product is the Type II variable's partner and
the rest of `n` is the variable; in the lower window `m = ∏_S rt` is the variable, and the rest of `n` with the
primes off `S` are the family's primes.

The proof:

* Upper window: `sum_cofactor_range` puts the rest of `n` in `(N₁/W₁, N₂/(W₀ + 1)]`, the comparisons `cmpsTU` (the
  region, the rest's roughness against the last prime, the range) cut out the family, and `typeII_gcmp` bounds it.
* Lower window: the rest of `n` is the product of a non-increasing tuple `y` of primes at least `rt`'s last entry
  (`sum_mult_eq`, `sum_rough_tuples`). `sum_TL_eq` regroups the pairs `(rt, y)` by `m = ∏_S rt`, a squarefree `m`
  of `Mset S P₁ P₂`, with the prime variables `x = (y, rt on Sᶜ)` and the comparisons `cmpsTL`, whose `m`-parts
  read `m`'s factors in decreasing order (`factS`). Their `m`-parts are at most `B + log m` (`cmpsTL_c_le`), and
  `typeII_gcmp'` bounds each length of `y`.

The file imports `SieveProp6.lean`.
-/
import SieveProp6

open Real Finset SieveFamily SieveTree SieveCmp

namespace SieveChain

/-! ### Comparisons without a designated pivot -/

/-- A comparison `0 ≤ c(m) + Σ_i e_i log x_i` (or `0 <` when `strict`) with coefficients in `{−1, 0, 1}`. -/
structure GCmp (K : ℕ) where
  c : ℕ → ℝ
  e : Fin K → ℝ
  strict : Bool
  he : ∀ i, e i = -1 ∨ e i = 0 ∨ e i = 1

variable {K : ℕ}

/-- The comparison's form `c(m) + Σ_i e_i log x_i`. -/
noncomputable def GCmp.form (C : GCmp K) (m : ℕ) (x : Fin K → ℕ) : ℝ := C.c m + ∑ i, C.e i * Real.log (x i)

/-- The comparison holds: `0 < form` if strict, `0 ≤ form` otherwise. -/
def GCmp.holds (C : GCmp K) (m : ℕ) (x : Fin K → ℕ) : Prop :=
  if C.strict then 0 < C.form m x else 0 ≤ C.form m x

/-- A comparison with a nonzero coefficient, pivoted at one of them. -/
noncomputable def GCmp.toCmp (C : GCmp K) (h : ∃ i, C.e i ≠ 0) : Cmp K where
  c := C.c
  e := C.e
  strict := C.strict
  piv := Classical.choose h
  hpiv := by
    have h1 := Classical.choose_spec h
    rcases C.he (Classical.choose h) with h2 | h2 | h2
    · exact Or.inr h2
    · exact absurd h2 h1
    · exact Or.inl h2
  he := fun i => by rcases C.he i with h | h | h <;> simp [h]

theorem GCmp.toCmp_holds (C : GCmp K) (h : ∃ i, C.e i ≠ 0) (m : ℕ) (x : Fin K → ℕ) :
    (C.toCmp h).holds m x ↔ C.holds m x := Iff.rfl

theorem GCmp.toCmp_c (C : GCmp K) (h : ∃ i, C.e i ≠ 0) : (C.toCmp h).c = C.c := rfl

/-- With every coefficient zero, a comparison does not depend on `x`. -/
theorem GCmp.holds_of_zero (C : GCmp K) (h : ∀ i, C.e i = 0) (m : ℕ) (x y : Fin K → ℕ) :
    C.holds m x ↔ C.holds m y := by
  unfold GCmp.holds GCmp.form
  simp [h]

/-- The comparisons of a list that have a nonzero coefficient, pivoted. -/
noncomputable def pivoted (l : List (GCmp K)) : List (Cmp K) :=
  open Classical in l.filterMap (fun C => if h : ∃ i, C.e i ≠ 0 then some (C.toCmp h) else none)

theorem mem_pivoted {l : List (GCmp K)} {C' : Cmp K} :
    C' ∈ pivoted l ↔ ∃ C ∈ l, ∃ h : ∃ i, C.e i ≠ 0, C.toCmp h = C' := by
  classical
  unfold pivoted
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨C, hC, hC'⟩
    by_cases h : ∃ i, C.e i ≠ 0
    · rw [dite_eq_left h] at hC'
      exact ⟨C, hC, h, Option.some_inj.1 hC'⟩
    · rw [dite_eq_right h] at hC'
      exact absurd hC' (by simp)
  · rintro ⟨C, hC, h, rfl⟩
    exact ⟨C, hC, by rw [dite_eq_left h]⟩

theorem length_pivoted_le (l : List (GCmp K)) : (pivoted l).length ≤ l.length :=
  List.length_filterMap_le _ _

/-- A list of comparisons holds iff its pivoted part holds and its comparisons with all coefficients zero hold. -/
theorem holds_iff_pivoted (l : List (GCmp K)) (m : ℕ) (x : Fin K → ℕ) :
    (∀ C ∈ l, C.holds m x) ↔
      (∀ C' ∈ pivoted l, C'.holds m x) ∧ (∀ C ∈ l, (∀ i, C.e i = 0) → C.holds m (fun _ => 1)) := by
  constructor
  · intro h
    refine ⟨fun C' hC' => ?_, fun C hC h0 => (C.holds_of_zero h0 m x _).1 (h C hC)⟩
    obtain ⟨C, hC, hne, rfl⟩ := mem_pivoted.1 hC'
    exact (C.toCmp_holds hne m x).2 (h C hC)
  · rintro ⟨h1, h2⟩ C hC
    by_cases hne : ∃ i, C.e i ≠ 0
    · exact (C.toCmp_holds hne m x).1 (h1 _ (mem_pivoted.2 ⟨C, hC, hne, rfl⟩))
    · push Not at hne
      exact (C.holds_of_zero hne m x _).2 (h2 C hC hne)

/-! ### The basic comparisons -/

/-- A comparison taken at `m = 0`, whatever `m`. -/
def GCmp.const (C : GCmp K) : GCmp K := { C with c := fun _ => C.c 0 }

theorem GCmp.const_holds (C : GCmp K) (m : ℕ) (x : Fin K → ℕ) : C.const.holds m x ↔ C.holds 0 x := Iff.rfl

theorem gsum_single (i : Fin K) (x : Fin K → ℕ) :
    ∑ t, (if t = i then (1 : ℝ) else 0) * Real.log (x t) = Real.log (x i) := by
  simp [ite_mul]

theorem gsum_log_prod (x : Fin K → ℕ) (hx : ∀ i, 1 ≤ x i) :
    ∑ t, (1 : ℝ) * Real.log (x t) = Real.log (∏ t, (x t : ℝ)) := by
  rw [Real.log_prod (fun t _ => by have := hx t; positivity)]
  simp

/-- `x_i ≤ minFac m`. -/
noncomputable def grough (i : Fin K) : GCmp K where
  c := fun m => Real.log (Nat.minFac m)
  e := fun t => -(if t = i then 1 else 0)
  strict := false
  he := fun t => by split_ifs <;> simp

theorem grough_holds (i : Fin K) (m : ℕ) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (grough i).holds m x ↔ x i ≤ Nat.minFac m := by
  have hpos : (0 : ℝ) < x i := by exact_mod_cast hx i
  have hmf : (0 : ℝ) < Nat.minFac m := by exact_mod_cast Nat.minFac_pos m
  unfold GCmp.holds GCmp.form grough
  simp only [Bool.false_eq_true, ite_false, neg_mul, Finset.sum_neg_distrib, gsum_single, ← sub_eq_add_neg,
    sub_nonneg]
  rw [Real.log_le_log_iff hpos hmf, Nat.cast_le]

/-- `b < m∏_i x_i`. -/
noncomputable def grangeLo (b : ℝ) : GCmp K where
  c := fun m => Real.log m - Real.log b
  e := fun _ => 1
  strict := true
  he := fun _ => by simp

theorem grangeLo_holds {b : ℝ} (hb : 0 < b) {m : ℕ} (hm : 1 ≤ m) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (grangeLo b).holds m x ↔ b < (m : ℝ) * ∏ t, (x t : ℝ) := by
  have hpos : (0 : ℝ) < ∏ t, (x t : ℝ) := Finset.prod_pos fun t _ => by exact_mod_cast hx t
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold GCmp.holds GCmp.form grangeLo
  simp only [ite_true]
  rw [gsum_log_prod x hx, sub_add_eq_add_sub, ← Real.log_mul hm0.ne' hpos.ne', sub_pos]
  exact Real.log_lt_log_iff hb (mul_pos hm0 hpos)

/-- `m∏_i x_i ≤ b`. -/
noncomputable def grangeHi (b : ℝ) : GCmp K where
  c := fun m => Real.log b - Real.log m
  e := fun _ => -1
  strict := false
  he := fun _ => by simp

theorem grangeHi_holds {b : ℝ} (hb : 0 < b) {m : ℕ} (hm : 1 ≤ m) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (grangeHi b).holds m x ↔ (m : ℝ) * ∏ t, (x t : ℝ) ≤ b := by
  have hpos : (0 : ℝ) < ∏ t, (x t : ℝ) := Finset.prod_pos fun t _ => by exact_mod_cast hx t
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : ∑ t, (-1 : ℝ) * Real.log (x t) = -Real.log (∏ t, (x t : ℝ)) := by
    rw [Real.log_prod (fun t _ => by have := hx t; positivity), ← Finset.sum_neg_distrib]
    simp
  unfold GCmp.holds GCmp.form grangeHi
  simp only [Bool.false_eq_true, ite_false]
  rw [hlog, ← sub_eq_add_neg, sub_sub, ← Real.log_mul hm0.ne' hpos.ne', sub_nonneg]
  exact Real.log_le_log_iff (mul_pos hm0 hpos) hb

/-- `x_j ≤ x_i`. -/
noncomputable def ggeVar (i j : Fin K) : GCmp K where
  c := fun _ => 0
  e := fun t => (if t = i then 1 else 0) - (if t = j then 1 else 0)
  strict := false
  he := fun t => by split_ifs <;> simp

theorem ggeVar_holds (i j : Fin K) (m : ℕ) {x : Fin K → ℕ} (hx : ∀ t, 1 ≤ x t) :
    (ggeVar i j).holds m x ↔ x j ≤ x i := by
  have hpos : ∀ t, (0 : ℝ) < x t := fun t => by exact_mod_cast hx t
  unfold GCmp.holds GCmp.form ggeVar
  simp only [Bool.false_eq_true, ite_false, zero_add, sub_mul, Finset.sum_sub_distrib, gsum_single, sub_nonneg]
  rw [Real.log_le_log_iff (hpos _) (hpos _), Nat.cast_le]

/-- `g(m) ≤ log x_i`. -/
noncomputable def ggeM (i : Fin K) (g : ℕ → ℝ) : GCmp K where
  c := fun m => -g m
  e := fun t => if t = i then 1 else 0
  strict := false
  he := fun t => by split_ifs <;> simp

theorem ggeM_holds (i : Fin K) (g : ℕ → ℝ) (m : ℕ) (x : Fin K → ℕ) :
    (ggeM i g).holds m x ↔ g m ≤ Real.log (x i) := by
  unfold GCmp.holds GCmp.form ggeM
  simp only [Bool.false_eq_true, ite_false, gsum_single, neg_add_eq_sub, sub_nonneg]

/-! ### Multiples of a number in a range -/

/-- A `p`-rough `W ∈ (W₀, W₁]` with `W₁ ≤ N₁`: its multiples in `(N₁, N₂]` that are `p`-rough are `Wk` with
`k ∈ (N₁/W₁, N₂/(W₀ + 1)]` and `p ≤ minFac k`. -/
theorem sum_cofactor_range (f : ℕ → ℂ) {W p W₀ W₁ N₁ N₂ : ℕ} (hW0 : 0 < W) (hWp : rough p W)
    (hlo : W₀ < W) (hhi : W ≤ W₁) (hW₁ : W₁ ≤ N₁) (hP₁ : 1 ≤ N₁ / W₁) :
    ∑ n ∈ Finset.Ioc N₁ N₂, f n * (if W ∣ n ∧ rough p n then 1 else 0) =
      ∑ k ∈ Finset.Ioc (N₁ / W₁) (N₂ / (W₀ + 1)),
        (if p ≤ Nat.minFac k ∧ N₁ < W * k ∧ W * k ≤ N₂ then f (W * k) else 0) := by
  rw [SieveStops1.sum_cofactor f hW0 (le_trans hhi hW₁) hWp, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  have hW10 : 0 < W₁ := lt_of_lt_of_le hW0 hhi
  constructor
  · rintro ⟨⟨hk2, -⟩, hr, h1, h2⟩
    refine ⟨⟨?_, ?_⟩, (SieveStops2.rough_iff_le_minFac hk2).1 hr, h1, h2⟩
    · rw [Nat.div_lt_iff_lt_mul hW10]
      calc N₁ < W * k := h1
        _ ≤ W₁ * k := Nat.mul_le_mul_right k hhi
        _ = k * W₁ := Nat.mul_comm _ _
    · rw [Nat.le_div_iff_mul_le (by omega)]
      calc k * (W₀ + 1) ≤ k * W := Nat.mul_le_mul_left k hlo
        _ = W * k := Nat.mul_comm _ _
        _ ≤ N₂ := h2
  · rintro ⟨⟨hk1, -⟩, hmin, h1, h2⟩
    have hk2 : 2 ≤ k := by omega
    exact ⟨⟨hk2, le_trans (Nat.le_mul_of_pos_left k hW0) h2⟩, (SieveStops2.rough_iff_le_minFac hk2).2 hmin, h1, h2⟩

open Classical in
/-- The `k`-tuples of primes up to `Y` that satisfy the comparisons `Ω` at `m = 0`. -/
noncomputable def RTg (k Y : ℕ) (Ω : List (GCmp k)) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ : Fin k => SieveTypeIIU.primesLe Y)).filter (fun rt => ∀ C ∈ Ω, C.holds 0 rt)

/-! ### Splitting a chain by a set of its indices -/

section Split

variable {k : ℕ} (S : Finset (Fin k))

/-- `Fin |S| ⊕ Fin |Sᶜ| ≃ Fin k`, increasing on each part. -/
def eS : Fin S.card ⊕ Fin Sᶜ.card ≃ Fin k := finSumEquivOfFinset rfl rfl

/-- The tuple with `a` on `S` and `b` on `Sᶜ`, in order. -/
def merge (a : Fin S.card → ℕ) (b : Fin Sᶜ.card → ℕ) : Fin k → ℕ := fun i => Sum.elim a b ((eS S).symm i)

variable {S}

theorem merge_inl (a : Fin S.card → ℕ) (b : Fin Sᶜ.card → ℕ) (u : Fin S.card) :
    merge S a b (eS S (Sum.inl u)) = a u := by
  simp [merge]

theorem merge_inr (a : Fin S.card → ℕ) (b : Fin Sᶜ.card → ℕ) (v : Fin Sᶜ.card) :
    merge S a b (eS S (Sum.inr v)) = b v := by
  simp [merge]

theorem merge_split (rt : Fin k → ℕ) :
    merge S (fun u => rt (eS S (Sum.inl u))) (fun v => rt (eS S (Sum.inr v))) = rt := by
  funext i
  obtain ⟨y, rfl⟩ := (eS S).surjective i
  rcases y with u | v
  · exact merge_inl _ _ u
  · exact merge_inr _ _ v

theorem eS_inl (u : Fin S.card) : eS S (Sum.inl u) = S.orderEmbOfFin rfl u := rfl

theorem eS_inl_mem (u : Fin S.card) : eS S (Sum.inl u) ∈ S := by
  rw [eS_inl]; exact S.orderEmbOfFin_mem rfl u

theorem eS_inl_strictMono : StrictMono (fun u : Fin S.card => eS S (Sum.inl u)) :=
  (S.orderEmbOfFin rfl).strictMono

theorem prod_split (f : Fin k → ℝ) :
    ∏ i, f i = (∏ u, f (eS S (Sum.inl u))) * ∏ v, f (eS S (Sum.inr v)) := by
  rw [← Fintype.prod_equiv (eS S) (fun y => f (eS S y)) f (fun _ => rfl), Fintype.prod_sum_type]

theorem sum_split (f : Fin k → ℝ) :
    ∑ i, f i = (∑ u, f (eS S (Sum.inl u))) + ∑ v, f (eS S (Sum.inr v)) := by
  rw [← Fintype.sum_equiv (eS S) (fun y => f (eS S y)) f (fun _ => rfl), Fintype.sum_sum_type]

theorem prod_split_nat (f : Fin k → ℕ) :
    ∏ i, f i = (∏ u, f (eS S (Sum.inl u))) * ∏ v, f (eS S (Sum.inr v)) := by
  rw [← Fintype.prod_equiv (eS S) (fun y => f (eS S y)) f (fun _ => rfl), Fintype.prod_sum_type]

/-- The product over `S` is the product over the first part. -/
theorem prod_S (f : Fin k → ℕ) : ∏ i ∈ S, f i = ∏ u, f (eS S (Sum.inl u)) := by
  conv_lhs => rw [← S.image_orderEmbOfFin_univ rfl]
  rw [Finset.prod_image (fun u _ v _ h => (S.orderEmbOfFin rfl).injective h)]
  rfl

/-- The factors of `m`, as a decreasing `|S|`-tuple. -/
noncomputable def factS (m : ℕ) : Fin S.card → ℕ := SieveStops2.desc S.card m.primeFactors

/-- For a decreasing tuple of primes on `S`, the factors of its product are the tuple. -/
theorem factS_prod {a : Fin S.card → ℕ} (ha : StrictAnti a) (hp : ∀ u, (a u).Prime) :
    factS (S := S) (∏ u, a u) = a := by
  have hinj := ha.injective
  have hpf : (∏ u, a u).primeFactors = Finset.univ.image a := by
    have e : ∏ u, a u = ∏ p ∈ Finset.univ.image a, p :=
      (Finset.prod_image (f := fun p => p) (fun u _ v _ h => hinj h)).symm
    rw [e]
    exact Nat.primeFactors_prod fun p hp' => by
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hp'
      exact hp u
  unfold factS
  rw [hpf]
  exact SieveStops2.desc_image ha

end Split

/-! ### Comparisons on the full tuple, as comparisons of the lower window -/

section Transform

variable {k t : ℕ} (S : Finset (Fin k))

/-- The full tuple `(rt, y)` on `Fin (k + t)`: `rt` with `m`'s factors on `S` and `x`'s last part on `Sᶜ`, and
`y`, `x`'s first part. -/
noncomputable def fullOf (m : ℕ) (x : Fin (t + Sᶜ.card) → ℕ) : Fin (k + t) → ℕ :=
  Fin.append (merge S (factS (S := S) m) (fun v => x (Fin.natAdd t v))) (fun a => x (Fin.castAdd Sᶜ.card a))

/-- A comparison of the full tuple `(rt, y)` at `m = 1`, as one of `x = (y, rt on Sᶜ)` with `m = ∏_S rt`. -/
noncomputable def splitS (C : GCmp (k + t)) : GCmp (t + Sᶜ.card) where
  c := fun m => C.c 1 + ∑ u, C.e (Fin.castAdd t (eS S (Sum.inl u))) * Real.log (factS (S := S) m u)
  e := fun i => Fin.addCases (fun a => C.e (Fin.natAdd k a)) (fun v => C.e (Fin.castAdd t (eS S (Sum.inr v)))) i
  strict := C.strict
  he := fun i => by
    refine Fin.addCases (fun a => ?_) (fun v => ?_) i
    · simpa using C.he _
    · simpa using C.he _

variable {S}

theorem splitS_form (C : GCmp (k + t)) (m : ℕ) (x : Fin (t + Sᶜ.card) → ℕ) :
    (splitS S C).form m x = C.form 1 (fullOf S m x) := by
  unfold GCmp.form splitS fullOf
  rw [Fin.sum_univ_add, Fin.sum_univ_add (f := fun j : Fin (k + t) => C.e j * Real.log _)]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.append_left, Fin.append_right]
  rw [sum_split (S := S) (fun i : Fin k => C.e (Fin.castAdd t i) *
    Real.log (merge S (factS (S := S) m) (fun v => x (Fin.natAdd t v)) i))]
  simp only [merge_inl, merge_inr]
  ring

theorem splitS_holds (C : GCmp (k + t)) (m : ℕ) (x : Fin (t + Sᶜ.card) → ℕ) :
    (splitS S C).holds m x ↔ C.holds 1 (fullOf S m x) := by
  unfold GCmp.holds
  rw [splitS_form]
  rfl

/-- A comparison of the chain, on the full tuple. -/
def liftChain (C : GCmp k) : GCmp (k + t) where
  c := fun _ => C.c 0
  e := fun i => Fin.addCases C.e (fun _ => 0) i
  strict := C.strict
  he := fun i => by
    refine Fin.addCases (fun a => ?_) (fun v => ?_) i
    · simpa using C.he _
    · simp

theorem liftChain_holds (C : GCmp k) (m : ℕ) (z : Fin (k + t) → ℕ) :
    (liftChain (t := t) C).holds m z ↔ C.holds 0 (fun i => z (Fin.castAdd t i)) := by
  unfold GCmp.holds GCmp.form liftChain
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]

end Transform

/-! ### The comparisons of the lower window -/

section TLcmps

open Classical

/-- `y` non-increasing: `y_b ≤ y_a` for `a ≤ b`, on the full tuple `(rt, y)`. -/
noncomputable def yPairs (k t : ℕ) : List (GCmp (k + t)) :=
  (List.finRange t).flatMap fun a => (List.finRange t).filterMap fun b =>
    if a ≤ b then some (ggeVar (Fin.natAdd k a) (Fin.natAdd k b)) else none

theorem mem_yPairs {k t : ℕ} {C : GCmp (k + t)} :
    C ∈ yPairs k t ↔ ∃ a b : Fin t, a ≤ b ∧ ggeVar (Fin.natAdd k a) (Fin.natAdd k b) = C := by
  unfold yPairs
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap]
  constructor
  · rintro ⟨a, b, hb⟩
    by_cases hab : a ≤ b
    · rw [ite_eq_left hab] at hb
      exact ⟨a, b, hab, Option.some_inj.1 hb⟩
    · rw [ite_eq_right hab] at hb
      exact absurd hb (by simp)
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨a, b, by rw [ite_eq_left hab]⟩

theorem length_yPairs_le (k t : ℕ) : (yPairs k t).length ≤ t * t := by
  unfold yPairs
  rw [List.length_flatMap]
  calc ((List.finRange t).map fun a => ((List.finRange t).filterMap fun b =>
        if a ≤ b then some (ggeVar (Fin.natAdd k a) (Fin.natAdd k b)) else none).length).sum
      ≤ ((List.finRange t).map fun _ => t).sum := by
        apply List.sum_le_sum
        intro a _
        exact (List.length_filterMap_le _ _).trans (by simp)
    _ = t * t := by simp

theorem yPairs_holds {k t : ℕ} (m : ℕ) {z : Fin (k + t) → ℕ} (hz : ∀ i, 1 ≤ z i) :
    (∀ C ∈ yPairs k t, C.holds m z) ↔ ∀ a b : Fin t, a ≤ b → z (Fin.natAdd k b) ≤ z (Fin.natAdd k a) := by
  constructor
  · intro h a b hab
    exact (ggeVar_holds _ _ m hz).1 (h _ (mem_yPairs.2 ⟨a, b, hab, rfl⟩))
  · intro h C hC
    obtain ⟨a, b, hab, rfl⟩ := mem_yPairs.1 hC
    exact (ggeVar_holds _ _ m hz).2 (h a b hab)

/-- `y` at least the chain's last entry, on the full tuple. -/
noncomputable def yLast (k' t : ℕ) : List (GCmp (k' + 1 + t)) :=
  (List.finRange t).map fun a => ggeVar (Fin.natAdd (k' + 1) a) (Fin.castAdd t (Fin.last k'))

theorem yLast_holds {k' t : ℕ} (m : ℕ) {z : Fin (k' + 1 + t) → ℕ} (hz : ∀ i, 1 ≤ z i) :
    (∀ C ∈ yLast k' t, C.holds m z) ↔ ∀ a : Fin t, z (Fin.castAdd t (Fin.last k')) ≤ z (Fin.natAdd (k' + 1) a) := by
  unfold yLast
  simp only [List.forall_mem_map, List.mem_finRange, true_implies]
  exact forall_congr' fun a => ggeVar_holds _ _ m hz

/-- The comparisons of the full tuple `(rt, y)`: the region `Ω` of `rt`, `y` non-increasing and at least `rt`'s
last entry, and the range `N₁ < ∏rt·∏y ≤ N₂`. -/
noncomputable def fullTL (k' t : ℕ) (Ω : List (GCmp (k' + 1))) (N₁ N₂ : ℝ) : List (GCmp (k' + 1 + t)) :=
  Ω.map (liftChain (t := t)) ++ yPairs (k' + 1) t ++ yLast k' t ++ [grangeLo N₁, grangeHi N₂]

theorem length_fullTL_le (k' t : ℕ) (Ω : List (GCmp (k' + 1))) (N₁ N₂ : ℝ) :
    (fullTL k' t Ω N₁ N₂).length ≤ Ω.length + t * t + t + 2 := by
  unfold fullTL yLast
  simp only [List.length_append, List.length_map, List.length_finRange, List.length_cons, List.length_nil]
  have := length_yPairs_le (k' + 1) t
  omega

theorem fullTL_holds {k' t : ℕ} (Ω : List (GCmp (k' + 1))) {N₁ N₂ : ℝ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (rt : Fin (k' + 1) → ℕ) (y : Fin t → ℕ) (hrt : ∀ i, 1 ≤ rt i) (hy : ∀ a, 1 ≤ y a) :
    (∀ C ∈ fullTL k' t Ω N₁ N₂, C.holds 1 (Fin.append rt y)) ↔
      (∀ C ∈ Ω, C.holds 0 rt) ∧ (∀ a b : Fin t, a ≤ b → y b ≤ y a) ∧ (∀ a, rt (Fin.last k') ≤ y a) ∧
        N₁ < (∏ i, (rt i : ℝ)) * ∏ a, (y a : ℝ) ∧ (∏ i, (rt i : ℝ)) * ∏ a, (y a : ℝ) ≤ N₂ := by
  have hz : ∀ i, 1 ≤ Fin.append rt y i := fun i => by
    refine Fin.addCases (fun i => ?_) (fun a => ?_) i
    · rw [Fin.append_left]; exact hrt i
    · rw [Fin.append_right]; exact hy a
  have hprod : ∏ i, ((Fin.append rt y i : ℕ) : ℝ) = (∏ i, (rt i : ℝ)) * ∏ a, (y a : ℝ) := by
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  unfold fullTL
  simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, and_true]
  rw [yPairs_holds 1 hz, yLast_holds 1 hz, grangeLo_holds hN₁ le_rfl hz, grangeHi_holds hN₂ le_rfl hz]
  simp only [Fin.append_left, Fin.append_right, Nat.cast_one, one_mul, hprod]
  have hlc : (∀ C ∈ Ω, (liftChain (t := t) C).holds 1 (Fin.append rt y)) ↔ ∀ C ∈ Ω, C.holds 0 rt := by
    refine forall₂_congr fun C _ => ?_
    rw [liftChain_holds]
    simp only [Fin.append_left]
  rw [hlc]
  tauto

/-- The comparisons of the lower window with `m = ∏_S rt`. -/
noncomputable def cmpsTL {k' : ℕ} (S : Finset (Fin (k' + 1))) (t : ℕ) (Ω : List (GCmp (k' + 1))) (N₁ N₂ : ℝ) :
    List (GCmp (t + Sᶜ.card)) :=
  (fullTL k' t Ω N₁ N₂).map (splitS S)

/-- The squarefree `m ∈ (P₁, P₂]` with `|S|` prime factors. -/
noncomputable def Mset {k : ℕ} (S : Finset (Fin k)) (P₁ P₂ : ℕ) : Finset ℕ :=
  (Finset.Ioc P₁ P₂).filter (fun m => m.primeFactors.card = S.card ∧ ∏ p ∈ m.primeFactors, p = m)

end TLcmps

/-! ### The lower window: chains and cofactor tuples as `m = ∏_S rt` and the other primes -/

section TLsum

open Classical

theorem prod_append_nat {a b : ℕ} (u : Fin a → ℕ) (v : Fin b → ℕ) :
    ∏ i, Fin.append u v i = (∏ i, u i) * ∏ i, v i := by
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- For `N₁, N₂ > 0`, `x_i ≥ 1` and `m`'s factors on `S` at least `1`: what the comparisons of the lower window say
at `(m, x)`, through the chain `rt` with `m`'s factors on `S` and `x`'s last part on `Sᶜ`, and `y`, `x`'s first part. -/
theorem cmpsTL_holds {k' : ℕ} {S : Finset (Fin (k' + 1))} {t : ℕ} (Ω : List (GCmp (k' + 1))) {N₁ N₂ : ℝ}
    (hN₁0 : 0 < N₁) (hN₂0 : 0 < N₂) (m : ℕ) (x : Fin (t + Sᶜ.card) → ℕ) (hx : ∀ i, 1 ≤ x i)
    (hf : ∀ u, 1 ≤ factS (S := S) m u) :
    (∀ C ∈ cmpsTL S t Ω N₁ N₂, C.holds m x) ↔
      (∀ C ∈ Ω, C.holds 0 (merge S (factS (S := S) m) (fun v => x (Fin.natAdd t v)))) ∧
      (∀ a b : Fin t, a ≤ b → x (Fin.castAdd Sᶜ.card b) ≤ x (Fin.castAdd Sᶜ.card a)) ∧
      (∀ a, merge S (factS (S := S) m) (fun v => x (Fin.natAdd t v)) (Fin.last k') ≤ x (Fin.castAdd Sᶜ.card a)) ∧
      N₁ < (∏ i, (merge S (factS (S := S) m) (fun v => x (Fin.natAdd t v)) i : ℝ)) *
        ∏ a, (x (Fin.castAdd Sᶜ.card a) : ℝ) ∧
      (∏ i, (merge S (factS (S := S) m) (fun v => x (Fin.natAdd t v)) i : ℝ)) *
        ∏ a, (x (Fin.castAdd Sᶜ.card a) : ℝ) ≤ N₂ := by
  have hrt : ∀ i, 1 ≤ merge S (factS (S := S) m) (fun v => x (Fin.natAdd t v)) i := by
    intro i
    obtain ⟨y, rfl⟩ := (eS S).surjective i
    rcases y with u | v
    · rw [merge_inl]; exact hf u
    · rw [merge_inr]; exact hx _
  unfold cmpsTL
  rw [List.forall_mem_map]
  rw [show (∀ C ∈ fullTL k' t Ω N₁ N₂, (splitS S C).holds m x) ↔
      (∀ C ∈ fullTL k' t Ω N₁ N₂, C.holds 1 (fullOf S m x)) from forall₂_congr fun C _ => splitS_holds C m x]
  exact fullTL_holds Ω hN₁0 hN₂0 _ _ hrt (fun a => hx _)

/-- **The lower window's bijection.** For `1 ≤ N₁ ≤ N₂ ≤ Y` and `P₂ ≤ Y`: the chains `rt` of the region `Ω` (prime,
decreasing, with `P₁ < ∏_S rt ≤ P₂`) times the non-increasing `t`-tuples `y` of primes at least `rt`'s last entry,
with `N₁ < ∏rt·∏y ≤ N₂`, are the `m ∈ Mset S P₁ P₂` times the tuples `x = (y, rt on Sᶜ)` that satisfy `cmpsTL`. -/
theorem sum_TL_eq {M : Type*} [AddCommMonoid M] {k' : ℕ} (S : Finset (Fin (k' + 1)))
    (Ω : List (GCmp (k' + 1))) {Y N₁ N₂ P₁ P₂ : ℕ} (t : ℕ)
    (hreg : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ P₁ < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ P₂)
    (hN₁ : 1 ≤ N₁) (hN₁₂ : N₁ ≤ N₂) (hN₂ : N₂ ≤ Y) (hP₂ : P₂ ≤ Y) (F : ℕ → M) :
    ∑ rt ∈ RTg (k' + 1) Y Ω, ∑ y ∈ SieveRoughTuple.tuples (rt (Fin.last k')) Y t,
        (if N₁ < (∏ i, rt i) * ∏ a, y a ∧ (∏ i, rt i) * ∏ a, y a ≤ N₂ then F ((∏ i, rt i) * ∏ a, y a) else 0) =
      ∑ m ∈ Mset S P₁ P₂, ∑ x ∈ Fintype.piFinset (fun _ : Fin (t + Sᶜ.card) => SieveTypeIIU.primesLe Y),
        (if ∀ C ∈ cmpsTL S t Ω N₁ N₂, C.holds m x then F (m * ∏ i, x i) else 0) := by
  set D := ((RTg (k' + 1) Y Ω) ×ˢ (Fintype.piFinset (fun _ : Fin t => SieveTypeIIU.primesLe Y))).filter
    (fun p => ((∀ i j : Fin t, i ≤ j → p.2 j ≤ p.2 i) ∧ (∀ i, p.1 (Fin.last k') ≤ p.2 i) ∧ ∏ a, p.2 a ≤ Y) ∧
      (N₁ < (∏ i, p.1 i) * ∏ a, p.2 a ∧ (∏ i, p.1 i) * ∏ a, p.2 a ≤ N₂)) with hD
  set Cd := ((Mset S P₁ P₂) ×ˢ (Fintype.piFinset (fun _ : Fin (t + Sᶜ.card) => SieveTypeIIU.primesLe Y))).filter
    (fun p => ∀ C ∈ cmpsTL S t Ω N₁ N₂, C.holds p.1 p.2) with hCd
  have hL : ∑ rt ∈ RTg (k' + 1) Y Ω, ∑ y ∈ SieveRoughTuple.tuples (rt (Fin.last k')) Y t,
      (if N₁ < (∏ i, rt i) * ∏ a, y a ∧ (∏ i, rt i) * ∏ a, y a ≤ N₂ then F ((∏ i, rt i) * ∏ a, y a) else 0) =
      ∑ p ∈ D, F ((∏ i, p.1 i) * ∏ a, p.2 a) := by
    rw [hD, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun rt _ => ?_
    rw [SieveRoughTuple.tuples, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    dsimp only
    simp only [ite_and]
  have hR : ∑ m ∈ Mset S P₁ P₂, ∑ x ∈ Fintype.piFinset (fun _ : Fin (t + Sᶜ.card) => SieveTypeIIU.primesLe Y),
      (if ∀ C ∈ cmpsTL S t Ω N₁ N₂, C.holds m x then F (m * ∏ i, x i) else 0) =
      ∑ p ∈ Cd, F (p.1 * ∏ i, p.2 i) := by
    rw [hCd, Finset.sum_filter, Finset.sum_product]
  rw [hL, hR]
  have hN₁0 : (0 : ℝ) < N₁ := by exact_mod_cast hN₁
  have hN₂0 : (0 : ℝ) < N₂ := by exact_mod_cast (show 0 < N₂ by omega)
  have hsem := fun m x (hx : ∀ i, 1 ≤ x i) hf => cmpsTL_holds (S := S) (t := t) Ω hN₁0 hN₂0 m x hx hf
  refine Finset.sum_nbij' (fun p => (∏ u, p.1 (eS S (Sum.inl u)), Fin.append p.2 (fun v => p.1 (eS S (Sum.inr v)))))
    (fun p => (merge S (factS (S := S) p.1) (fun v => p.2 (Fin.natAdd t v)), fun a => p.2 (Fin.castAdd Sᶜ.card a)))
    ?_ ?_ ?_ ?_ ?_
  · -- into the window's tuples
    rintro ⟨rt, y⟩ hp
    simp only [hD, Finset.mem_filter, Finset.mem_product, RTg, Fintype.mem_piFinset] at hp
    obtain ⟨⟨⟨hrtY, hrtΩ⟩, hyY⟩, ⟨hanti, hlast, -⟩, hlo, hhi⟩ := hp
    have hrtp : ∀ i, (rt i).Prime := fun i => (SieveTypeIIU.mem_primesLe.1 (hrtY i)).2
    obtain ⟨hsa, hP₁S, hSP₂⟩ := hreg rt hrtp hrtΩ
    have hsaS : StrictAnti (fun u => rt (eS S (Sum.inl u))) := hsa.comp_strictMono eS_inl_strictMono
    have hfac := factS_prod (S := S) hsaS (fun u => hrtp _)
    have hm : ∏ i ∈ S, rt i = ∏ u, rt (eS S (Sum.inl u)) := prod_S rt
    have hpf : (∏ u, rt (eS S (Sum.inl u))).primeFactors = Finset.univ.image (fun u => rt (eS S (Sum.inl u))) := by
      have e : ∏ u, rt (eS S (Sum.inl u)) = ∏ p ∈ Finset.univ.image (fun u => rt (eS S (Sum.inl u))), p :=
        (Finset.prod_image (f := fun p => p) (fun u _ v _ h => hsaS.injective h)).symm
      rw [e]
      exact Nat.primeFactors_prod fun p hp' => by
        obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hp'
        exact hrtp _
    have hx1 : ∀ i, 1 ≤ Fin.append y (fun v => rt (eS S (Sum.inr v))) i := fun i => by
      refine Fin.addCases (fun a => ?_) (fun v => ?_) i
      · rw [Fin.append_left]; exact (SieveTypeIIU.mem_primesLe.1 (hyY a)).2.one_lt.le
      · rw [Fin.append_right]; exact (hrtp _).one_lt.le
    have hf1 : ∀ u, 1 ≤ factS (S := S) (∏ u, rt (eS S (Sum.inl u))) u := fun u => by
      rw [hfac]; exact (hrtp _).one_lt.le
    simp only [hCd, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset]
    refine ⟨⟨?_, fun i => ?_⟩, (hsem _ _ hx1 hf1).2 ?_⟩
    · rw [Mset, Finset.mem_filter, Finset.mem_Ioc, hpf]
      refine ⟨⟨hm ▸ hP₁S, hm ▸ hSP₂⟩, ?_, ?_⟩
      · rw [Finset.card_image_of_injective _ hsaS.injective, Finset.card_univ, Fintype.card_fin]
      · exact (Finset.prod_image (f := fun p => p) (fun u _ v _ h => hsaS.injective h))
    · refine Fin.addCases (fun a => ?_) (fun v => ?_) i
      · rw [Fin.append_left]; exact hyY a
      · rw [Fin.append_right]; exact hrtY _
    · have hmerge : merge S (factS (S := S) (∏ u, rt (eS S (Sum.inl u))))
          (fun v => Fin.append y (fun v => rt (eS S (Sum.inr v))) (Fin.natAdd t v)) = rt := by
        rw [hfac]
        simp only [Fin.append_right]
        exact merge_split rt
      simp only [hmerge, Fin.append_left]
      refine ⟨hrtΩ, hanti, hlast, ?_, ?_⟩
      · have : (N₁ : ℝ) < (((∏ i, rt i) * ∏ a, y a : ℕ) : ℝ) := by exact_mod_cast hlo
        push_cast at this
        exact this
      · have : (((∏ i, rt i) * ∏ a, y a : ℕ) : ℝ) ≤ N₂ := by exact_mod_cast hhi
        push_cast at this
        exact this
  · -- back to the chains
    rintro ⟨m, x⟩ hp
    simp only [hCd, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset] at hp
    obtain ⟨⟨hmM, hxY⟩, hall⟩ := hp
    rw [Mset, Finset.mem_filter, Finset.mem_Ioc] at hmM
    obtain ⟨⟨hP₁m, hmP₂⟩, hcard, hprodm⟩ := hmM
    have hx1 : ∀ i, 1 ≤ x i := fun i => (SieveTypeIIU.mem_primesLe.1 (hxY i)).2.one_lt.le
    have hfmem : ∀ u, factS (S := S) m u ∈ m.primeFactors := fun u => SieveStops2.desc_mem hcard u
    have hfp : ∀ u, (factS (S := S) m u).Prime := fun u => Nat.prime_of_mem_primeFactors (hfmem u)
    have hm0 : m ≠ 0 := by omega
    have hfle : ∀ u, factS (S := S) m u ≤ Y := fun u =>
      le_trans (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors (hfmem u))) (le_trans hmP₂ hP₂)
    have hf1 : ∀ u, 1 ≤ factS (S := S) m u := fun u => (hfp u).one_lt.le
    obtain ⟨hΩ', hanti, hlast, hlo, hhi⟩ := (hsem m x hx1 hf1).1 hall
    set rt := merge S (factS (S := S) m) (fun v => x (Fin.natAdd t v)) with hrt
    have hrtY : ∀ i, rt i ∈ SieveTypeIIU.primesLe Y := by
      intro i
      obtain ⟨y, rfl⟩ := (eS S).surjective i
      rcases y with u | v
      · rw [hrt, merge_inl]; exact SieveTypeIIU.mem_primesLe.2 ⟨hfle u, hfp u⟩
      · rw [hrt, merge_inr]; exact hxY _
    have hcast : ((∏ i, rt i) * ∏ a, x (Fin.castAdd Sᶜ.card a) : ℕ) =
        ((∏ i, (rt i : ℝ)) * ∏ a, (x (Fin.castAdd Sᶜ.card a) : ℝ) : ℝ) := by push_cast; ring
    have hlo' : N₁ < (∏ i, rt i) * ∏ a, x (Fin.castAdd Sᶜ.card a) := by
      have : (N₁ : ℝ) < ((∏ i, rt i) * ∏ a, x (Fin.castAdd Sᶜ.card a) : ℕ) := by rw [hcast]; exact hlo
      exact_mod_cast this
    have hhi' : (∏ i, rt i) * ∏ a, x (Fin.castAdd Sᶜ.card a) ≤ N₂ := by
      have : (((∏ i, rt i) * ∏ a, x (Fin.castAdd Sᶜ.card a) : ℕ) : ℝ) ≤ N₂ := by rw [hcast]; exact hhi
      exact_mod_cast this
    have hrt1 : 1 ≤ ∏ i, rt i := Finset.one_le_prod fun i _ => by
      obtain ⟨y, rfl⟩ := (eS S).surjective i
      rcases y with u | v
      · rw [hrt, merge_inl]; exact hf1 u
      · rw [hrt, merge_inr]; exact hx1 _
    simp only [hD, Finset.mem_filter, Finset.mem_product, RTg, Fintype.mem_piFinset]
    refine ⟨⟨⟨hrtY, hΩ'⟩, fun a => hxY _⟩, ⟨hanti, hlast, ?_⟩, hlo', hhi'⟩
    calc ∏ a, x (Fin.castAdd Sᶜ.card a) ≤ (∏ i, rt i) * ∏ a, x (Fin.castAdd Sᶜ.card a) :=
          Nat.le_mul_of_pos_left _ hrt1
      _ ≤ N₂ := hhi'
      _ ≤ Y := hN₂
  · -- left inverse
    rintro ⟨rt, y⟩ hp
    simp only [hD, Finset.mem_filter, Finset.mem_product, RTg, Fintype.mem_piFinset] at hp
    obtain ⟨⟨⟨hrtY, hrtΩ⟩, -⟩, -, -, -⟩ := hp
    have hrtp : ∀ i, (rt i).Prime := fun i => (SieveTypeIIU.mem_primesLe.1 (hrtY i)).2
    have hsaS : StrictAnti (fun u => rt (eS S (Sum.inl u))) :=
      (hreg rt hrtp hrtΩ).1.comp_strictMono eS_inl_strictMono
    have hfac := factS_prod (S := S) hsaS (fun u => hrtp _)
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hfac]
      simp only [Fin.append_right]
      exact merge_split rt
    · funext a
      simp only [Fin.append_left]
  · -- right inverse
    rintro ⟨m, x⟩ hp
    simp only [hCd, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hmM, -⟩, -⟩ := hp
    rw [Mset, Finset.mem_filter] at hmM
    obtain ⟨-, hcard, hprodm⟩ := hmM
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · simp only [merge_inl]
      unfold factS
      rw [SieveStops2.prod_desc hcard, hprodm]
    · simp only [merge_inr]
      exact Fin.append_castAdd_natAdd
  · -- the summands
    rintro ⟨rt, y⟩ hp
    simp only
    rw [prod_append_nat, prod_split_nat (S := S) rt]
    ring_nf

/-- The forms' `m`-parts of the lower window are at most `B + log m` on `Mset`, given `C.c 0 ≤ B` on `Ω`,
`log N₂ ≤ B`, `0 ≤ B` and `N₁ ≥ 1`. -/
theorem cmpsTL_c_le {k' : ℕ} (S : Finset (Fin (k' + 1))) (t : ℕ) (Ω : List (GCmp (k' + 1))) {N₁ N₂ B : ℝ}
    {P₁ P₂ : ℕ} (hΩ : ∀ C ∈ Ω, C.c 0 ≤ B) (hB : 0 ≤ B) (hN₁ : 1 ≤ N₁) (hN₂ : Real.log N₂ ≤ B) :
    ∀ C ∈ cmpsTL S t Ω N₁ N₂, ∀ m ∈ Mset S P₁ P₂, C.c m ≤ B + Real.log m := by
  intro C' hC' m hm
  rw [Mset, Finset.mem_filter] at hm
  obtain ⟨-, hcard, hprodm⟩ := hm
  unfold cmpsTL at hC'
  obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC'
  have hf1 : ∀ u, 1 ≤ factS (S := S) m u := fun u =>
    (Nat.prime_of_mem_primeFactors (SieveStops2.desc_mem hcard u)).one_lt.le
  have hsum : ∑ u, C.e (Fin.castAdd t (eS S (Sum.inl u))) * Real.log (factS (S := S) m u) ≤ Real.log m := by
    calc ∑ u, C.e (Fin.castAdd t (eS S (Sum.inl u))) * Real.log (factS (S := S) m u)
        ≤ ∑ u, Real.log (factS (S := S) m u) := by
          refine Finset.sum_le_sum fun u _ => ?_
          have hl : 0 ≤ Real.log (factS (S := S) m u) := Real.log_nonneg (by exact_mod_cast hf1 u)
          rcases C.he (Fin.castAdd t (eS S (Sum.inl u))) with h | h | h <;> rw [h] <;> linarith
      _ = Real.log m := by
          rw [← Real.log_prod (fun u _ => by have := hf1 u; positivity)]
          congr 1
          have : (∏ u, factS (S := S) m u : ℕ) = m := by
            unfold factS
            rw [SieveStops2.prod_desc hcard, hprodm]
          exact_mod_cast this
  have hc1 : C.c 1 ≤ B := by
    unfold fullTL at hC
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
    rcases hC with ((⟨C₀, hC₀, rfl⟩ | hC) | hC) | rfl | rfl
    · exact hΩ C₀ hC₀
    · obtain ⟨a, b, -, rfl⟩ := mem_yPairs.1 hC
      exact hB
    · unfold yLast at hC
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hC
      exact hB
    · show Real.log ((1 : ℕ) : ℝ) - Real.log N₁ ≤ B
      have := Real.log_nonneg hN₁
      simp only [Nat.cast_one, Real.log_one]
      linarith
    · show Real.log N₂ - Real.log ((1 : ℕ) : ℝ) ≤ B
      simp only [Nat.cast_one, Real.log_one, sub_zero]
      exact hN₂
  show C.c 1 + ∑ u, C.e (Fin.castAdd t (eS S (Sum.inl u))) * Real.log (factS (S := S) m u) ≤ B + Real.log m
  linarith

end TLsum

/-! ### Multiples of a number as cofactor tuples -/

/-- The `p`-rough multiples in `(N₁, N₂]` of a `p`-rough `W > 0` are `Wk` with `k ∈ [1, N₂]` `p`-rough. -/
theorem sum_mult_eq (f : ℕ → ℂ) {W p N₁ N₂ : ℕ} (hW : 0 < W) (hWp : rough p W) :
    ∑ n ∈ Finset.Ioc N₁ N₂, f n * (if W ∣ n ∧ rough p n then 1 else 0) =
      ∑ k ∈ (Finset.Icc 1 N₂).filter (fun k => ∀ p' < p, p'.Prime → ¬ p' ∣ k),
        (if N₁ < W * k ∧ W * k ≤ N₂ then f (W * k) else 0) := by
  rw [show (∑ n ∈ Finset.Ioc N₁ N₂, f n * (if W ∣ n ∧ rough p n then 1 else 0)) =
      ∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => W ∣ n ∧ rough p n), f n by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun n => n / W) (fun k => W * k) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hn2⟩, ⟨c, rfl⟩, hr⟩ := hn
    rw [Nat.mul_div_cancel_left c hW]
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; omega
      · omega
    exact ⟨⟨⟨hc1, le_trans (Nat.le_mul_of_pos_left c hW) hn2⟩,
      fun p' hp' hpp hpd => hr p' hp' hpp (dvd_mul_of_dvd_right hpd W)⟩, hn1, hn2⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨-, hr⟩, h1, h2⟩ := hk
    refine ⟨⟨h1, h2⟩, dvd_mul_right W k, fun p' hp' hpp hpd => ?_⟩
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
    · exact hWp p' hp' hpp h
    · exact hr p' hp' hpp h
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2.1
  · intro k _
    exact Nat.mul_div_cancel_left k hW
  · intro n hn
    simp only [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2.1]

/-- For `z ≥ 2`, `Y ≥ 1` and `Y < z^{K+1}`, the `z`-rough `k ∈ [1, Y]` are the products of the non-increasing tuples
of at most `K` primes at least `z`, the empty tuple included. -/
theorem sum_rough_tuples {z Y : ℕ} (hz : 2 ≤ z) (hY : 1 ≤ Y) {M : Type*} [AddCommMonoid M] (G : ℕ → M) (K : ℕ)
    (hK : Y < z ^ (K + 1)) :
    ∑ k ∈ (Finset.Icc 1 Y).filter (fun k => ∀ p < z, p.Prime → ¬ p ∣ k), G k =
      ∑ t ∈ Finset.range (K + 1), ∑ y ∈ SieveRoughTuple.tuples z Y t, G (∏ a, y a) := by
  have hsplit : (Finset.Icc 1 Y).filter (fun k => ∀ p < z, p.Prime → ¬ p ∣ k) =
      insert 1 ((Finset.Icc 2 Y).filter (fun k => ∀ p < z, p.Prime → ¬ p ∣ k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨h1, h2⟩, hr⟩
      rcases (show k = 1 ∨ 2 ≤ k by omega) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨⟨h, h2⟩, hr⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, hr⟩)
      · exact ⟨⟨le_rfl, hY⟩, fun p _ hp hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)⟩
      · exact ⟨⟨by omega, h2⟩, hr⟩
  have h1 : (1 : ℕ) ∉ (Finset.Icc 2 Y).filter (fun k => ∀ p < z, p.Prime → ¬ p ∣ k) := by
    simp
  rw [hsplit, Finset.sum_insert h1, SieveRoughTuple.sum_rough_eq hz G K hK, SieveTypeIIR.sum_Icc_one,
    Finset.sum_range_succ', add_comm]
  congr 1
  have h0 : SieveRoughTuple.tuples z Y 0 = {fun i => i.elim0} := by
    ext y
    simp only [SieveRoughTuple.tuples, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
    constructor
    · intro _
      funext i
      exact i.elim0
    · rintro rfl
      refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
      simpa using hY
  rw [h0, Finset.sum_singleton]
  simp

section TypeII

open Classical

/-- **Type II with comparisons without pivots.** `SieveStops2.typeII_cmp` for comparisons with coefficients in
`{−1, 0, 1}`: those with a nonzero coefficient are pivoted, and those without one become conditions on `m`. -/
theorem typeII_gcmp (K₀ J₀ : ℕ) {e₁ Λ₁ : ℝ} (he₁ : 0 < e₁) (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (P₁ P₂ : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P₁ P₂ →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ∀ (acoef : ℕ → ℂ), (∀ m, ‖acoef m‖ ≤ 1) → ∀ (n : ℕ), n + 1 ≤ K₀ →
      ∀ (l : List (GCmp (n + 1))), l.length ≤ J₀ → (∀ C ∈ l, ∀ m ∈ S, C.c m ≤ Λ₁ * Real.log q) →
      (∀ m ∈ S, ∀ x : Fin (n + 1) → ℕ, (∀ i, (x i).Prime) → (∀ C ∈ l, C.holds m x) →
        (∀ i, 2 * (q : ℝ) ^ e₁ ≤ x i) ∧ (m : ℝ) * ∏ i, (x i : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ)) →
      ‖∑ m ∈ S, ∑ x ∈ Fintype.piFinset (fun _ : Fin (n + 1) =>
          SieveTypeIIU.primesLe ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊),
          (if ∀ C ∈ l, C.holds m x then acoef m * dw q a (m * ∏ i, x i) else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveStops2.typeII_cmp K₀ J₀ he₁ hΛ₁
  refine ⟨δ, hδ, q₀, ?_⟩
  intro q _ hq a ha P₁ P₂ S hS hP₁ hP₂ acoef hacoef n hn l hl hc hsupp
  set S' := S.filter (fun m => ∀ C ∈ l, (∀ i, C.e i = 0) → C.holds m (fun _ => 1)) with hS'
  have hsum : ∑ m ∈ S, ∑ x ∈ Fintype.piFinset (fun _ : Fin (n + 1) =>
        SieveTypeIIU.primesLe ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊),
        (if ∀ C ∈ l, C.holds m x then acoef m * dw q a (m * ∏ i, x i) else 0) =
      ∑ m ∈ S', ∑ x ∈ Fintype.piFinset (fun _ : Fin (n + 1) =>
        SieveTypeIIU.primesLe ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊),
        (if ∀ C' ∈ pivoted l, C'.holds m x then acoef m * dw q a (m * ∏ i, x i) else 0) := by
    rw [hS', Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hm
    · refine Finset.sum_congr rfl fun x _ => ?_
      have : (∀ C ∈ l, C.holds m x) ↔ ∀ C' ∈ pivoted l, C'.holds m x := by
        rw [holds_iff_pivoted]; tauto
      simp only [this]
    · refine Finset.sum_eq_zero fun x _ => ?_
      rw [ite_eq_right]
      intro h
      exact hm ((holds_iff_pivoted l m x).1 h).2
  rw [hsum]
  refine hq₀ q hq a ha P₁ P₂ S' ((Finset.filter_subset _ _).trans hS) hP₁ hP₂ acoef hacoef n hn (pivoted l)
    ((length_pivoted_le l).trans hl) ?_ ?_
  · intro C' hC' m hm
    obtain ⟨C, hC, hne, rfl⟩ := mem_pivoted.1 hC'
    exact hc C hC m (Finset.mem_filter.1 hm).1
  · intro m hm x hx hall
    rw [hS', Finset.mem_filter] at hm
    exact hsupp m hm.1 x hx ((holds_iff_pivoted l m x).2 ⟨hall, hm.2⟩)

/-- `typeII_gcmp` for any number `K ≥ 1` of primes. -/
theorem typeII_gcmp' (K₀ J₀ : ℕ) {e₁ Λ₁ : ℝ} (he₁ : 0 < e₁) (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (P₁ P₂ : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P₁ P₂ →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ∀ (acoef : ℕ → ℂ), (∀ m, ‖acoef m‖ ≤ 1) → ∀ (K : ℕ), 1 ≤ K → K ≤ K₀ →
      ∀ (l : List (GCmp K)), l.length ≤ J₀ → (∀ C ∈ l, ∀ m ∈ S, C.c m ≤ Λ₁ * Real.log q) →
      (∀ m ∈ S, ∀ x : Fin K → ℕ, (∀ i, (x i).Prime) → (∀ C ∈ l, C.holds m x) →
        (∀ i, 2 * (q : ℝ) ^ e₁ ≤ x i) ∧ (m : ℝ) * ∏ i, (x i : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ)) →
      ‖∑ m ∈ S, ∑ x ∈ Fintype.piFinset (fun _ : Fin K =>
          SieveTypeIIU.primesLe ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊),
          (if ∀ C ∈ l, C.holds m x then acoef m * dw q a (m * ∏ i, x i) else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
  obtain ⟨δ, hδ, q₀, hq₀⟩ := typeII_gcmp K₀ J₀ he₁ hΛ₁
  refine ⟨δ, hδ, q₀, ?_⟩
  intro q _ hq a ha P₁ P₂ S hS hP₁ hP₂ acoef hacoef K hK1 hK l hl hc hsupp
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
  exact hq₀ q hq a ha P₁ P₂ S hS hP₁ hP₂ acoef hacoef n hK l hl hc hsupp

/-- The comparisons of the upper window: the region, the cofactor's roughness and the range. -/
noncomputable def cmpsTU (k' : ℕ) (Ω : List (GCmp (k' + 1))) (N₁ N₂ : ℝ) : List (GCmp (k' + 1)) :=
  Ω.map GCmp.const ++ [grough (Fin.last k'), grangeLo N₁, grangeHi N₂]

/-- **Chains times a rough cofactor in the window.** Fix `e₀ > 0`, `k′`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and
`q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over the `(k′ + 1)`-tuples of primes up to
`N₂ = ⌊2q^L⌋` that satisfy at most `J₀` comparisons `Ω` (with `m`-parts at most `Λ₁ log q` at `m = 0`), each such
tuple having its entries at least `q^{e₀}` and its last entry least, and `W₀ < ∏rt ≤ W₁`. Let `W₁ ≤ N₁ = ⌊q^L⌋`,
`q^{0.401L} ≤ ⌊N₁/W₁⌋` and `⌊N₂/(W₀ + 1)⌋ ≤ q^{0.485L}`. Then the multiples `n ∈ (N₁, N₂]` of `∏rt` with no prime
factor below `rt`'s last entry, summed over `rt`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`. -/
theorem chainTU_bound {e₀ : ℝ} (he₀ : 0 < e₀) (k' J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (W₀ W₁ : ℕ) (Ω : List (GCmp (k' + 1))), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ (∀ i, rt (Fin.last k') ≤ rt i) ∧ W₀ < ∏ i, rt i ∧ ∏ i, rt i ≤ W₁) →
      W₁ ≤ ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ ((⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ / W₁ : ℕ) : ℝ) →
      ((⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ / (W₀ + 1) : ℕ) : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊,
            dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
  obtain ⟨δ, hδ, q₁, hq₁⟩ := typeII_gcmp (k' + 2) (J₀ + 3) (half_pos he₀)
    (show (0 : ℝ) ≤ Λ₁ + 2333 / 1000 + 1 by positivity)
  have hev1 := (tendsto_rpow_atTop (half_pos he₀)).eventually_ge_atTop (2 : ℝ)
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev1)
  refine ⟨δ, hδ, max (max q₁ q₂) 3, ?_⟩
  intro q _ hq a ha W₀ W₁ Ω hΩlen hΩc hΩ hW₁ hP₁ hP₂
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqe : (2 : ℝ) ≤ (q : ℝ) ^ (e₀ / 2) := hq₂ q (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq)
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  set N₁ := ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ with hN₁
  set N₂ := ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ with hN₂
  set S := Finset.Ioc (N₁ / W₁) (N₂ / (W₀ + 1)) with hSdef
  have hX1 : (1 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hN₁1 : 1 ≤ N₁ := Nat.le_floor (by exact_mod_cast hX1)
  have hN₁N₂ : N₁ ≤ N₂ := Nat.floor_le_floor (by linarith)
  have hN₂1 : 1 ≤ N₂ := le_trans hN₁1 hN₁N₂
  have hN₁le : (N₁ : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Nat.floor_le (by positivity)
  have hN₂le : (N₂ : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) := Nat.floor_le (by positivity)
  have hP₁1 : 1 ≤ N₁ / W₁ := by
    have : (1 : ℝ) ≤ (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    exact_mod_cast this.trans hP₁
  have hqe2 : (2 : ℝ) * (q : ℝ) ^ (e₀ / 2) ≤ (q : ℝ) ^ e₀ := by
    have : (q : ℝ) ^ e₀ = (q : ℝ) ^ (e₀ / 2) * (q : ℝ) ^ (e₀ / 2) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [this]
    have : (0 : ℝ) ≤ (q : ℝ) ^ (e₀ / 2) := by positivity
    nlinarith
  -- the tuples
  have hRT : ∀ rt ∈ RTg (k' + 1) N₂ Ω, (∀ i, (rt i).Prime) ∧ (∀ C ∈ Ω, C.holds 0 rt) := by
    intro rt hrt
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hrt
    exact ⟨fun i => (SieveTypeIIU.mem_primesLe.1 (hrt.1 i)).2, hrt.2⟩
  -- each tuple: its multiples as cofactors in the window
  have hterm : ∀ rt ∈ RTg (k' + 1) N₂ Ω,
      ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0) =
        ∑ k ∈ S, (if rt (Fin.last k') ≤ Nat.minFac k ∧ N₁ < (∏ i, rt i) * k ∧ (∏ i, rt i) * k ≤ N₂
          then dw q a (k * ∏ i, rt i) else 0) := by
    intro rt hrt
    obtain ⟨hrtp, hrtΩ⟩ := hRT rt hrt
    obtain ⟨-, hlast, hlo, hhi⟩ := hΩ rt hrtp hrtΩ
    have hW0 : 0 < ∏ i, rt i := Finset.prod_pos fun i _ => (hrtp i).pos
    have hWr : rough (rt (Fin.last k')) (∏ i, rt i) := by
      intro ℓ hℓp hℓ hd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 hd
      rw [(Nat.prime_dvd_prime_iff_eq hℓ (hrtp i)).1 hi] at hℓp
      have := hlast i
      omega
    rw [sum_cofactor_range (dw q a) hW0 hWr hlo hhi hW₁ hP₁1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (∏ i, rt i) k]
  have hsum : ∑ rt ∈ RTg (k' + 1) N₂ Ω, ∑ n ∈ Finset.Ioc N₁ N₂,
      dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0) =
      ∑ k ∈ S, ∑ x ∈ Fintype.piFinset (fun _ : Fin (k' + 1) => SieveTypeIIU.primesLe N₂),
        (if ∀ C ∈ cmpsTU k' Ω N₁ N₂, C.holds k x then (fun _ => (1 : ℂ)) k * dw q a (k * ∏ i, x i) else 0) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := by
      have := (Finset.mem_Ioc.1 hk).1
      omega
    rw [RTg, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Fintype.mem_piFinset] at hx
    have hx1 : ∀ i, 1 ≤ x i := fun i => (SieveTypeIIU.mem_primesLe.1 (hx i)).2.one_lt.le
    have hiff : (∀ C ∈ cmpsTU k' Ω N₁ N₂, C.holds k x) ↔ (∀ C ∈ Ω, C.holds 0 x) ∧
        (x (Fin.last k') ≤ Nat.minFac k ∧ N₁ < (∏ i, x i) * k ∧ (∏ i, x i) * k ≤ N₂) := by
      have hN₁0 : (0 : ℝ) < N₁ := by exact_mod_cast hN₁1
      have hN₂0 : (0 : ℝ) < N₂ := by exact_mod_cast hN₂1
      have hc : ((∏ i, x i) * k : ℕ) = ((k : ℝ) * ∏ i, (x i : ℝ)) := by push_cast; ring
      unfold cmpsTU
      simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
        false_implies, implies_true, and_true, GCmp.const_holds, grough_holds _ k hx1,
        grangeLo_holds hN₁0 hk1 hx1, grangeHi_holds hN₂0 hk1 hx1]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨h1, h2, ?_, ?_⟩
        · have : (N₁ : ℝ) < ((∏ i, x i) * k : ℕ) := by rw [hc]; exact h3
          exact_mod_cast this
        · have : (((∏ i, x i) * k : ℕ) : ℝ) ≤ N₂ := by rw [hc]; exact h4
          exact_mod_cast this
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨h1, h2, ?_, ?_⟩
        · rw [← hc]; exact_mod_cast h3
        · rw [← hc]; exact_mod_cast h4
    by_cases hΩx : ∀ C ∈ Ω, C.holds 0 x
    · rw [ite_eq_left hΩx]
      by_cases hc : x (Fin.last k') ≤ Nat.minFac k ∧ N₁ < (∏ i, x i) * k ∧ (∏ i, x i) * k ≤ N₂
      · rw [ite_eq_left hc, ite_eq_left (hiff.2 ⟨hΩx, hc⟩), one_mul]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.1 h).2)]
    · rw [ite_eq_right hΩx, ite_eq_right (fun h => hΩx (hiff.1 h).1)]
  rw [hsum]
  -- the bound
  have hlog : ∀ (t c : ℝ), 0 < t → t ≤ (q : ℝ) ^ c → Real.log t ≤ c * Real.log q := fun t c ht h => by
    rw [← Real.log_rpow hq0]
    exact Real.log_le_log ht h
  have hΛl : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq.le
  have hB1 : (2333 / 1000 : ℝ) * Real.log q ≤ (Λ₁ + 2333 / 1000 + 1) * Real.log q := by
    rw [add_mul, add_mul, one_mul]
    linarith
  have hB2 : (2333 / 1000 + 1 : ℝ) * Real.log q ≤ (Λ₁ + 2333 / 1000 + 1) * Real.log q := by
    rw [add_mul, add_mul, add_mul, one_mul]
    linarith
  have hB3 : Λ₁ * Real.log q ≤ (Λ₁ + 2333 / 1000 + 1) * Real.log q := by
    rw [add_mul, add_mul, one_mul]
    have : (0 : ℝ) ≤ 2333 / 1000 * Real.log q := by positivity
    linarith
  refine hq₁ q hq1 a ha (N₁ / W₁) (N₂ / (W₀ + 1)) S (subset_refl _) hP₁ hP₂ (fun _ => 1) (fun _ => by simp)
    k' (by omega) (cmpsTU k' Ω N₁ N₂) (by unfold cmpsTU; simp; omega) ?_ ?_
  · intro C hC m hm
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ioc.1 hm).1
      omega
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmP : (m : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := by
      have h1 : (m : ℝ) ≤ ((N₂ / (W₀ + 1) : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Ioc.1 hm).2
      have h2 : (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      linarith
    have hlm := (hlog m (2333 / 1000) (by linarith) hmP).trans hB1
    have hlm0 : 0 ≤ Real.log m := Real.log_nonneg hm1'
    have hmf : Real.log (Nat.minFac m) ≤ Real.log m :=
      Real.log_le_log (by exact_mod_cast Nat.minFac_pos m) (by exact_mod_cast Nat.minFac_le (by omega))
    have hN₁l : 0 ≤ Real.log N₁ := Real.log_nonneg (by exact_mod_cast hN₁1)
    have hN₂q : (N₂ : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) := by
      rw [Real.rpow_add hq0, Real.rpow_one]
      have h0 : (0 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := by positivity
      have h1 : 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) * q := by
        have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ q by linarith) h0
        linarith
      linarith
    have hlN₂ := (hlog N₂ (2333 / 1000 + 1) (by exact_mod_cast hN₂1) hN₂q).trans hB2
    unfold cmpsTU at hC
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
    rcases hC with ⟨C₀, hC₀, rfl⟩ | rfl | rfl | rfl
    · exact (hΩc C₀ hC₀).trans hB3
    · show Real.log (Nat.minFac m) ≤ _
      linarith
    · show Real.log m - Real.log N₁ ≤ _
      linarith
    · show Real.log N₂ - Real.log m ≤ _
      linarith
  · intro m hm x hx hall
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ioc.1 hm).1
      omega
    have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
    unfold cmpsTU at hall
    simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
      false_implies, implies_true, and_true, GCmp.const_holds] at hall
    obtain ⟨hΩx, -, -, hhi⟩ := hall
    have hN₂0 : (0 : ℝ) < N₂ := by exact_mod_cast hN₂1
    refine ⟨fun i => (hqe2.trans ((hΩ x hx hΩx).1 i)), ?_⟩
    exact ((grangeHi_holds hN₂0 hm1 hx1).1 hhi).trans hN₂le

set_option maxHeartbeats 1600000 in
/-- **Chains with a product of some of their primes in the window.** Fix `e₀ > 0`, `k′`, `J₀` and `Λ₁ ≥ 0`. There
are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over the `(k′ + 1)`-tuples of primes
up to `N₂ = ⌊2q^L⌋` that satisfy at most `J₀` comparisons `Ω` (with `m`-parts at most `Λ₁ log q` at `m = 0`), each
such tuple strictly decreasing, with entries at least `q^{e₀}` and `P₁ < ∏_{i∈S} rt_i ≤ P₂`, where `q^{0.401L} ≤ P₁` and
`P₂ ≤ q^{0.485L}`. Then the multiples `n ∈ (N₁, N₂]` of `∏rt` with no prime factor below `rt`'s last entry, summed
over `rt`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`. -/
theorem chainTL_bound {e₀ : ℝ} (he₀ : 0 < e₀) (k' J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (S : Finset (Fin (k' + 1))) (Ω : List (GCmp (k' + 1))) (P₁ P₂ : ℕ), Ω.length ≤ J₀ →
      (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ P₁ < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ P₂) →
      ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊,
            dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
  set Kmax : ℕ := ⌈(2333 / 1000 + 1) / e₀⌉₊ with hKmax
  obtain ⟨δ, hδ, q₁, hq₁⟩ := typeII_gcmp' (Kmax + k' + 2) (J₀ + Kmax * Kmax + Kmax + 2) (half_pos he₀)
    (show (0 : ℝ) ≤ Λ₁ + 2 * (2333 / 1000) + 2 by positivity)
  have hev1 := (tendsto_rpow_atTop (half_pos he₀)).eventually_ge_atTop (2 : ℝ)
  have hev2 := (tendsto_rpow_atTop (half_pos hδ)).eventually_ge_atTop ((Kmax : ℝ) + 1)
  have hev3 := (tendsto_rpow_atTop
    (show (0 : ℝ) < 2333 / 1000 - 485 / 1000 * (2333 / 1000) by norm_num)).eventually_ge_atTop (2 : ℝ)
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (hev1.and (hev2.and hev3)))
  refine ⟨δ / 2, half_pos hδ, max (max q₁ q₂) 3, ?_⟩
  intro q _ hq a ha S Ω P₁ P₂ hΩlen hΩc hP₁ hP₂ hreg
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  obtain ⟨hqe, hqK, hq485⟩ := hq₂ q (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq)
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  set N₁ := ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ with hN₁
  set N₂ := ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ with hN₂
  have hX1 : (1 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hN₁1 : 1 ≤ N₁ := Nat.le_floor (by exact_mod_cast hX1)
  have hN₁N₂ : N₁ ≤ N₂ := Nat.floor_le_floor (by linarith)
  have hN₂1 : 1 ≤ N₂ := le_trans hN₁1 hN₁N₂
  have hN₂le : (N₂ : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) := Nat.floor_le (by positivity)
  have hqe2 : (2 : ℝ) * (q : ℝ) ^ (e₀ / 2) ≤ (q : ℝ) ^ e₀ := by
    have : (q : ℝ) ^ e₀ = (q : ℝ) ^ (e₀ / 2) * (q : ℝ) ^ (e₀ / 2) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [this]
    have : (0 : ℝ) ≤ (q : ℝ) ^ (e₀ / 2) := by positivity
    nlinarith
  -- `P₂ < N₁`
  have hP₂N₁ : P₂ < N₁ := by
    have h1 : (q : ℝ) ^ (2333 / 1000 : ℝ) = (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) *
        (q : ℝ) ^ (2333 / 1000 - 485 / 1000 * (2333 / 1000) : ℝ) := by
      rw [← Real.rpow_add hq0]; ring_nf
    have h2 : (1 : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have h3 : (q : ℝ) ^ (2333 / 1000 : ℝ) - 1 < N₁ := Nat.sub_one_lt_floor _
    have h4 : (P₂ : ℝ) < N₁ := by nlinarith
    exact_mod_cast h4
  -- the tuples' length
  have hpK : ∀ p : ℕ, (q : ℝ) ^ e₀ ≤ p → N₂ < p ^ (Kmax + 1) := by
    intro p hp
    have hK : (2333 / 1000 + 1 : ℝ) ≤ e₀ * (Kmax + 1) := by
      have := Nat.le_ceil ((2333 / 1000 + 1) / e₀)
      rw [← hKmax, div_le_iff₀ he₀] at this
      nlinarith
    have hpow : (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) ≤ (p : ℝ) ^ (Kmax + 1) := by
      calc (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) ≤ (q : ℝ) ^ (e₀ * (Kmax + 1)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hK
        _ = ((q : ℝ) ^ e₀) ^ (Kmax + 1) := by rw [Real.rpow_mul hq0.le, ← Real.rpow_natCast]; push_cast; ring_nf
        _ ≤ (p : ℝ) ^ (Kmax + 1) := pow_le_pow_left₀ (by positivity) hp _
    have hlt : (N₂ : ℝ) < (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) := by
      calc (N₂ : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) := hN₂le
        _ < 3 * (q : ℝ) ^ (2333 / 1000 : ℝ) := by linarith
        _ ≤ (q : ℝ) * (q : ℝ) ^ (2333 / 1000 : ℝ) := by nlinarith
        _ = (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) := by rw [Real.rpow_add hq0, Real.rpow_one]; ring
    exact_mod_cast lt_of_lt_of_le hlt hpow
  -- each chain: its multiples as cofactor tuples
  have hRT : ∀ rt ∈ RTg (k' + 1) N₂ Ω, (∀ i, (rt i).Prime) ∧ (∀ C ∈ Ω, C.holds 0 rt) := by
    intro rt hrt
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hrt
    exact ⟨fun i => (SieveTypeIIU.mem_primesLe.1 (hrt.1 i)).2, hrt.2⟩
  have hterm : ∀ rt ∈ RTg (k' + 1) N₂ Ω,
      ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0) =
        ∑ t ∈ Finset.range (Kmax + 1), ∑ y ∈ SieveRoughTuple.tuples (rt (Fin.last k')) N₂ t,
          (if N₁ < (∏ i, rt i) * ∏ a, y a ∧ (∏ i, rt i) * ∏ a, y a ≤ N₂
            then dw q a ((∏ i, rt i) * ∏ a, y a) else 0) := by
    intro rt hrt
    obtain ⟨hrtp, hrtΩ⟩ := hRT rt hrt
    obtain ⟨hsa, hge, -, -⟩ := hreg rt hrtp hrtΩ
    have hW0 : 0 < ∏ i, rt i := Finset.prod_pos fun i _ => (hrtp i).pos
    have hWr : rough (rt (Fin.last k')) (∏ i, rt i) := by
      intro ℓ hℓp hℓ hd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 hd
      rw [(Nat.prime_dvd_prime_iff_eq hℓ (hrtp i)).1 hi] at hℓp
      have := hsa.antitone (Fin.le_last i)
      omega
    rw [sum_mult_eq (dw q a) hW0 hWr]
    exact sum_rough_tuples (hrtp _).two_le hN₂1
      (fun k => if N₁ < (∏ i, rt i) * k ∧ (∏ i, rt i) * k ≤ N₂ then dw q a ((∏ i, rt i) * k) else 0) Kmax
      (hpK _ (hge _))
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  -- each size `t`
  have hbound : ∀ t ∈ Finset.range (Kmax + 1),
      ‖∑ rt ∈ RTg (k' + 1) N₂ Ω, ∑ y ∈ SieveRoughTuple.tuples (rt (Fin.last k')) N₂ t,
          (if N₁ < (∏ i, rt i) * ∏ a, y a ∧ (∏ i, rt i) * ∏ a, y a ≤ N₂
            then dw q a ((∏ i, rt i) * ∏ a, y a) else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
    intro t ht
    have htK : t ≤ Kmax := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    have hreg' : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ P₁ < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ P₂ := fun rt hp hΩ' =>
      ⟨(hreg rt hp hΩ').1, (hreg rt hp hΩ').2.2⟩
    rw [sum_TL_eq S Ω t hreg' hN₁1 hN₁N₂ le_rfl (le_trans hP₂N₁.le hN₁N₂) (dw q a)]
    rcases Nat.eq_zero_or_pos (t + Sᶜ.card) with h0 | hpos
    · -- no primes left: `n = ∏_S rt ≤ P₂ < N₁`
      have hSc : Sᶜ.card = 0 := by omega
      rw [Finset.sum_eq_zero, norm_zero]
      · positivity
      intro m hm
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [ite_eq_right]
      intro hall
      exfalso
      rw [Mset, Finset.mem_filter, Finset.mem_Ioc] at hm
      obtain ⟨⟨-, hmP₂⟩, hcard, hprodm⟩ := hm
      have hx1 : ∀ i, 1 ≤ x i := fun i => by
        exact (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 hx i)).2.one_lt.le
      have hf1 : ∀ u, 1 ≤ factS (S := S) m u := fun u =>
        (Nat.prime_of_mem_primeFactors (SieveStops2.desc_mem hcard u)).one_lt.le
      obtain ⟨-, -, -, hlo, -⟩ := (cmpsTL_holds (S := S) (t := t) Ω (by exact_mod_cast hN₁1)
        (by exact_mod_cast hN₂1) m x hx1 hf1).1 hall
      have ht0 : t = 0 := by omega
      subst ht0
      have hprod : (∏ i, (merge S (factS (S := S) m) (fun v => x (Fin.natAdd 0 v)) i : ℝ)) = m := by
        rw [prod_split (S := S)]
        simp only [merge_inl, merge_inr]
        have h1 : ∏ v : Fin Sᶜ.card, ((x (Fin.natAdd 0 v) : ℕ) : ℝ) = 1 := by
          rw [Fintype.prod_eq_one]
          intro v
          exact absurd v.isLt (by omega)
        rw [h1, mul_one]
        have : (∏ u, factS (S := S) m u : ℕ) = m := by
          unfold factS
          rw [SieveStops2.prod_desc hcard, hprodm]
        exact_mod_cast this
      rw [hprod, Fintype.prod_empty, mul_one] at hlo
      have : (m : ℝ) ≤ P₂ := by exact_mod_cast hmP₂
      have : (P₂ : ℝ) < N₁ := by exact_mod_cast hP₂N₁
      linarith
    · -- the Type II bound
      have hlog : ∀ (t' c : ℝ), 0 < t' → t' ≤ (q : ℝ) ^ c → Real.log t' ≤ c * Real.log q := fun t' c ht' h => by
        rw [← Real.log_rpow hq0]
        exact Real.log_le_log ht' h
      have hN₂q : (N₂ : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) := by
        rw [Real.rpow_add hq0, Real.rpow_one]
        have h0 : (0 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := by positivity
        have h1 : 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) * q := by
          have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ q by linarith) h0
          linarith
        linarith
      have hlN₂ := hlog N₂ (2333 / 1000 + 1) (by exact_mod_cast hN₂1) hN₂q
      have hΛl : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq.le
      have hB0 : 0 ≤ (Λ₁ + 2333 / 1000 + 1) * Real.log q := by positivity
      have hBsplit : (Λ₁ + 2333 / 1000 + 1) * Real.log q = Λ₁ * Real.log q + (2333 / 1000 + 1) * Real.log q := by
        ring
      have hLq : 0 ≤ (2333 / 1000 + 1) * Real.log q := by positivity
      have hΛB : Λ₁ * Real.log q ≤ (Λ₁ + 2333 / 1000 + 1) * Real.log q := by rw [hBsplit]; linarith
      have hN₂B : Real.log (N₂ : ℝ) ≤ (Λ₁ + 2333 / 1000 + 1) * Real.log q := by rw [hBsplit]; linarith
      have hN₁R : (1 : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hN₁1
      have hcle := cmpsTL_c_le S t Ω (N₁ := (N₁ : ℝ)) (N₂ := (N₂ : ℝ)) (P₁ := P₁) (P₂ := P₂)
        (B := (Λ₁ + 2333 / 1000 + 1) * Real.log q) (fun C hC => (hΩc C hC).trans hΛB) hB0 hN₁R hN₂B
      have h := hq₁ q hq1 a ha P₁ P₂ (Mset S P₁ P₂) (Finset.filter_subset _ _) hP₁ hP₂ (fun _ => 1)
        (fun _ => by simp) (t + Sᶜ.card) hpos (by have := Finset.card_le_univ Sᶜ; simp at this; omega)
        (cmpsTL S t Ω N₁ N₂) ?_ ?_ ?_
      · simpa only [one_mul] using h
      · unfold cmpsTL
        rw [List.length_map]
        refine (length_fullTL_le k' t Ω N₁ N₂).trans ?_
        have : t * t ≤ Kmax * Kmax := Nat.mul_le_mul htK htK
        omega
      · intro C hC m hm
        have h1 := hcle C hC m hm
        have hm1 : 1 ≤ m := by
          have := (Finset.mem_Ioc.1 (Finset.filter_subset _ _ hm)).1
          have hP₁1 : (1 : ℝ) ≤ P₁ := le_trans (Real.one_le_rpow (by linarith) (by norm_num)) hP₁
          have : (1 : ℕ) ≤ P₁ := by exact_mod_cast hP₁1
          omega
        have hmq : (m : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := by
          have h1 : (m : ℝ) ≤ P₂ := by exact_mod_cast (Finset.mem_Ioc.1 (Finset.filter_subset _ _ hm)).2
          have h2 : (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          linarith
        have hlm := hlog m (2333 / 1000) (by exact_mod_cast hm1) hmq
        have : (Λ₁ + 2333 / 1000 + 1) * Real.log q + 2333 / 1000 * Real.log q =
            (Λ₁ + 2 * (2333 / 1000) + 1) * Real.log q := by ring
        nlinarith
      · intro m hm x hx hall
        rw [Mset, Finset.mem_filter] at hm
        obtain ⟨-, hcard, hprodm⟩ := hm
        have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
        have hfp : ∀ u, (factS (S := S) m u).Prime := fun u =>
          Nat.prime_of_mem_primeFactors (SieveStops2.desc_mem hcard u)
        have hf1 : ∀ u, 1 ≤ factS (S := S) m u := fun u => (hfp u).one_lt.le
        obtain ⟨hΩ', -, hlast, -, hhi⟩ := (cmpsTL_holds (S := S) (t := t) Ω (by exact_mod_cast hN₁1)
          (by exact_mod_cast hN₂1) m x hx1 hf1).1 hall
        set rt := merge S (factS (S := S) m) (fun v => x (Fin.natAdd t v)) with hrt
        have hrtp : ∀ i, (rt i).Prime := by
          intro i
          obtain ⟨y, rfl⟩ := (eS S).surjective i
          rcases y with u | v
          · rw [hrt, merge_inl]; exact hfp u
          · rw [hrt, merge_inr]; exact hx _
        obtain ⟨-, hge, -, -⟩ := hreg rt hrtp hΩ'
        have hprod : (m : ℝ) * ∏ i, (x i : ℝ) = (∏ i, (rt i : ℝ)) * ∏ a, (x (Fin.castAdd Sᶜ.card a) : ℝ) := by
          rw [prod_split (S := S) (fun i => (rt i : ℝ)), Fin.prod_univ_add]
          simp only [hrt, merge_inl, merge_inr]
          have : (∏ u, factS (S := S) m u : ℕ) = m := by
            unfold factS
            rw [SieveStops2.prod_desc hcard, hprodm]
          have h' : (∏ u, (factS (S := S) m u : ℝ)) = m := by exact_mod_cast this
          rw [h']
          ring
        refine ⟨fun i => ?_, by rw [hprod]; linarith⟩
        refine Fin.addCases (fun a => ?_) (fun v => ?_) i
        · have h1 : (rt (Fin.last k') : ℝ) ≤ x (Fin.castAdd Sᶜ.card a) := by exact_mod_cast hlast a
          linarith [hge (Fin.last k')]
        · have h1 : rt (eS S (Sum.inr v)) = x (Fin.natAdd t v) := by rw [hrt, merge_inr]
          have := hge (eS S (Sum.inr v))
          rw [h1] at this
          linarith
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ hbound).trans ?_
  rw [Finset.card_range, nsmul_eq_mul]
  calc ((Kmax + 1 : ℕ) : ℝ) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ))
      ≤ (q : ℝ) ^ (δ / 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ)) :=
        mul_le_mul_of_nonneg_right (by push_cast; exact hqK) (by positivity)
    _ = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ / 2 : ℝ) := by
        rw [mul_left_comm, ← Real.rpow_add hq0]
        congr 2
        ring

end TypeII

end SieveChain
