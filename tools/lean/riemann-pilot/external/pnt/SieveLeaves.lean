/-
# Round 604: the leaves' estimates on families of atoms (milestone M8)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. `gA q a m = 1[m ≡ a]` and `gB q m = 1[(m, q) = 1]/φ(q)`; `L`, `w₁` and `w₂` are a route's parameters
(`SieveRoute.Route`); `N1 q = ⌊q^L⌋`, `N2 q = ⌊2q^L⌋`; `ThrOK q spec` says that the atoms' thresholds lie in
`[1, q^{L+1}]`. The cells are those of `SieveCert`'s grid (`SieveCert.Grid`).

* `exists_inside`: a box of cells that `SieveCert.surelyEval` passes has a set `T` of its primes whose subset sums
  over the box stay inside `U = (u₁, u₂) ∪ (1 − u₂, 1 − u₁)`.
* `window_lo`, `window_hi`: for `x > 1` and primes in their cells, `⌊x^{B/DEN}⌋ < ∏_T rt` when `B` is below the box's
  lower sum over `T`, and `∏_T rt ≤ ⌊x^{B/DEN}⌋` when `B` is above its upper sum.
* `prod_proper_le`: a proper subset of a strictly decreasing tuple of positive integers has product at most that of all
  but the last entry.
* `TL_spec`, `TU_spec`: `SieveChain.chainTL_bound` and `chainTU_bound` (with `RouteOK` and `hII`) on a family of at most
  `18` atoms with `ThrOK`, as bounds on `|famI(g_A) − famI(g_B)|`.
* `P6_spec`: `SieveProp6.prop6` (with `RouteOK` and `hII`) on a family of at most `18` atoms with `ThrOK` and nonzero
  coefficients (`NZ`), as a bound on `|famJ(g_A, z₀) − famJ(g_B, z₀)|`.

These connect M8's families (`SieveDecomp`) with the Type II bounds and Proposition 6. `dw_eq`, `sum_dw_famI` and
`sum_dw_famJ` write `SieveFamily.dw = gA − gB` on the families, and `RTg_eq_of_thrOK` and `RT_pivoted` identify a
family with the comparisons of its atoms.

Round 607 made the route's numbers and the certificate's grid parameters and the Type II estimate a hypothesis
(`hII`); the statements of earlier rounds are the case `SieveRoute.route2333` and `SieveCert.grid2333`, with
`SieveRoute.typeII2333` for `hII`.


The file imports `SieveBuch.lean`.
-/
import SieveBuch

open Real Finset SieveFamily SieveChain SieveDecomp SieveBuch SieveRoute
open SieveCert (V DEN H U1 U2 cand dec inKK ne3 counted4 surelyEval cell inside subsetSums)

namespace SieveLeaves

open Classical

/-! ### A box surely evaluable has one set of primes in a window -/

/-- Each subset-sum range of a box is the sum over a set of its sides. -/
theorem subsetSums_ofFn {k : ℕ} (f : Fin k → ℕ × ℕ) :
    ∀ s ∈ subsetSums (List.ofFn f), ∃ T : Finset (Fin k), s = (∑ t ∈ T, (f t).1, ∑ t ∈ T, (f t).2) := by
  induction k with
  | zero =>
    intro s hs
    simp only [List.ofFn_zero, subsetSums, List.mem_singleton] at hs
    exact ⟨∅, by simp [hs]⟩
  | succ k ih =>
    intro s hs
    simp only [List.ofFn_succ, subsetSums, List.mem_append, List.mem_map] at hs
    rcases hs with hs | ⟨s', hs', rfl⟩
    · obtain ⟨T, rfl⟩ := ih (fun t => f t.succ) s hs
      exact ⟨T.map (Fin.succEmb k), by simp [Finset.sum_map]⟩
    · obtain ⟨T, rfl⟩ := ih (fun t => f t.succ) s' hs'
      refine ⟨insert 0 (T.map (Fin.succEmb k)), ?_⟩
      have h0 : (0 : Fin (k + 1)) ∉ T.map (Fin.succEmb k) := by simp [Fin.succ_ne_zero]
      rw [Finset.sum_insert h0, Finset.sum_insert h0]
      simp [Finset.sum_map, add_comm]

/-- A box surely evaluable has a set of primes whose sums over the box stay inside `U`. -/
theorem exists_inside [SieveCert.Grid] {k : ℕ} (f : Fin k → ℕ × ℕ) (h : surelyEval (List.ofFn f) = true) :
    ∃ T : Finset (Fin k), inside (∑ t ∈ T, (f t).1) (∑ t ∈ T, (f t).2) = true := by
  simp only [surelyEval, List.any_eq_true] at h
  obtain ⟨s, hs, hin⟩ := h
  obtain ⟨T, rfl⟩ := subsetSums_ofFn f s hs
  exact ⟨T, hin⟩

/-- For `x > 0` and primes in the cells `c`, `∏_T rt ≥ x^{Σ_T e_{c_t}/DEN}`. -/
theorem box_lo [SieveCert.Grid] {x : ℝ} (hx : 0 < x) {k : ℕ} {c rt : Fin k → ℕ} (h : ∀ t, InC x (c t) (rt t))
    (T : Finset (Fin k)) :
    x ^ (((∑ t ∈ T, SieveCert.e (c t) : ℕ) : ℝ) / DEN) ≤ ∏ t ∈ T, (rt t : ℝ) := by
  rw [Nat.cast_sum, Finset.sum_div, Real.rpow_sum_of_pos hx]
  exact Finset.prod_le_prod₀ (fun t _ => Real.rpow_nonneg hx.le _) fun t _ => (h t).1

/-- For `x > 0` and primes in the cells `c`, `∏_T rt ≤ x^{Σ_T (e_{c_t} + H)/DEN}`. -/
theorem box_hi [SieveCert.Grid] {x : ℝ} (hx : 0 < x) {k : ℕ} {c rt : Fin k → ℕ} (h : ∀ t, InC x (c t) (rt t))
    (T : Finset (Fin k)) :
    ∏ t ∈ T, (rt t : ℝ) ≤ x ^ (((∑ t ∈ T, (SieveCert.e (c t) + H) : ℕ) : ℝ) / DEN) := by
  rw [Nat.cast_sum, Finset.sum_div, Real.rpow_sum_of_pos hx]
  refine Finset.prod_le_prod₀ (fun t _ => Nat.cast_nonneg _) fun t _ => ?_
  push_cast
  exact (h t).2.le

/-- Below the box: for `x > 1`, primes in the cells `c` and `B < Σ_T e_{c_t}`, `⌊x^{B/DEN}⌋ < ∏_T rt`. -/
theorem window_lo [SieveCert.Grid] {x : ℝ} (hx : 1 < x) {k : ℕ} {c rt : Fin k → ℕ} (h : ∀ t, InC x (c t) (rt t))
    {T : Finset (Fin k)} {B : ℕ} (hB : B < ∑ t ∈ T, SieveCert.e (c t)) :
    ⌊x ^ ((B : ℝ) / DEN)⌋₊ < ∏ t ∈ T, rt t := by
  have hD := SieveCert.DEN_pos'
  have h1 : x ^ ((B : ℝ) / DEN) < x ^ (((∑ t ∈ T, SieveCert.e (c t) : ℕ) : ℝ) / DEN) :=
    Real.rpow_lt_rpow_of_exponent_lt hx (div_lt_div_of_pos_right (by exact_mod_cast hB) hD)
  have h2 := box_lo (by linarith) h T
  have h3 : (⌊x ^ ((B : ℝ) / DEN)⌋₊ : ℝ) < ∏ t ∈ T, (rt t : ℝ) :=
    lt_of_le_of_lt (Nat.floor_le (Real.rpow_nonneg (by linarith) _)) (lt_of_lt_of_le h1 h2)
  exact_mod_cast h3

/-- Above the box: for `x > 1`, primes in the cells `c` and `Σ_T (e_{c_t} + H) < B`, `∏_T rt ≤ ⌊x^{B/DEN}⌋`. -/
theorem window_hi [SieveCert.Grid] {x : ℝ} (hx : 1 < x) {k : ℕ} {c rt : Fin k → ℕ} (h : ∀ t, InC x (c t) (rt t))
    {T : Finset (Fin k)} {B : ℕ} (hB : ∑ t ∈ T, (SieveCert.e (c t) + H) < B) :
    ∏ t ∈ T, rt t ≤ ⌊x ^ ((B : ℝ) / DEN)⌋₊ := by
  have hD := SieveCert.DEN_pos'
  have h1 : x ^ (((∑ t ∈ T, (SieveCert.e (c t) + H) : ℕ) : ℝ) / DEN) < x ^ ((B : ℝ) / DEN) :=
    Real.rpow_lt_rpow_of_exponent_lt hx (div_lt_div_of_pos_right (by exact_mod_cast hB) hD)
  have h2 := box_hi (by linarith) h T
  refine Nat.le_floor ?_
  push_cast
  exact (h2.trans h1.le)

/-- A proper subset of a strictly decreasing tuple of positive integers has product at most that of all but the last
entry. -/
theorem prod_proper_le {k' : ℕ} {rt : Fin (k' + 1) → ℕ} (hsa : StrictAnti rt) (hpos : ∀ t, 1 ≤ rt t)
    {T : Finset (Fin (k' + 1))} (hT : T ≠ Finset.univ) :
    ∏ t ∈ T, rt t ≤ ∏ t ∈ Finset.univ.erase (Fin.last k'), rt t := by
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, t₀ ∉ T := by
    by_contra h
    push Not at h
    exact hT (Finset.eq_univ_of_forall h)
  have h1 : ∏ t ∈ T, rt t ≤ ∏ t ∈ Finset.univ.erase t₀, rt t :=
    Finset.prod_le_prod_of_subset_of_one_le (fun t ht => Finset.mem_erase.2 ⟨fun h => ht₀ (h ▸ ht),
      Finset.mem_univ _⟩) fun t _ _ => hpos t
  have h2 : (∏ t ∈ Finset.univ.erase t₀, rt t) * rt t₀ = (∏ t ∈ Finset.univ.erase (Fin.last k'), rt t) *
      rt (Fin.last k') := by
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ _), Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  have h3 : rt (Fin.last k') ≤ rt t₀ := hsa.antitone (Fin.le_last t₀)
  have h4 : 0 < rt (Fin.last k') := hpos _
  have h5 : (∏ t ∈ Finset.univ.erase t₀, rt t) * rt (Fin.last k') ≤
      (∏ t ∈ Finset.univ.erase (Fin.last k'), rt t) * rt (Fin.last k') := by
    calc (∏ t ∈ Finset.univ.erase t₀, rt t) * rt (Fin.last k') ≤ (∏ t ∈ Finset.univ.erase t₀, rt t) * rt t₀ :=
          Nat.mul_le_mul_left _ h3
      _ = _ := h2
  exact h1.trans (Nat.le_of_mul_le_mul_right h5 h4)

/-! ### The weights, and the sums of `dw` -/

/-- `1[n ≡ a]`. -/
noncomputable def gA (q : ℕ) (a : ZMod q) (m : ℕ) : ℝ := if (m : ZMod q) = a then 1 else 0

/-- `1[(n, q) = 1]/φ(q)`. -/
noncomputable def gB (q : ℕ) (m : ℕ) : ℝ := if IsUnit (m : ZMod q) then (q.totient : ℝ)⁻¹ else 0

theorem gA_nonneg (q : ℕ) (a : ZMod q) (m : ℕ) : 0 ≤ gA q a m := by
  unfold gA
  split_ifs <;> norm_num

theorem dw_eq (q : ℕ) (a : ZMod q) (m : ℕ) : SieveFamily.dw q a m = ((gA q a m - gB q m : ℝ) : ℂ) := by
  unfold SieveFamily.dw gA gB
  split_ifs <;> push_cast <;> simp [div_eq_mul_inv]

theorem sum_dw_famI (q : ℕ) (a : ZMod q) (N₁ N₂ : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ)) :
    ∑ rt ∈ F, ∑ n ∈ Ioc N₁ N₂, SieveFamily.dw q a n *
        (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0) =
      ((famI (gA q a) N₁ N₂ F - famI (gB q) N₁ N₂ F : ℝ) : ℂ) := by
  unfold famI
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun rt _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [dw_eq]
  split_ifs <;> push_cast <;> ring

theorem sum_dw_famJ (q : ℕ) (a : ZMod q) (N₁ N₂ z : ℕ) {k : ℕ} (F : Finset (Fin k → ℕ)) :
    ∑ rt ∈ F, ∑ n ∈ Ioc N₁ N₂, SieveFamily.dw q a n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough z n then 1 else 0) =
      ((famJ (gA q a) N₁ N₂ z F - famJ (gB q) N₁ N₂ z F : ℝ) : ℂ) := by
  unfold famJ
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun rt _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [dw_eq]
  split_ifs <;> push_cast <;> ring

/-! ### The estimates on families of atoms -/

variable [Route]

/-- `N₁ = ⌊q^L⌋`. -/
noncomputable abbrev N1 (q : ℕ) : ℕ := ⌊(q : ℝ) ^ L⌋₊
/-- `N₂ = ⌊2q^L⌋`. -/
noncomputable abbrev N2 (q : ℕ) : ℕ := ⌊2 * (q : ℝ) ^ L⌋₊

/-- The thresholds of a family's atoms lie in `[1, q^{L+1}]`. -/
def ThrOK (q : ℕ) {k : ℕ} (spec : List (Atom k)) : Prop :=
  ∀ A ∈ spec, 1 ≤ A.thr ∧ A.thr ≤ (q : ℝ) ^ (L + 1 : ℝ)

theorem c_le_of_thrOK {q : ℕ} (hq : 1 ≤ q) {k : ℕ} {spec : List (Atom k)} (h : ThrOK q spec) :
    ∀ C ∈ spec.map Atom.toG, C.c 0 ≤ (L + 1) * Real.log q := by
  intro C hC
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hC
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  refine (Atom.toG_c_le A).trans ?_
  have h1 := (h A hA).1
  rw [abs_of_nonneg (Real.log_nonneg h1), ← Real.log_rpow hq0]
  exact Real.log_le_log (by linarith) (h A hA).2

theorem holds_iff_sem {q : ℕ} {k : ℕ} {spec : List (Atom k)} (h : ThrOK q spec) {rt : Fin k → ℕ}
    (hp : ∀ i, (rt i).Prime) : (∀ C ∈ spec.map Atom.toG, C.holds 0 rt) ↔ ∀ A ∈ spec, A.sem rt := by
  simp only [List.forall_mem_map]
  exact forall₂_congr fun A hA => A.toG_holds (by linarith [(h A hA).1]) 0 fun i => (hp i).one_lt.le

theorem RTg_eq_of_thrOK {q : ℕ} {k Y : ℕ} {spec : List (Atom k)} (h : ThrOK q spec) :
    RTg k Y (spec.map Atom.toG) = famSet k Y spec :=
  RTg_eq k Y spec fun A hA => by linarith [(h A hA).1]

variable (a₀ : ℝ)

/-- **The lower window, on a family of atoms** (`SieveChain.chainTL_bound`). Assume `RouteOK` and the route's Type II
estimate (`hII`). For `a₀ > 0` and `k'` there are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: a
family of `(k' + 1)`-tuples of primes cut out by at most `18` atoms with thresholds as in `ThrOK`, each tuple strictly
decreasing, with entries at least `q^{a₀}` and `P₁ < ∏_{i∈S} rt_i ≤ P₂`, where `q^{w₁L} ≤ P₁` and `P₂ ≤ q^{w₂L}`, has
`|A − B/φ(q)| ≤ q^{L−δ}/φ(q)`. -/
theorem TL_spec [RouteOK] (hII : TypeIIAt) (ha₀ : 0 < a₀) (k' : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (spec : List (Atom (k' + 1))) (S : Finset (Fin (k' + 1))) (P₁ P₂ : ℕ), spec.length ≤ 18 → ThrOK q spec →
      (q : ℝ) ^ (w₁ * L) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (w₂ * L) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
        StrictAnti rt ∧ (∀ i, (q : ℝ) ^ a₀ ≤ rt i) ∧ P₁ < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ P₂) →
      |famI (gA q a) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec) -
          famI (gB q) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec)| ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨δ, hδ, q₀, hq₀⟩ := chainTL_bound hII ha₀ k' 18 (Λ₁ := L + 1) (by linarith [L_pos])
  refine ⟨δ, hδ, q₀, fun q _ hq a ha spec S P₁ P₂ hlen hthr hP₁ hP₂ hreg => ?_⟩
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have h := hq₀ q hq a ha S (spec.map Atom.toG) P₁ P₂ (by simpa using hlen) (c_le_of_thrOK hq1 hthr) hP₁ hP₂
    fun rt hp hΩ => hreg rt hp ((holds_iff_sem hthr hp).1 hΩ)
  rwa [RTg_eq_of_thrOK hthr, sum_dw_famI, Complex.norm_real, Real.norm_eq_abs] at h

/-- **The upper window, on a family of atoms** (`SieveChain.chainTU_bound`). Assume `RouteOK` and the route's Type II
estimate (`hII`). For `a₀ > 0` and `k'` there are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: a
family of `(k' + 1)`-tuples of primes cut out by at most `18` atoms with thresholds as in `ThrOK`, each tuple strictly
decreasing, with entries at least `q^{a₀}` and `W₀ < ∏rt ≤ W₁`, where `W₁ ≤ N₁`, `q^{w₁L} ≤ ⌊N₁/W₁⌋` and
`⌊N₂/(W₀ + 1)⌋ ≤ q^{w₂L}`, has `|A − B/φ(q)| ≤ q^{L−δ}/φ(q)`. -/
theorem TU_spec [RouteOK] (hII : TypeIIAt) (ha₀ : 0 < a₀) (k' : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (spec : List (Atom (k' + 1))) (W₀ W₁ : ℕ), spec.length ≤ 18 → ThrOK q spec →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
        StrictAnti rt ∧ (∀ i, (q : ℝ) ^ a₀ ≤ rt i) ∧ W₀ < ∏ i, rt i ∧ ∏ i, rt i ≤ W₁) →
      W₁ ≤ N1 q → (q : ℝ) ^ (w₁ * L) ≤ ((N1 q / W₁ : ℕ) : ℝ) →
      ((N2 q / (W₀ + 1) : ℕ) : ℝ) ≤ (q : ℝ) ^ (w₂ * L) →
      |famI (gA q a) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec) -
          famI (gB q) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec)| ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨δ, hδ, q₀, hq₀⟩ := chainTU_bound hII ha₀ k' 18 (Λ₁ := L + 1) (by linarith [L_pos])
  refine ⟨δ, hδ, q₀, fun q _ hq a ha spec W₀ W₁ hlen hthr hreg hW₁ hP₁ hP₂ => ?_⟩
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have h := hq₀ q hq a ha W₀ W₁ (spec.map Atom.toG) (by simpa using hlen) (c_le_of_thrOK hq1 hthr)
    (fun rt hp hΩ => by
      obtain ⟨hsa, hge, hlo, hhi⟩ := hreg rt hp ((holds_iff_sem hthr hp).1 hΩ)
      exact ⟨hge, fun i => hsa.antitone (Fin.le_last i), hlo, hhi⟩) hW₁ hP₁ hP₂
  rwa [RTg_eq_of_thrOK hthr, sum_dw_famI, Complex.norm_real, Real.norm_eq_abs] at h

/-- An atom whose comparison has a nonzero coefficient. -/
def NZ {k : ℕ} : Atom k → Prop
  | .ge _ _ => True
  | .lt _ _ => True
  | .ltVar s t => s ≠ t
  | .prodLe T _ => T.Nonempty
  | .prodGt T _ => T.Nonempty

omit [Route] in
theorem toG_nz {k : ℕ} (A : Atom k) (h : NZ A) : ∃ i, A.toG.e i ≠ 0 := by
  cases A with
  | ge t b => exact ⟨t, by simp [Atom.toG]⟩
  | lt t b => exact ⟨t, by simp [Atom.toG]⟩
  | ltVar s t => exact ⟨s, by simp [Atom.toG, show s ≠ t from h]⟩
  | prodLe T b =>
    obtain ⟨i, hi⟩ := (show T.Nonempty from h)
    exact ⟨i, by simp [Atom.toG, hi]⟩
  | prodGt T b =>
    obtain ⟨i, hi⟩ := (show T.Nonempty from h)
    exact ⟨i, by simp [Atom.toG, hi]⟩

/-- With thresholds as in `ThrOK` and nonzero coefficients, the pivoted comparisons cut out the same family. -/
theorem RT_pivoted {q : ℕ} {k Y : ℕ} {spec : List (Atom k)} (h : ThrOK q spec) (hnz : ∀ A ∈ spec, NZ A) :
    SieveStops2.RT k Y (pivoted (spec.map Atom.toG)) = famSet k Y spec := by
  rw [← RTg_eq_of_thrOK h]
  unfold SieveStops2.RT RTg
  refine Finset.filter_congr fun x _ => ?_
  rw [holds_iff_pivoted]
  constructor
  · intro h1
    refine ⟨h1, fun C hC h0 => ?_⟩
    obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hC
    obtain ⟨i, hi⟩ := toG_nz A (hnz A hA)
    exact absurd (h0 i) hi
  · exact fun h1 => h1.1

variable (b₀ : ℝ)

/-- **Proposition 6, on a family of atoms.** Assume `RouteOK` and the route's Type II estimate (`hII`). For `a₀ > 0`,
`b₀` with `a₀ + b₀ < (1 − w₁)L` and `(1 − w₂)L < b₀ < L − 1`, `j`, and `η > 0` there are `δ > 0` and `q₀` such that for
`q ≥ q₀` and a unit `a` mod `q`: for a family of `j`-tuples of primes cut out by at most `18` atoms with nonzero
coefficients and thresholds as in `ThrOK`, each tuple with entries at least `z₀ = ⌈q^{a₀}⌉` and product `r` at most
`⌊q^{b₀}⌋`, `Σ_{rt}(S(A_r, z₀) − S(B_r, z₀)/φ(q))` is at most `ηq^L/(φ(q) log q) + q^{L−δ}/φ(q)` in absolute value. -/
theorem P6_spec [RouteOK] (hII : TypeIIAt) (ha₀ : 0 < a₀) (hab : a₀ + b₀ < (1 - w₁) * L)
    (hb₁ : (1 - w₂) * L < b₀) (hb₂ : b₀ < L - 1) (j : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (spec : List (Atom j)), spec.length ≤ 18 → ThrOK q spec → (∀ A ∈ spec, NZ A) →
      (∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
        (∀ i, ⌈(q : ℝ) ^ a₀⌉₊ ≤ rt i) ∧ ∏ i, rt i ≤ ⌊(q : ℝ) ^ b₀⌋₊) →
      |famJ (gA q a) (N1 q) (N2 q) ⌈(q : ℝ) ^ a₀⌉₊ (famSet j (N2 q) spec) -
          famJ (gB q) (N1 q) (N2 q) ⌈(q : ℝ) ^ a₀⌉₊ (famSet j (N2 q) spec)| ≤
        η * (q : ℝ) ^ L / (q.totient * Real.log q) +
          (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveProp6.prop6 hII j 18 (Λ₁ := L + 1) (by linarith [L_pos]) ha₀ hab hb₁ hb₂ hη
  refine ⟨δ, hδ, q₀, fun q _ hq a ha spec hlen hthr hnz hreg => ?_⟩
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have h := hq₀ q hq a ha (pivoted (spec.map Atom.toG)) ((length_pivoted_le _).trans (by simpa using hlen))
    (fun C' hC' => by
      obtain ⟨C, hC, hne, rfl⟩ := mem_pivoted.1 hC'
      exact c_le_of_thrOK hq1 hthr C hC)
    (fun rt hp hΩ => by
      refine hreg rt hp ((holds_iff_sem hthr hp).1 ?_)
      exact ((holds_iff_pivoted _ 0 rt).2 ⟨hΩ, fun C hC h0 => by
        obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hC
        obtain ⟨i, hi⟩ := toG_nz A (hnz A hA)
        exact absurd (h0 i) hi⟩))
  rwa [RT_pivoted hthr hnz, sum_dw_famJ, Complex.norm_real, Real.norm_eq_abs] at h

end SieveLeaves
