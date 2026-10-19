/-
# Round 604: the stops of Buchstab's tree above the threshold (milestone M5)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. `RT j Y Ω` is the set of `j`-tuples of primes up to `Y` that satisfy the comparisons `Ω` at
`m = 0`.

* `typeII_cmp`: `SieveTypeIIU.typeII_unw` with the comparisons given as a list of `SieveCmp.Cmp`s.
* `sum_stops_eq`: the stops `W = r_1⋯r_j·∏P·p` of the tree at the threshold `X'` (`r` over `RT`, `p ∈ [w, z₀)`, `P` an
  `s`-set of primes of `(p, z₀)`), with `p ≤ minFac k` and `N₁ < Wk ≤ N₂`, are the tuples `(r, P in decreasing order,
  p)` of primes up to `Y` that satisfy the comparisons `cmps` at `k`.
* `stops2_bound`: fix `e₀ > 0`, `j`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit
  `a` mod `q`: let `rt` run over the `j`-tuples of primes up to `N₂ = ⌊2q^L⌋` satisfying at most `J₀` comparisons `Ω`
  (taken at `m = 0`, with `m`-parts `c(0)` at most `Λ₁ log q`) that force every `rt_i ≥ z₀`, and let
  `q^{e₀} ≤ w ≤ z₀`, `1 ≤ X'`, `X'z₀ ≤ N₁ = ⌊q^L⌋`, `q^{0.401L} ≤ ⌊N₁/(X'z₀)⌋` and `⌊N₂/(X' + 1)⌋ ≤ q^{0.485L}`. Then
  the stops of Buchstab's tree at the threshold `X'` (`SieveDiff.tree_weighted` with `r = ∏rt`), summed over `rt`,
  have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`, `L = 2.333`.

This is the evaluation of the stops in Proposition 6 (`frontier/linnik/SIEVE-ROUTE.md` §5, §13's M5) for one tree
at the threshold `X'`. A stop `W` lies in `(X', X'z₀)`, so its cofactor `k` lies in `(N₁/(X'z₀), N₂/(X' + 1)]`, inside
the lower window. The roles swap: `k` is the Type II variable and the stop's primes are the family's.

The proof: `sum_cofactor_window` writes a stop's multiples as `Wk` with `k` in that range and `p ≤ minFac k`
(`rough_iff_le_minFac`). For each size `s ≤ ⌈L/e₀⌉` of `P` (a larger `P` has `∏P > X'`), `sum_stops_eq` turns the stops
into a family of `(j + s + 1)`-tuples with the comparisons `cmps`: the region `Ω`, the order `y_1 > ⋯ > y_s > p`,
`y_1 < z₀` (or `p < z₀`), `p ≥ w`, the threshold, the cofactor's roughness and the range (`cmps_iff`). Their
`m`-parts are at most `(Λ₁ + L + 1) log q` (`cmps_c_le`), and `typeII_cmp` bounds each size.

The file imports `SieveCmp.lean` and `SieveStops1.lean`.
-/
import SieveCmp
import SieveStops1

open Real Finset SieveFamily SieveTree SieveCmp

namespace SieveStops2

/-! ### A set of `s` naturals as a strictly decreasing `s`-tuple -/

/-- The elements of `P` in decreasing order, when `P` has `s` elements. -/
noncomputable def desc (s : ℕ) (P : Finset ℕ) : Fin s → ℕ :=
  fun u => if h : P.card = s then P.orderEmbOfFin h (Fin.rev u) else 0

theorem desc_eq {s : ℕ} {P : Finset ℕ} (h : P.card = s) (u : Fin s) :
    desc s P u = P.orderEmbOfFin h (Fin.rev u) := by
  simp [desc, h]

theorem desc_strictAnti {s : ℕ} {P : Finset ℕ} (h : P.card = s) : StrictAnti (desc s P) := by
  intro u v huv
  rw [desc_eq h, desc_eq h]
  exact (P.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.2 huv)

theorem desc_mem {s : ℕ} {P : Finset ℕ} (h : P.card = s) (u : Fin s) : desc s P u ∈ P := by
  rw [desc_eq h]
  exact P.orderEmbOfFin_mem h _

theorem image_desc {s : ℕ} {P : Finset ℕ} (h : P.card = s) : Finset.univ.image (desc s P) = P := by
  conv_rhs => rw [← P.image_orderEmbOfFin_univ h]
  ext p
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨Fin.rev u, (desc_eq h u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨Fin.rev u, by rw [desc_eq h, Fin.rev_rev]⟩

theorem desc_image {s : ℕ} {y : Fin s → ℕ} (hy : StrictAnti y) : desc s (Finset.univ.image y) = y := by
  have hc : (Finset.univ.image y).card = s := by
    rw [Finset.card_image_of_injective _ hy.injective, Finset.card_univ, Fintype.card_fin]
  have hu := Finset.orderEmbOfFin_unique hc (f := y ∘ Fin.rev)
    (fun u => Finset.mem_image_of_mem _ (Finset.mem_univ _)) (hy.comp Fin.rev_strictAnti)
  funext u
  rw [desc_eq hc, ← hu]
  simp [Fin.rev_rev]

theorem prod_desc {s : ℕ} {P : Finset ℕ} (h : P.card = s) : ∏ u, desc s P u = ∏ p ∈ P, p := by
  conv_rhs => rw [← image_desc h]
  rw [Finset.prod_image (fun u _ v _ huv => (desc_strictAnti h).injective huv)]

/-! ### The tuple `(r_1, …, r_j, y_1, …, y_s, p)` -/

/-- The tuple `(r_1, …, r_j, y_1, …, y_s, p)`. -/
def app {j s : ℕ} (rt : Fin j → ℕ) (y : Fin s → ℕ) (p : ℕ) : Fin (j + s + 1) → ℕ :=
  fun i => if h : i.val < j then rt ⟨i, h⟩ else if h' : i.val < j + s then y ⟨i.val - j, by omega⟩ else p

variable {j s : ℕ}

theorem app_lt (rt : Fin j → ℕ) (y : Fin s → ℕ) (p : ℕ) (i : Fin (j + s + 1)) (h : i.val < j) :
    app rt y p i = rt ⟨i, h⟩ := by
  simp [app, h]

theorem app_mid (rt : Fin j → ℕ) (y : Fin s → ℕ) (p : ℕ) (i : Fin (j + s + 1)) (h1 : j ≤ i.val)
    (h2 : i.val < j + s) : app rt y p i = y ⟨i.val - j, by omega⟩ := by
  simp [app, show ¬ i.val < j by omega, h2]

theorem app_last (rt : Fin j → ℕ) (y : Fin s → ℕ) (p : ℕ) : app rt y p (Fin.last _) = p := by
  simp [app]

theorem app_block (rt : Fin j → ℕ) (y : Fin s → ℕ) (p : ℕ) (i : Fin (j + s + 1)) (u : Fin s)
    (h : i.val = j + u) : app rt y p i = y u := by
  rw [app_mid _ _ _ _ (by omega) (by have := u.isLt; omega)]
  congr 1
  ext
  simp only
  omega

theorem app_end (rt : Fin j → ℕ) (y : Fin s → ℕ) (p : ℕ) (i : Fin (j + s + 1)) (h : i.val = j + s) :
    app rt y p i = p := by
  rw [show i = Fin.last _ from Fin.ext (by simp [h]), app_last]

theorem prod_app_init (rt : Fin j → ℕ) (y : Fin s → ℕ) (p : ℕ) :
    ∏ i : Fin (j + s), app rt y p i.castSucc = (∏ i, rt i) * ∏ u, y u := by
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun u _ => ?_
    rw [app_lt _ _ _ _ (by simp)]
    rfl
  · refine Finset.prod_congr rfl fun u _ => ?_
    rw [app_mid _ _ _ _ (by simp) (by simp)]
    congr 1
    ext
    simp

theorem prod_app (rt : Fin j → ℕ) (y : Fin s → ℕ) (p : ℕ) :
    ∏ i, app rt y p i = (∏ i, rt i) * (∏ u, y u) * p := by
  rw [Fin.prod_univ_castSucc, prod_app_init, app_last]

/-- `x` is the tuple of its parts. -/
theorem app_parts (x : Fin (j + s + 1) → ℕ) :
    app (fun u : Fin j => x ⟨u, by omega⟩) (fun u : Fin s => x ⟨j + u, by omega⟩) (x (Fin.last _)) = x := by
  funext i
  unfold app
  have hi := i.isLt
  split_ifs with h1 h2
  · rfl
  · exact congrArg x (Fin.ext (by simp only; omega))
  · exact congrArg x (Fin.ext (by simp only [Fin.val_last]; omega))

/-- The product over the coordinates before the last. -/
theorem prod_filter_init {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i.val < n), f i = ∏ i : Fin n, f i.castSucc := by
  have h : Finset.univ.filter (fun i : Fin (n + 1) => i.val < n) = Finset.univ.image Fin.castSucc := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨⟨i, hi⟩, Fin.ext rfl⟩
    · rintro ⟨u, rfl⟩
      exact u.isLt
  rw [h, Finset.prod_image (fun u _ v _ huv => Fin.castSucc_injective n huv)]

/-! ### The comparisons of a stop above the threshold -/

/-- A comparison on the first `j` coordinates whose form does not depend on `m`, taken at `m = 0`. -/
noncomputable def liftc {K : ℕ} (C : Cmp j) (h : j ≤ K) : Cmp K :=
  { lift C h with c := fun _ => C.c 0 }

theorem liftc_holds {K : ℕ} (C : Cmp j) (h : j ≤ K) (m : ℕ) (x : Fin K → ℕ) :
    (liftc C h).holds m x ↔ C.holds 0 (fun i => x (Fin.castLE h i)) :=
  lift_holds C h 0 x

/-- The comparisons of the stops of size `s`: the region `Ω` of `(r_1, …, r_j)`, the decreasing order of
`y_1 > ⋯ > y_s > p`, `y_1 < z₀` (or `p < z₀`), `p ≥ w`, the tree's threshold `y_1⋯y_s r_1⋯r_j ≤ X' < ⋯ p`, the
cofactor's roughness `p ≤ minFac k`, and the range `N₁ < k∏ ≤ N₂`. -/
noncomputable def cmps (j s : ℕ) (Ω : List (Cmp j)) (z₀ w X' N₁ N₂ : ℝ) : List (Cmp (j + s + 1)) :=
  Ω.map (fun C => liftc C (by omega)) ++
    (List.finRange s).map (fun (u : Fin s) => gt (⟨j + u, by have := u.isLt; omega⟩ : Fin (j + s + 1))
      ⟨j + u + 1, by have := u.isLt; omega⟩
      (by simp [Fin.ext_iff])) ++
    [lt ⟨j, by omega⟩ z₀, ge (Fin.last _) w] ++
    (if h : 0 < j + s then
      [prodLe (Finset.univ.filter (fun i : Fin (j + s + 1) => i.val < j + s)) (i₀ := 0)
        (by simp [h]) X']
      else []) ++
    [prodGt Finset.univ (i₀ := Fin.last _) (Finset.mem_univ _) X', rough (Fin.last _), rangeLo N₁, rangeHi N₂]

/-- **What the comparisons say**, for `x_i ≥ 1`, `k ≥ 1` and positive thresholds with `X' ≥ 1`. -/
theorem cmps_iff (Ω : List (Cmp j)) {z₀ w X' N₁ N₂ : ℝ} (hz₀ : 0 < z₀) (hw : 0 < w) (hX' : 1 ≤ X')
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) {k : ℕ} (hk : 1 ≤ k) {x : Fin (j + s + 1) → ℕ} (hx : ∀ i, 1 ≤ x i) :
    (∀ C ∈ cmps j s Ω z₀ w X' N₁ N₂, C.holds k x) ↔
      (∀ C ∈ Ω, C.holds 0 (fun u : Fin j => x ⟨u, by omega⟩)) ∧
      (∀ u : Fin s, x ⟨j + u + 1, by have := u.isLt; omega⟩ < x ⟨j + u, by have := u.isLt; omega⟩) ∧
      (x ⟨j, by omega⟩ : ℝ) < z₀ ∧ w ≤ (x (Fin.last _) : ℝ) ∧
      ∏ i : Fin (j + s), (x i.castSucc : ℝ) ≤ X' ∧ X' < ∏ i, (x i : ℝ) ∧
      x (Fin.last _) ≤ Nat.minFac k ∧ N₁ < (k : ℝ) * ∏ i, (x i : ℝ) ∧ (k : ℝ) * ∏ i, (x i : ℝ) ≤ N₂ := by
  have hX'0 : (0 : ℝ) < X' := by linarith
  have hprod : ∏ i : Fin (j + s), (x i.castSucc : ℝ) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin (j + s + 1) => i.val < j + s), (x i : ℝ) :=
    (prod_filter_init (n := j + s) (fun i => (x i : ℝ))).symm
  unfold cmps
  split_ifs with h
  · simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_finRange, true_implies,
      List.mem_nil_iff, false_implies, implies_true, and_true, liftc_holds, gt_holds _ k hx, lt_holds _ hz₀ k hx,
      ge_holds _ hw k hx, prodLe_holds _ _ hX'0 k hx, prodGt_holds _ _ hX'0 k hx, rough_holds _ k hx,
      rangeLo_holds hN₁ hk hx, rangeHi_holds hN₂ hk hx]
    rw [hprod]
    tauto
  · have he : Finset.univ.filter (fun i : Fin (j + s + 1) => i.val < j + s) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    have h1 : ∏ i : Fin (j + s), (x i.castSucc : ℝ) ≤ X' := by
      rw [hprod, he, Finset.prod_empty]
      exact hX'
    simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_finRange, true_implies,
      List.mem_nil_iff, false_implies, implies_true, and_true, liftc_holds, gt_holds _ k hx, lt_holds _ hz₀ k hx,
      ge_holds _ hw k hx, prodGt_holds _ _ hX'0 k hx, rough_holds _ k hx,
      rangeLo_holds hN₁ hk hx, rangeHi_holds hN₂ hk hx]
    tauto

/-- The consecutive inequalities make the block `x_j > ⋯ > x_{j+s}` strictly decreasing. -/
theorem block_strictAnti {x : Fin (j + s + 1) → ℕ}
    (hb : ∀ u : Fin s, x ⟨j + u + 1, by have := u.isLt; omega⟩ < x ⟨j + u, by have := u.isLt; omega⟩) :
    StrictAnti (fun u : Fin (s + 1) => x ⟨j + u, by have := u.isLt; omega⟩) := by
  refine Fin.strictAnti_iff_succ_lt.2 fun u => ?_
  have e1 : x ⟨j + (u.succ : ℕ), by have := u.isLt; simp only [Fin.val_succ]; omega⟩ =
      x ⟨j + u + 1, by have := u.isLt; omega⟩ := congrArg x (Fin.ext (by simp only [Fin.val_succ]; omega))
  have e2 : x ⟨j + (u.castSucc : ℕ), by have := u.isLt; simp only [Fin.val_castSucc]; omega⟩ =
      x ⟨j + u, by have := u.isLt; omega⟩ := congrArg x (Fin.ext (by simp only [Fin.val_castSucc]))
  show x ⟨j + (u.succ : ℕ), _⟩ < x ⟨j + (u.castSucc : ℕ), _⟩
  rw [e1, e2]
  exact hb u

section Sums

open Classical

/-- The `j`-tuples of primes up to `Y` that satisfy the comparisons `Ω` at `m = 0`. -/
noncomputable def RT (j Y : ℕ) (Ω : List (Cmp j)) : Finset (Fin j → ℕ) :=
  (Fintype.piFinset (fun _ : Fin j => SieveTypeIIU.primesLe Y)).filter (fun rt => ∀ C ∈ Ω, C.holds 0 rt)

/-- **The stops of size `s`, as tuples of primes.** The stops `W = r_1⋯r_j·∏P·p` of the tree at the threshold `X'`
(`r` over `RT`, `p ∈ [w, z₀)`, `P` an `s`-set of primes of `(p, z₀)`) with `p ≤ minFac k` and `N₁ < Wk ≤ N₂` are the
tuples `(r, P in decreasing order, p)` of primes up to `Y` that satisfy the comparisons `cmps`. -/
theorem sum_stops_eq {M : Type*} [AddCommMonoid M] (Ω : List (Cmp j)) {Y w z₀ X' N₁ N₂ k : ℕ}
    (hw : 1 ≤ w) (hwz : w ≤ z₀) (hz₀Y : z₀ ≤ Y) (hX' : 1 ≤ X') (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (hk : 1 ≤ k)
    (F : ℕ → M) :
    ∑ rt ∈ RT j Y Ω, ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powersetCard s,
        (if (∏ i, rt i) * ∏ p' ∈ P, p' ≤ X' ∧ X' < (∏ i, rt i) * (∏ p' ∈ P, p') * p ∧ p ≤ Nat.minFac k ∧
            N₁ < (∏ i, rt i) * (∏ p' ∈ P, p') * p * k ∧ (∏ i, rt i) * (∏ p' ∈ P, p') * p * k ≤ N₂
          then F ((∏ i, rt i) * (∏ p' ∈ P, p') * p) else 0) =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin (j + s + 1) => SieveTypeIIU.primesLe Y),
        (if ∀ C ∈ cmps j s Ω z₀ w X' N₁ N₂, C.holds k x then F (∏ i, x i) else 0) := by
  set W : (Fin j → ℕ) × ℕ × Finset ℕ → ℕ := fun t => (∏ i, t.1 i) * (∏ p' ∈ t.2.2, p') * t.2.1 with hW
  set cond : (Fin j → ℕ) × ℕ × Finset ℕ → Prop := fun t =>
    (∏ i, t.1 i) * ∏ p' ∈ t.2.2, p' ≤ X' ∧ X' < W t ∧ t.2.1 ≤ Nat.minFac k ∧ N₁ < W t * k ∧ W t * k ≤ N₂
    with hcond
  set D := (RT j Y Ω ×ˢ (primesIco w z₀ ×ˢ (primesIco w z₀).powersetCard s)).filter
    (fun t => t.2.2 ⊆ primesIco (t.2.1 + 1) z₀ ∧ cond t) with hD
  set Cd := (Fintype.piFinset (fun _ : Fin (j + s + 1) => SieveTypeIIU.primesLe Y)).filter
    (fun x => ∀ C ∈ cmps j s Ω z₀ w X' N₁ N₂, C.holds k x) with hCd
  -- the left side as a sum over `D`
  have hL : ∑ rt ∈ RT j Y Ω, ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powersetCard s,
        (if (∏ i, rt i) * ∏ p' ∈ P, p' ≤ X' ∧ X' < (∏ i, rt i) * (∏ p' ∈ P, p') * p ∧ p ≤ Nat.minFac k ∧
            N₁ < (∏ i, rt i) * (∏ p' ∈ P, p') * p * k ∧ (∏ i, rt i) * (∏ p' ∈ P, p') * p * k ≤ N₂
          then F ((∏ i, rt i) * (∏ p' ∈ P, p') * p) else 0) = ∑ t ∈ D, F (W t) := by
    rw [hD, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun rt _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpw := (mem_primesIco.1 hp).1
    have hsub : ((primesIco w z₀).powersetCard s).filter (fun P => P ⊆ primesIco (p + 1) z₀) =
        (primesIco (p + 1) z₀).powersetCard s := by
      ext P
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨-, hc⟩, h⟩
        exact ⟨h, hc⟩
      · rintro ⟨h, hc⟩
        refine ⟨⟨fun ℓ hℓ => ?_, hc⟩, h⟩
        obtain ⟨h1, h2, h3⟩ := mem_primesIco.1 (h hℓ)
        exact mem_primesIco.2 ⟨by omega, h2, h3⟩
    rw [← hsub, Finset.sum_filter]
    refine Finset.sum_congr rfl fun P _ => ?_
    by_cases h : P ⊆ primesIco (p + 1) z₀
    · simp only [h, true_and, ite_true, hcond, hW]
    · simp only [h, false_and, ite_false]
  have hR : ∑ x ∈ Fintype.piFinset (fun _ : Fin (j + s + 1) => SieveTypeIIU.primesLe Y),
        (if ∀ C ∈ cmps j s Ω z₀ w X' N₁ N₂, C.holds k x then F (∏ i, x i) else 0) = ∑ x ∈ Cd, F (∏ i, x i) := by
    rw [hCd, Finset.sum_filter]
  rw [hL, hR]
  have hz₀ : (0 : ℝ) < z₀ := by exact_mod_cast (show 0 < z₀ by omega)
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hX'1 : (1 : ℝ) ≤ X' := by exact_mod_cast hX'
  have hN₁0 : (0 : ℝ) < N₁ := by exact_mod_cast (show 0 < N₁ by omega)
  have hN₂0 : (0 : ℝ) < N₂ := by exact_mod_cast (show 0 < N₂ by omega)
  have hiff := fun (x : Fin (j + s + 1) → ℕ) (hx : ∀ i, 1 ≤ x i) =>
    cmps_iff (s := s) Ω hz₀ hw0 hX'1 hN₁0 hN₂0 hk hx
  refine Finset.sum_nbij' (fun t => app t.1 (desc s t.2.2) t.2.1)
    (fun x => ((fun u : Fin j => x ⟨u, by omega⟩), x (Fin.last _),
      Finset.univ.image (fun u : Fin s => x ⟨j + u, by have := u.isLt; omega⟩))) ?_ ?_ ?_ ?_ ?_
  · -- into the tuples
    rintro ⟨rt, p, P⟩ ht
    simp only [hD, Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard, RT,
      Finset.mem_filter, Fintype.mem_piFinset] at ht
    obtain ⟨⟨⟨hrtY, hrtΩ⟩, hp, -, hcard⟩, hPp, hX1, hX2, hmin, hN1, hN2⟩ := ht
    obtain ⟨hpw, hpz, hpp⟩ := mem_primesIco.1 hp
    have hPm : ∀ u, desc s P u ∈ primesIco (p + 1) z₀ := fun u => hPp (desc_mem hcard u)
    have hbox : ∀ i, app rt (desc s P) p i ∈ SieveTypeIIU.primesLe Y := by
      intro i
      rw [SieveTypeIIU.mem_primesLe]
      unfold app
      split_ifs with h1 h2
      · exact (SieveTypeIIU.mem_primesLe.1 (hrtY _))
      · obtain ⟨-, h3, h4⟩ := mem_primesIco.1 (hPm ⟨i.val - j, by omega⟩)
        exact ⟨by omega, h4⟩
      · exact ⟨by omega, hpp⟩
    simp only [hCd, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨hbox, ?_⟩
    have hx1 : ∀ i, 1 ≤ app rt (desc s P) p i := fun i =>
      (Nat.Prime.one_lt (SieveTypeIIU.mem_primesLe.1 (hbox i)).2).le
    refine (hiff _ hx1).2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : (fun u : Fin j => app rt (desc s P) p ⟨u, by omega⟩) = rt := funext fun u => by
        rw [app_lt _ _ _ _ u.isLt]
      rw [this]
      exact hrtΩ
    · intro u
      have e1 : app rt (desc s P) p ⟨j + u, by have := u.isLt; omega⟩ = desc s P u := app_block _ _ _ _ u rfl
      rw [e1]
      by_cases hu : (u : ℕ) + 1 < s
      · have e2 : app rt (desc s P) p ⟨j + u + 1, by have := u.isLt; omega⟩ = desc s P ⟨u + 1, hu⟩ :=
          app_block _ _ _ _ _ (by simp only; omega)
        rw [e2]
        exact desc_strictAnti hcard (Fin.lt_def.2 (by simp only; omega))
      · have e2 : app rt (desc s P) p ⟨j + u + 1, by have := u.isLt; omega⟩ = p :=
          app_end _ _ _ _ (by simp only; omega)
        rw [e2]
        exact (mem_primesIco.1 (hPm u)).1
    · by_cases hs : 0 < s
      · have e1 : app rt (desc s P) p ⟨j, by omega⟩ = desc s P ⟨0, hs⟩ := app_block _ _ _ _ _ (by simp only; omega)
        rw [e1]
        exact_mod_cast (mem_primesIco.1 (hPm _)).2.1
      · have e1 : app rt (desc s P) p ⟨j, by omega⟩ = p := app_end _ _ _ _ (by simp only; omega)
        rw [e1]
        exact_mod_cast hpz
    · rw [app_last]
      exact_mod_cast hpw
    · rw [show ∏ i : Fin (j + s), (app rt (desc s P) p i.castSucc : ℝ) =
          ((∏ i : Fin (j + s), app rt (desc s P) p i.castSucc : ℕ) : ℝ) by push_cast; rfl,
        prod_app_init, prod_desc hcard]
      exact_mod_cast hX1
    · rw [show ∏ i, (app rt (desc s P) p i : ℝ) = ((∏ i, app rt (desc s P) p i : ℕ) : ℝ) by push_cast; rfl,
        prod_app, prod_desc hcard]
      exact_mod_cast hX2
    · rw [app_last]
      exact hmin
    · rw [show (k : ℝ) * ∏ i, (app rt (desc s P) p i : ℝ) = ((∏ i, app rt (desc s P) p i) * k : ℕ) by
          push_cast; ring, prod_app, prod_desc hcard]
      exact_mod_cast hN1
    · rw [show (k : ℝ) * ∏ i, (app rt (desc s P) p i : ℝ) = ((∏ i, app rt (desc s P) p i) * k : ℕ) by
          push_cast; ring, prod_app, prod_desc hcard]
      exact_mod_cast hN2
  · -- back to the stops
    intro x hx
    simp only [hCd, Finset.mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨hbox, hall⟩ := hx
    have hpr : ∀ i, (x i).Prime := fun i => (SieveTypeIIU.mem_primesLe.1 (hbox i)).2
    have hx1 : ∀ i, 1 ≤ x i := fun i => (hpr i).one_lt.le
    obtain ⟨hΩ, hb, hz, hwl, hX1, hX2, hmin, hN1, hN2⟩ := (hiff x hx1).1 hall
    have hanti := block_strictAnti hb
    set y : Fin s → ℕ := fun u => x ⟨j + u, by have := u.isLt; omega⟩ with hy
    have hyanti : StrictAnti y := fun u v huv =>
      hanti (show Fin.castSucc u < Fin.castSucc v from Fin.castSucc_lt_castSucc_iff.2 huv)
    have hlast : x (Fin.last _) = x ⟨j + s, by omega⟩ := congrArg x (Fin.ext (by simp))
    have hyp : ∀ u, x (Fin.last _) < y u := fun u => by
      rw [hlast]
      exact hanti (show Fin.castSucc u < Fin.last s from Fin.castSucc_lt_last u)
    have hyz : ∀ u, y u < z₀ := fun u => by
      have h0 : y u ≤ x ⟨j, by omega⟩ := by
        have := hanti.antitone (show (0 : Fin (s + 1)) ≤ Fin.castSucc u from Fin.zero_le _)
        simpa using this
      have : x ⟨j, by omega⟩ < z₀ := by exact_mod_cast hz
      omega
    have hpz : x (Fin.last _) < z₀ := by
      have := hyp
      by_cases hs : 0 < s
      · exact lt_trans (hyp ⟨0, hs⟩) (hyz ⟨0, hs⟩)
      · have : x (Fin.last _) = x ⟨j, by omega⟩ := congrArg x (Fin.ext (by simp; omega))
        rw [this]
        exact_mod_cast hz
    have hwp : w ≤ x (Fin.last _) := by exact_mod_cast hwl
    have hcard : (Finset.univ.image y).card = s := by
      rw [Finset.card_image_of_injective _ hyanti.injective, Finset.card_univ, Fintype.card_fin]
    have hparts := app_parts x
    have hdesc : desc s (Finset.univ.image y) = y := desc_image hyanti
    have hprod_init : (∏ i, (fun u : Fin j => x ⟨u, by omega⟩) i) * ∏ p' ∈ Finset.univ.image y, p' =
        ∏ i : Fin (j + s), x i.castSucc := by
      rw [← prod_desc hcard, hdesc]
      conv_rhs => rw [← hparts]
      rw [prod_app_init]
    have hWx : (∏ i, (fun u : Fin j => x ⟨u, by omega⟩) i) * (∏ p' ∈ Finset.univ.image y, p') *
        x (Fin.last _) = ∏ i, x i := by
      rw [hprod_init, Fin.prod_univ_castSucc]
    simp only [hD, Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard, RT,
      Finset.mem_filter, Fintype.mem_piFinset, hcond, hW]
    refine ⟨⟨⟨fun u => hbox _, hΩ⟩, mem_primesIco.2 ⟨hwp, hpz, hpr _⟩, ?_, hcard⟩, ?_, ?_, ?_, hmin, ?_, ?_⟩
    · intro ℓ hℓ
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hℓ
      exact mem_primesIco.2 ⟨le_trans hwp (hyp u).le, hyz u, hpr _⟩
    · intro ℓ hℓ
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hℓ
      exact mem_primesIco.2 ⟨hyp u, hyz u, hpr _⟩
    · rw [hprod_init]
      exact_mod_cast hX1
    · rw [hWx]
      exact_mod_cast hX2
    · rw [hWx]
      have : (N₁ : ℝ) < ((∏ i, x i) * k : ℕ) := by push_cast; linarith
      exact_mod_cast this
    · rw [hWx]
      have : (((∏ i, x i) * k : ℕ) : ℝ) ≤ N₂ := by push_cast; linarith
      exact_mod_cast this
  · -- left inverse
    rintro ⟨rt, p, P⟩ ht
    simp only [hD, Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard] at ht
    have hcard := ht.1.2.2.2
    refine Prod.ext (funext fun u => app_lt _ _ _ _ u.isLt) (Prod.ext (app_last _ _ _) ?_)
    show Finset.univ.image (fun u : Fin s => app rt (desc s P) p ⟨j + u, _⟩) = P
    have : (fun u : Fin s => app rt (desc s P) p ⟨j + u, by have := u.isLt; omega⟩) = desc s P := by
      funext u
      rw [app_mid _ _ _ _ (by simp) (by simp)]
      congr 1
      ext
      simp
    rw [this, image_desc hcard]
  · -- right inverse
    intro x hx
    simp only [hCd, Finset.mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨hbox, hall⟩ := hx
    have hx1 : ∀ i, 1 ≤ x i := fun i => (SieveTypeIIU.mem_primesLe.1 (hbox i)).2.one_lt.le
    obtain ⟨-, hb, -⟩ := (hiff x hx1).1 hall
    have hanti := block_strictAnti hb
    have hyanti : StrictAnti (fun u : Fin s => x ⟨j + u, by have := u.isLt; omega⟩) := fun u v huv =>
      hanti (show Fin.castSucc u < Fin.castSucc v from Fin.castSucc_lt_castSucc_iff.2 huv)
    show app (fun u : Fin j => x ⟨u, by omega⟩) (desc s (Finset.univ.image _)) (x (Fin.last _)) = x
    rw [desc_image hyanti]
    exact app_parts x
  · -- the products
    rintro ⟨rt, p, P⟩ ht
    simp only [hD, Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard] at ht
    show F (W (rt, p, P)) = F (∏ i, app rt (desc s P) p i)
    rw [prod_app, prod_desc ht.1.2.2.2]

end Sums

/-! ### The bound -/

theorem rough_iff_le_minFac {p k : ℕ} (hk : 2 ≤ k) : (∀ p' < p, p'.Prime → ¬ p' ∣ k) ↔ p ≤ Nat.minFac k := by
  constructor
  · intro h
    by_contra hlt
    exact h _ (not_le.1 hlt) (Nat.minFac_prime (by omega)) (Nat.minFac_dvd k)
  · intro h p' hp' hpp hd
    have := Nat.minFac_le_of_dvd hpp.two_le hd
    omega

/-- A stop `W ∈ (X', X'z₀]` below `N₁`: its multiples in `(N₁, N₂]` are `Wk` with `k ∈ (N₁/(X'z₀), N₂/(X' + 1)]`. -/
theorem sum_cofactor_window (f : ℕ → ℂ) {W p X' z₀ N₁ N₂ : ℕ} (hW0 : 0 < W) (hWN : W ≤ N₁) (hWp : rough p W)
    (hXW : X' < W) (hWX : W ≤ X' * z₀) (hP₁ : 1 ≤ N₁ / (X' * z₀)) :
    ∑ n ∈ Finset.Ioc N₁ N₂, f n * (if W ∣ n ∧ rough p n then 1 else 0) =
      ∑ k ∈ Finset.Ioc (N₁ / (X' * z₀)) (N₂ / (X' + 1)),
        (if p ≤ Nat.minFac k ∧ N₁ < W * k ∧ W * k ≤ N₂ then f (W * k) else 0) := by
  rw [SieveStops1.sum_cofactor f hW0 hWN hWp, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  have hXz0 : 0 < X' * z₀ := lt_of_lt_of_le hW0 hWX
  constructor
  · rintro ⟨⟨hk2, -⟩, hr, h1, h2⟩
    refine ⟨⟨?_, ?_⟩, (rough_iff_le_minFac hk2).1 hr, h1, h2⟩
    · rw [Nat.div_lt_iff_lt_mul hXz0]
      calc N₁ < W * k := h1
        _ ≤ X' * z₀ * k := Nat.mul_le_mul_right k hWX
        _ = k * (X' * z₀) := Nat.mul_comm _ _
    · rw [Nat.le_div_iff_mul_le (by omega)]
      calc k * (X' + 1) ≤ k * W := Nat.mul_le_mul_left k hXW
        _ = W * k := Nat.mul_comm _ _
        _ ≤ N₂ := h2
  · rintro ⟨⟨hk1, -⟩, hmin, h1, h2⟩
    have hk2 : 2 ≤ k := by omega
    exact ⟨⟨hk2, le_trans (Nat.le_mul_of_pos_left k hW0) h2⟩, (rough_iff_le_minFac hk2).2 hmin, h1, h2⟩

theorem cmps_length (Ω : List (Cmp j)) (z₀ w X' N₁ N₂ : ℝ) :
    (cmps j s Ω z₀ w X' N₁ N₂).length ≤ Ω.length + s + 7 := by
  unfold cmps
  simp only [List.length_append, List.length_map, List.length_finRange, List.length_cons, List.length_nil]
  split_ifs <;> simp only [List.length_cons, List.length_nil] <;> omega

/-- The forms' `m`-parts are at most `B` at `m`, given bounds on the thresholds. -/
theorem cmps_c_le (Ω : List (Cmp j)) {z₀ w X' N₁ N₂ B : ℝ} {m : ℕ} (hB : 0 ≤ B) (hΩ : ∀ C ∈ Ω, C.c 0 ≤ B)
    (hz₀B : Real.log z₀ ≤ B) (hw : 1 ≤ w) (hX' : 1 ≤ X') (hX'B : Real.log X' ≤ B) (hm : 1 ≤ m)
    (hmB : Real.log m ≤ B) (hN₁ : 1 ≤ N₁) (hN₂B : Real.log N₂ ≤ B) :
    ∀ C ∈ cmps j s Ω z₀ w X' N₁ N₂, C.c m ≤ B := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm'
  have hlogw : 0 ≤ Real.log w := Real.log_nonneg hw
  have hlogX : 0 ≤ Real.log X' := Real.log_nonneg hX'
  have hlogN : 0 ≤ Real.log N₁ := Real.log_nonneg hN₁
  have hmf : Real.log (Nat.minFac m) ≤ Real.log m := by
    have h1 : (0 : ℝ) < Nat.minFac m := by exact_mod_cast Nat.minFac_pos m
    exact Real.log_le_log h1 (by exact_mod_cast Nat.minFac_le (by omega))
  unfold cmps
  simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, and_true]
  refine ⟨⟨⟨⟨fun C hC => hΩ C hC, fun u _ => ?_⟩, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [gt, hB]
  · simpa [lt] using hz₀B
  · simp only [ge]
    linarith
  · split_ifs
    · simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
      simpa [prodLe] using hX'B
    · simp
  · simp only [prodGt]
    linarith
  · simp only [SieveCmp.rough]
    linarith
  · simp only [rangeLo]
    linarith
  · simp only [rangeHi]
    linarith

theorem sum_range_eq_of_zero {M : Type*} [AddCommMonoid M] {g : ℕ → M} {a b : ℕ} (ha : ∀ s, a ≤ s → g s = 0)
    (hb : ∀ s, b ≤ s → g s = 0) : ∑ s ∈ Finset.range a, g s = ∑ s ∈ Finset.range b, g s := by
  have h1 : ∑ s ∈ Finset.range a, g s = ∑ s ∈ Finset.range (max a b), g s :=
    Finset.sum_subset (Finset.range_subset_range.2 (le_max_left a b)) fun s _ hs =>
      ha s (by simpa using hs)
  have h2 : ∑ s ∈ Finset.range b, g s = ∑ s ∈ Finset.range (max a b), g s :=
    Finset.sum_subset (Finset.range_subset_range.2 (le_max_right a b)) fun s _ hs =>
      hb s (by simpa using hs)
  rw [h1, h2]

section Bound

open Classical

/-- **Type II with a list of comparisons.** `SieveTypeIIU.typeII_unw` with the comparisons given as a list of
`Cmp`s, whose coefficients are at most `1` in absolute value. -/
theorem typeII_cmp (K₀ J₀ : ℕ) {e₁ Λ₁ : ℝ} (he₁ : 0 < e₁) (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (P₁ P₂ : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P₁ P₂ →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ∀ (acoef : ℕ → ℂ), (∀ m, ‖acoef m‖ ≤ 1) → ∀ (n : ℕ), n + 1 ≤ K₀ →
      ∀ (l : List (Cmp (n + 1))), l.length ≤ J₀ → (∀ C ∈ l, ∀ m ∈ S, C.c m ≤ Λ₁ * Real.log q) →
      (∀ m ∈ S, ∀ x : Fin (n + 1) → ℕ, (∀ i, (x i).Prime) → (∀ C ∈ l, C.holds m x) →
        (∀ i, 2 * (q : ℝ) ^ e₁ ≤ x i) ∧ (m : ℝ) * ∏ i, (x i : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ)) →
      ‖∑ m ∈ S, ∑ x ∈ Fintype.piFinset (fun _ : Fin (n + 1) =>
          SieveTypeIIU.primesLe ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊),
          (if ∀ C ∈ l, C.holds m x then acoef m * dw q a (m * ∏ i, x i) else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
  obtain ⟨δ, hδ, q₀, hq₀⟩ := SieveTypeIIU.typeII_unw K₀ J₀ he₁ zero_le_one hΛ₁
  refine ⟨δ, hδ, q₀, ?_⟩
  intro q _ hq a ha P₁ P₂ S hS hP₁ hP₂ acoef hacoef n hn l hl hc hsupp
  have hget : ∀ (m : ℕ) (x : Fin (n + 1) → ℕ), (∀ C ∈ l, C.holds m x) ↔ ∀ t, (l.get t).holds m x := by
    intro m x
    constructor
    · intro h t
      exact h _ (List.get_mem l t)
    · intro h C hC
      obtain ⟨t, rfl⟩ := List.mem_iff_get.1 hC
      exact h t
  have h := hq₀ q hq a ha P₁ P₂ S hS hP₁ hP₂ acoef hacoef n hn (J := l.length) hl (fun t => (l.get t).c)
    (fun t => (l.get t).e) (fun t => (l.get t).holds) (fun t i => (l.get t).he i)
    (fun t m x => (l.get t).spec m x) (fun t m hm => hc _ (List.get_mem l t) m hm)
    (fun t => (l.get t).piv) (fun t => (l.get t).hpiv)
    (fun m hm x hx hall => hsupp m hm x hx ((hget m x).2 hall))
  convert h using 2
  unfold Dsum
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => ?_
  have hcast : ∀ t : Fin l.length, (((if (l.get t).holds m x then 1 else 0 : ℝ)) : ℂ) =
      if (l.get t).holds m x then 1 else 0 := fun t => by split_ifs <;> simp
  simp only [hcast]
  rw [Finset.prod_boole]
  by_cases hall : ∀ C ∈ l, C.holds m x
  · rw [ite_eq_left hall, ite_eq_left (fun t _ => (hget m x).1 hall t), mul_one]
  · rw [ite_eq_right hall, ite_eq_right (fun h' => hall ((hget m x).2 fun t => h' t (Finset.mem_univ _))),
      mul_zero, zero_mul]

/-- **The stops above the threshold.** Fix `e₀ > 0`, `j`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for
`q ≥ q₀` and a unit `a` mod `q`: let `rt` run over the `j`-tuples of primes up to `N₂ = ⌊2q^L⌋` satisfying at most `J₀`
comparisons `Ω` (taken at `m = 0`, with `m`-parts `c(0)` at most `Λ₁ log q`) that force every `rt_i ≥ z₀`, and let
`q^{e₀} ≤ w ≤ z₀`, `1 ≤ X'`, `X'z₀ ≤ N₁ = ⌊q^L⌋`, `q^{0.401L} ≤ ⌊N₁/(X'z₀)⌋` and `⌊N₂/(X' + 1)⌋ ≤ q^{0.485L}`.
Then the stops of Buchstab's tree at the threshold `X'` (`SieveDiff.tree_weighted` with `r = ∏rt`), summed over
`rt`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`, `L = 2.333`. -/
theorem stops2_bound {e₀ : ℝ} (he₀ : 0 < e₀) (j J₀ : ℕ) {Λ₁ : ℝ} (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (X' w z₀ : ℕ) (Ω : List (Cmp j)), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) → ∀ i, z₀ ≤ rt i) →
      (q : ℝ) ^ e₀ ≤ w → w ≤ z₀ → 1 ≤ X' → X' * z₀ ≤ ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ ((⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ / (X' * z₀) : ℕ) : ℝ) →
      ((⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ / (X' + 1) : ℕ) : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ‖∑ rt ∈ RT j ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ Ω, ∑ p ∈ primesIco w z₀,
          ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℂ) ^ (P.card + 1) *
          (if (∏ i, rt i) * ∏ p' ∈ P, p' ≤ X' ∧ X' < (∏ i, rt i) * (∏ p' ∈ P, p') * p then
            ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊, dw q a n *
              (if (∏ i, rt i) * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
  set S₀ : ℕ := ⌈(2333 / 1000 : ℝ) / e₀⌉₊ with hS₀
  obtain ⟨δ, hδ, q₁, hq₁⟩ := typeII_cmp (j + S₀ + 2) (J₀ + S₀ + 7) (half_pos he₀)
    (show (0 : ℝ) ≤ Λ₁ + 2333 / 1000 + 1 by positivity)
  have hev1 := (tendsto_rpow_atTop (half_pos he₀)).eventually_ge_atTop (2 : ℝ)
  have hev2 := (tendsto_rpow_atTop (half_pos hδ)).eventually_ge_atTop ((S₀ : ℝ) + 1)
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually (hev1.and hev2))
  refine ⟨δ / 2, half_pos hδ, max (max q₁ q₂) 3, ?_⟩
  intro q _ hq a ha X' w z₀ Ω hΩlen hΩc hΩz hw hwz hX' hXz hP₁ hP₂
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : q₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  obtain ⟨hqe, hqS⟩ := hq₂ q hq2
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  set N₁ := ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ with hN₁
  set N₂ := ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ with hN₂
  set S := Finset.Ioc (N₁ / (X' * z₀)) (N₂ / (X' + 1)) with hSdef
  have hX1 : (1 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hN₁1 : 1 ≤ N₁ := Nat.le_floor (by exact_mod_cast hX1)
  have hN₁N₂ : N₁ ≤ N₂ := Nat.floor_le_floor (by linarith)
  have hN₁le : (N₁ : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Nat.floor_le (by positivity)
  have hN₂le : (N₂ : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) := Nat.floor_le (by positivity)
  have hP₁1 : 1 ≤ N₁ / (X' * z₀) := by
    have : (1 : ℝ) ≤ (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    exact_mod_cast this.trans hP₁
  have hqe2 : (2 : ℝ) * (q : ℝ) ^ (e₀ / 2) ≤ (q : ℝ) ^ e₀ := by
    have : (q : ℝ) ^ e₀ = (q : ℝ) ^ (e₀ / 2) * (q : ℝ) ^ (e₀ / 2) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [this]
    have : (0 : ℝ) ≤ (q : ℝ) ^ (e₀ / 2) := by positivity
    nlinarith
  have hw2 : (2 : ℝ) * (q : ℝ) ^ (e₀ / 2) ≤ w := hqe2.trans hw
  have hw1 : 1 ≤ w := by
    have : (1 : ℝ) ≤ w := by linarith
    exact_mod_cast this
  have hz₀1 : 1 ≤ z₀ := le_trans hw1 hwz
  have hz₀N : z₀ ≤ N₁ := le_trans (Nat.le_mul_of_pos_left z₀ (by omega)) hXz
  have hXN : X' ≤ N₁ := le_trans (Nat.le_mul_of_pos_right X' (by omega)) hXz
  have hz₀Y : z₀ ≤ N₂ := le_trans hz₀N hN₁N₂
  have hN₂1 : 1 ≤ N₂ := le_trans hN₁1 hN₁N₂
  -- the membership of `RT`
  have hRT : ∀ rt ∈ RT j N₂ Ω, (∀ i, (rt i).Prime) ∧ ∀ i, z₀ ≤ rt i := by
    intro rt hrt
    rw [RT, Finset.mem_filter, Fintype.mem_piFinset] at hrt
    have hp : ∀ i, (rt i).Prime := fun i => (SieveTypeIIU.mem_primesLe.1 (hrt.1 i)).2
    exact ⟨hp, hΩz rt hp hrt.2⟩
  -- each node: the stop's sum over `n` as a sum over the cofactor `k ∈ S`
  have hterm : ∀ rt ∈ RT j N₂ Ω, ∀ p ∈ primesIco w z₀, ∀ P ∈ (primesIco (p + 1) z₀).powerset,
      (if (∏ i, rt i) * ∏ p' ∈ P, p' ≤ X' ∧ X' < (∏ i, rt i) * (∏ p' ∈ P, p') * p then
        ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if (∏ i, rt i) * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0)
        else 0) =
      ∑ k ∈ S, (if (∏ i, rt i) * ∏ p' ∈ P, p' ≤ X' ∧ X' < (∏ i, rt i) * (∏ p' ∈ P, p') * p ∧
          p ≤ Nat.minFac k ∧ N₁ < (∏ i, rt i) * (∏ p' ∈ P, p') * p * k ∧ (∏ i, rt i) * (∏ p' ∈ P, p') * p * k ≤ N₂
        then dw q a (k * ((∏ i, rt i) * (∏ p' ∈ P, p') * p)) else 0) := by
    intro rt hrt p hp P hP
    obtain ⟨hrtp, hrtz⟩ := hRT rt hrt
    obtain ⟨hpw, hpz, hpp⟩ := mem_primesIco.1 hp
    have hPs : P ⊆ primesIco (p + 1) z₀ := Finset.mem_powerset.1 hP
    have hr0 : 0 < ∏ i, rt i := Finset.prod_pos fun i _ => (hrtp i).pos
    have hpi0 : 0 < ∏ p' ∈ P, p' := Finset.prod_pos fun ℓ hℓ => (mem_primesIco.1 (hPs hℓ)).2.2.pos
    have hWr : rough p ((∏ i, rt i) * (∏ p' ∈ P, p') * p) := by
      intro ℓ hℓp hℓ hd
      rcases (Nat.Prime.dvd_mul hℓ).1 hd with h | h
      · rcases (Nat.Prime.dvd_mul hℓ).1 h with h' | h'
        · obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 h'
          rw [(Nat.prime_dvd_prime_iff_eq hℓ (hrtp i)).1 hi] at hℓp
          have := hrtz i
          omega
        · obtain ⟨ℓ', hℓ', hd'⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 h'
          have hm := mem_primesIco.1 (hPs hℓ')
          rw [(Nat.prime_dvd_prime_iff_eq hℓ hm.2.2).1 hd'] at hℓp
          omega
      · rw [(Nat.prime_dvd_prime_iff_eq hℓ hpp).1 h] at hℓp
        omega
    generalize ∏ i, rt i = r at hr0 hWr ⊢
    generalize ∏ p' ∈ P, p' = pi at hpi0 hWr ⊢
    by_cases htree : r * pi ≤ X' ∧ X' < r * pi * p
    · rw [ite_eq_left htree]
      have hWX : r * pi * p ≤ X' * z₀ := le_trans (Nat.mul_le_mul_right p htree.1) (Nat.mul_le_mul_left X' hpz.le)
      rw [sum_cofactor_window (dw q a) (Nat.mul_pos (Nat.mul_pos hr0 hpi0) hpp.pos) (le_trans hWX hXz) hWr
        htree.2 hWX hP₁1]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hc : p ≤ Nat.minFac k ∧ N₁ < r * pi * p * k ∧ r * pi * p * k ≤ N₂
      · rw [ite_eq_left hc, ite_eq_left ⟨htree.1, htree.2, hc⟩, mul_comm]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.2.2)]
    · rw [ite_eq_right htree]
      exact (Finset.sum_eq_zero fun k _ => ite_eq_right fun h => htree ⟨h.1, h.2.1⟩).symm
  -- the nodes with more than `S₀` primes in `P` are not stops
  have hvanish : ∀ rt ∈ RT j N₂ Ω, ∀ p ∈ primesIco w z₀, ∀ P ∈ (primesIco (p + 1) z₀).powerset, S₀ < P.card →
      ¬ (∏ i, rt i) * ∏ p' ∈ P, p' ≤ X' := by
    intro rt hrt p hp P hP hcard hle
    obtain ⟨hrtp, -⟩ := hRT rt hrt
    have hpw := (mem_primesIco.1 hp).1
    have hPw : ∀ p' ∈ P, w ≤ p' := fun p' hp' => by
      have := (mem_primesIco.1 (Finset.mem_powerset.1 hP hp')).1
      omega
    have h1 : w ^ P.card ≤ ∏ p' ∈ P, p' := Finset.pow_card_le_prod P (fun p' => p') w hPw
    have hr1 : 0 < ∏ i, rt i := Finset.prod_pos fun i _ => (hrtp i).pos
    have h2 : ∏ p' ∈ P, p' ≤ (∏ i, rt i) * ∏ p' ∈ P, p' := Nat.le_mul_of_pos_left _ hr1
    have hS₀e : (2333 / 1000 : ℝ) ≤ e₀ * S₀ := by
      have := Nat.le_ceil ((2333 / 1000 : ℝ) / e₀)
      rw [← hS₀, div_le_iff₀ he₀] at this
      linarith
    have hcardR : (S₀ : ℝ) + 1 ≤ P.card := by exact_mod_cast hcard
    have h3 : (X' : ℝ) < (w : ℝ) ^ P.card := by
      calc (X' : ℝ) ≤ N₁ := by exact_mod_cast hXN
        _ ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := hN₁le
        _ < (q : ℝ) ^ (e₀ * P.card) := Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by nlinarith)
        _ = ((q : ℝ) ^ e₀) ^ P.card := by rw [Real.rpow_mul hq0.le, Real.rpow_natCast]
        _ ≤ (w : ℝ) ^ P.card := pow_le_pow_left₀ (by positivity) hw _
    have h4 : (w : ℝ) ^ P.card ≤ X' := by exact_mod_cast le_trans h1 (le_trans h2 hle)
    linarith
  -- the whole sum, by the size `s` of `P`, as Type II sums over the cofactor `k` and the tuples of primes
  have hsum : ∑ rt ∈ RT j N₂ Ω, ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset,
      (-1 : ℂ) ^ (P.card + 1) *
        (if (∏ i, rt i) * ∏ p' ∈ P, p' ≤ X' ∧ X' < (∏ i, rt i) * (∏ p' ∈ P, p') * p then
          ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if (∏ i, rt i) * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0)
          else 0) =
      ∑ s ∈ Finset.range (S₀ + 1), (-1 : ℂ) ^ (s + 1) * ∑ k ∈ S,
        ∑ x ∈ Fintype.piFinset (fun _ : Fin (j + s + 1) => SieveTypeIIU.primesLe N₂),
          (if ∀ C ∈ cmps j s Ω z₀ w X' N₁ N₂, C.holds k x then dw q a (k * ∏ i, x i) else 0) := by
    have hstep : ∀ rt ∈ RT j N₂ Ω, ∀ p ∈ primesIco w z₀,
        ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℂ) ^ (P.card + 1) *
          (if (∏ i, rt i) * ∏ p' ∈ P, p' ≤ X' ∧ X' < (∏ i, rt i) * (∏ p' ∈ P, p') * p then
            ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n *
              (if (∏ i, rt i) * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) =
        ∑ s ∈ Finset.range (S₀ + 1), (-1 : ℂ) ^ (s + 1) * ∑ k ∈ S,
          ∑ P ∈ (primesIco (p + 1) z₀).powersetCard s,
            (if (∏ i, rt i) * ∏ p' ∈ P, p' ≤ X' ∧ X' < (∏ i, rt i) * (∏ p' ∈ P, p') * p ∧
              p ≤ Nat.minFac k ∧ N₁ < (∏ i, rt i) * (∏ p' ∈ P, p') * p * k ∧
              (∏ i, rt i) * (∏ p' ∈ P, p') * p * k ≤ N₂
            then dw q a (k * ((∏ i, rt i) * (∏ p' ∈ P, p') * p)) else 0) := by
      intro rt hrt p hp
      rw [Finset.sum_congr rfl fun P hP => by rw [hterm rt hrt p hp P hP], Finset.sum_powerset]
      refine (sum_range_eq_of_zero (b := S₀ + 1) (g := fun s => ∑ P ∈ (primesIco (p + 1) z₀).powersetCard s,
          (-1 : ℂ) ^ (P.card + 1) * ∑ k ∈ S,
            (if (∏ i, rt i) * ∏ p' ∈ P, p' ≤ X' ∧ X' < (∏ i, rt i) * (∏ p' ∈ P, p') * p ∧
              p ≤ Nat.minFac k ∧ N₁ < (∏ i, rt i) * (∏ p' ∈ P, p') * p * k ∧
              (∏ i, rt i) * (∏ p' ∈ P, p') * p * k ≤ N₂
            then dw q a (k * ((∏ i, rt i) * (∏ p' ∈ P, p') * p)) else 0)) ?_ ?_).trans ?_
      · intro s hs
        rw [Finset.powersetCard_eq_empty.2 (by omega), Finset.sum_empty]
      · intro s hs
        refine Finset.sum_eq_zero fun P hP => ?_
        have hPs := Finset.mem_powersetCard.1 hP
        have hnot := hvanish rt hrt p hp P (Finset.mem_powerset.2 hPs.1) (by omega)
        rw [Finset.sum_eq_zero fun k _ => ite_eq_right fun h => hnot h.1, mul_zero]
      · refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_comm (s := S), Finset.mul_sum]
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [(Finset.mem_powersetCard.1 hP).2]
    rw [Finset.sum_congr rfl fun rt hrt =>
      (Finset.sum_congr rfl fun p hp => hstep rt hrt p hp).trans Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp_rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl fun rt _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := by
      have := (Finset.mem_Ioc.1 hk).1
      omega
    exact sum_stops_eq Ω hw1 hwz hz₀Y hX' hN₁1 hN₂1 hk1 (fun W => dw q a (k * W))
  rw [hsum]
  have hlog : ∀ (t c : ℝ), 0 < t → t ≤ (q : ℝ) ^ c → Real.log t ≤ c * Real.log q := fun t c ht h => by
    rw [← Real.log_rpow hq0]
    exact Real.log_le_log ht h
  have hX'R : (1 : ℝ) ≤ X' := by exact_mod_cast hX'
  have hbound : ∀ s ∈ Finset.range (S₀ + 1), ‖(-1 : ℂ) ^ (s + 1) * ∑ k ∈ S,
      ∑ x ∈ Fintype.piFinset (fun _ : Fin (j + s + 1) => SieveTypeIIU.primesLe N₂),
        (if ∀ C ∈ cmps j s Ω z₀ w X' N₁ N₂, C.holds k x then dw q a (k * ∏ i, x i) else 0)‖ ≤
      (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
    intro s hs
    have hsS : s ≤ S₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h := hq₁ q hq1 a ha (N₁ / (X' * z₀)) (N₂ / (X' + 1)) S (subset_refl _) hP₁ hP₂ (fun _ => 1)
      (fun _ => by simp) (j + s) (by omega) (cmps j s Ω z₀ w X' N₁ N₂)
      (le_trans (cmps_length Ω _ _ _ _ _) (by omega)) ?_ ?_
    · simpa only [one_mul] using h
    · intro C hC m hm
      have hm1 : 1 ≤ m := by
        have := (Finset.mem_Ioc.1 hm).1
        omega
      have hmP : (m : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := by
        have h1 : (m : ℝ) ≤ ((N₂ / (X' + 1) : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Ioc.1 hm).2
        have h2 : (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        linarith
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
      refine cmps_c_le (s := s) Ω (by positivity) (fun C hC => (hΩc C hC).trans hB3) ?_
        (by exact_mod_cast hw1) hX'R ?_ hm1 ?_ (by exact_mod_cast hN₁1) ?_ C hC
      · exact (hlog z₀ (2333 / 1000) (by exact_mod_cast hz₀1)
          (le_trans (by exact_mod_cast hz₀N) hN₁le)).trans hB1
      · exact (hlog X' (2333 / 1000) (by linarith) (le_trans (by exact_mod_cast hXN) hN₁le)).trans hB1
      · exact (hlog m (2333 / 1000) (by exact_mod_cast hm1) hmP).trans hB1
      · have hN₂q : (N₂ : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 + 1 : ℝ) := by
          rw [Real.rpow_add hq0, Real.rpow_one]
          have h0 : (0 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := by positivity
          have h1 : 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) * q := by
            have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ q by linarith) h0
            linarith
          linarith
        exact (hlog N₂ (2333 / 1000 + 1) (by exact_mod_cast hN₂1) hN₂q).trans hB2
    · intro m hm x hx hall
      have hm1 : 1 ≤ m := by
        have := (Finset.mem_Ioc.1 hm).1
        omega
      have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
      obtain ⟨hΩ', hb, -, hwl, -, -, -, -, hN2⟩ := (cmps_iff (s := s) Ω (by exact_mod_cast hz₀1)
        (by exact_mod_cast hw1) hX'R (by exact_mod_cast hN₁1) (by exact_mod_cast hN₂1) hm1 hx1).1 hall
      refine ⟨fun i => ?_, hN2.trans hN₂le⟩
      by_cases hi : i.val < j
      · have h1 := hΩz (fun u : Fin j => x ⟨u, by omega⟩) (fun u => hx _) hΩ' ⟨i, hi⟩
        have h2 : (z₀ : ℝ) ≤ x i := by exact_mod_cast h1
        have h3 : (w : ℝ) ≤ z₀ := by exact_mod_cast hwz
        linarith
      · have hanti := block_strictAnti hb
        have hu : i.val - j < s + 1 := by omega
        have h1 : x (Fin.last _) ≤ x i := by
          have := hanti.antitone (Fin.le_last (⟨i.val - j, hu⟩ : Fin (s + 1)))
          simp only at this
          convert this using 2 <;> ext <;> simp
          omega
        have h2 : (x (Fin.last _) : ℝ) ≤ x i := by exact_mod_cast h1
        linarith
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ hbound).trans ?_
  rw [Finset.card_range, nsmul_eq_mul]
  calc ((S₀ + 1 : ℕ) : ℝ) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ))
      ≤ (q : ℝ) ^ (δ / 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ)) :=
        mul_le_mul_of_nonneg_right (by push_cast; exact hqS) (by positivity)
    _ = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ / 2 : ℝ) := by
        rw [mul_left_comm, ← Real.rpow_add hq0]
        congr 2
        ring

end Bound

end SieveStops2
