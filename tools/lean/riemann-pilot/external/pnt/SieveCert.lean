/-
# Round 595: the certificate of the sieve route's loss, checked by the kernel (milestone M7)

Plain statements (`total_le_2333`, `total_div_le`). The loss certificate of
`frontier/linnik/sieve_route_certificate.py`, with the crude bound for Buchstab's `ω`, is redone here in natural numbers
on a grid of cells (`Grid`: the window's ends and the number `n` of cells a side). Each cell's bound is computed from
its corners, rounding up twice (the value of `ω`, then the bound), and is a multiple of `2^{−60}`. On `grid2333`, the
grid of the curve step at `L = 2333/1000` on the window `[401/1000, 485/1000]` of `SieveTypeII.typeII_step` with
`n = 70`, the total is at most `0.88` (`total_le_2333`). The kernel checks it by `decide +kernel`, and `total_le_2333`
depends on `propext` alone.

* The grid. Coordinates are multiples of `1/DEN`, `DEN = 2^40`. The window's ends are `U1 < U2` (for `grid2333`,
  `U1 = ⌈(401/1000)DEN⌉` and `U2 = ⌊(485/1000)DEN⌋`), `V = U2 − U1`, and the cells of side `H = ⌈(DEN/2 − V)/n⌉` start
  at `e k = V + Hk`. `GridOK` lists the facts about the grid that the semantic lemmas below and the route's proofs use;
  for a given grid each is checked by `decide`.
* The tests, as in the certificate: `cand` (a cell of `(α₁, α₂)` that may meet the region and may be non-evaluable),
  `allowed` (the sharp rule for decomposition), `inKK` and `ne3` (the cells of `α₃`), and `counted4` (the cells of
  depth 4). Evaluability is a subset sum of the cell's corners inside `U = (u₁, u₂) ∪ (1 − u₂, 1 − u₁)`
  (`surelyEval`).
* The bounds: `h²` (or `h⁴`) times an upper bound for the crude `ω` on the cell's arguments, rounded up to a multiple
  of `2^{−60}` (`omK`), times the prefactor `1/(ab²)` (or `1/(abcd²)`) at the lower corner, rounded up again to a
  multiple of `2^{−60}` (`bound2`, `bound4`). A cell of depth 2 costs the smaller of its own bound and the sum of its
  cells of depth 4 when it may be decomposed (`dec`, `cost`).

What the tests say about points (the semantic lemmas):

* `eval_of_surelyEval`: if `surelyEval` holds on a box, every point of the box is evaluable (`Eval`).
* `cover2`: a point of the region of depth 2 that is not evaluable lies in a candidate cell.
* `sum_le_of_allowed`, `cover3`: on a cell that may be decomposed, a non-evaluable point keeps `α₁ + α₂ ≤ 1 − u₂`,
  and each non-evaluable `α₃` of the region of depth 3 keeps `α₁ + α₂ + α₃ ≤ 1 − u₂` and lies in a counted row.
* `cover4`: a point of depth 4 that is not evaluable lies in a counted cell.
* `omegaC_le`: the crude `ω` (`omegaC`) on the cell's arguments, widened by `τ < 1/DEN`, is at most `omK/K`.
* `bound2_ge`, `bound4_ge`: each bound is at least `h²` (or `h⁴`) times `omK/K` times the prefactor.
* `total_eq`, `total_div_le`: the total is the double sum of the costs, and if it is at most `0.88K` in natural numbers
  it is at most `0.88` in the reals.

Round 607 made the grid a parameter (`Grid`, with `GridOK`); round 595's grid is `grid2333`, and its `total_le` is
`total_le_2333`.


The file imports only Mathlib.
-/
import Mathlib

namespace SieveCert

/-! ### The grid and the certificate, in natural numbers -/

/-- The denominator of the coordinates. -/
def DEN : ℕ := 2 ^ 40
/-- **A grid of the certificate**: the window's ends `U1 < U2`, in units of `1/DEN`, and the number `n` of cells a
side. -/
class Grid where
  /-- The window's left end. -/
  U1 : ℕ
  /-- The window's right end. -/
  U2 : ℕ
  /-- The number of cells a side. -/
  n : ℕ

export Grid (U1 U2 n)

/-- The fixed point's scale: bounds are in units of `1/K = 2^{−60}`. -/
def K : ℕ := 2 ^ 60
/-- `⌈0.5672 K⌉`. -/
def topK : ℕ := (K * 5672 + 9999) / 10000

/-- The ranges of the subset sums of a box, the empty subset included. -/
def subsetSums : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | p :: rest => subsetSums rest ++ (subsetSums rest).map (fun s => (s.1 + p.1, s.2 + p.2))

/-- Division rounded up. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- `f 0 + ⋯ + f (m − 1)`. -/
def sumTo (m : ℕ) (f : ℕ → ℕ) : ℕ := (List.range m).foldl (fun s i => s + f i) 0

variable [Grid]

/-- The window's width, the least exponent of a sifted prime. -/
def V : ℕ := U2 - U1
/-- The cells' side, `⌈(DEN/2 − V)/n⌉`. -/
def H : ℕ := (DEN / 2 - V + n - 1) / n
/-- The lower end of cell `k`. -/
def e (k : ℕ) : ℕ := V + H * k
/-- `DEN − U1`, the right end of the complement window. -/
def lim : ℕ := DEN - U1

/-- A range `[lo, hi]` of sums lies inside `U`. -/
def inside (lo hi : ℕ) : Bool :=
  (decide (U1 < lo) && decide (hi < U2)) || (decide (DEN - U2 < lo) && decide (hi < DEN - U1))

/-- Some subset sum of the box lies inside `U` on the whole box. -/
def surelyEval (xs : List (ℕ × ℕ)) : Bool := (subsetSums xs).any (fun s => inside s.1 s.2)

/-- `K/max(lo, 1)` rounded up, with `lo = (DEN − s − t − mH)/(t + H)`. -/
def invK (s t m : ℕ) : ℕ :=
  if DEN ≤ s + 2 * t + (m + 1) * H then K else cdiv (K * (t + H)) (DEN - s - t - m * H)

/-- `K` times an upper bound for the crude `ω` on the arguments `[lo, hi]` of a cell, rounded up, where
`lo = (DEN − s − t − mH)/(t + H)` and `hi = (DEN − s − t)/t`: `0` if `hi < 1`, `0.5672` if `lo ≥ 2`, `1/max(lo, 1)`
if `hi < 2`, and the larger of the last two otherwise. -/
def omK (s t m : ℕ) : ℕ :=
  if DEN < s + 2 * t then 0
  else if s + 3 * t + (m + 2) * H ≤ DEN then topK
  else if DEN < s + 3 * t then invK s t m else max (invK s t m) topK

/-- The bound of a cell of depth 2 with lower corner `(a, b)`, in units of `1/K`. -/
def bound2 (a b : ℕ) : ℕ := cdiv (H * H * DEN * omK a b 2) (a * b * b)

/-- The bound of a cell of depth 4 with lower corner `(a, b, c, d)`, in units of `1/K`. -/
def bound4 (a b c d : ℕ) : ℕ := cdiv (H ^ 4 * DEN * omK (a + b + c) d 4) (a * b * c * d * d)

/-- The range of cell `k`. -/
def cell (k : ℕ) : ℕ × ℕ := (e k, e k + H)

/-- The cell `(i, j)` may meet the region of depth 2 and may be non-evaluable. -/
def cand (i j : ℕ) : Bool :=
  decide (e j < e i + H) && decide (2 * e i < DEN) && decide (e i + 2 * e j ≤ DEN) &&
    !(decide (U1 < e i) && decide (e i + H < U2)) && !surelyEval [cell i, cell j]

/-- The cell `k` of `α₃` may meet the region of depth 3 over the cell `(i, j)`. -/
def inKK (i j k : ℕ) : Bool := decide (e k < e j + H) && decide (e i + e j + 2 * e k ≤ DEN)

/-- The cell `(i, j, k)` may be non-evaluable. -/
def ne3 (i j k : ℕ) : Bool := !surelyEval [cell i, cell j, cell k]

/-- The sharp rule: the sums `α₁ + α₂`, and `α₁ + α₂ + α₃` over the counted rows, stay below `1 − u₁`. -/
def allowed (i j : ℕ) : Bool :=
  decide (e i + H + (e j + H) < lim) &&
    (List.range n).all (fun k => !(inKK i j k && ne3 i j k) || decide (e i + H + (e j + H) + (e k + H) < lim))

/-- The cell `(i, j, k, l)` may be non-evaluable, and for `l ≤ k`, which `row` imposes, it may meet the region of
depth 4. -/
def counted4 (i j k l : ℕ) : Bool :=
  decide (e i + e j + e k + 2 * e l ≤ DEN) && !surelyEval [cell i, cell j, cell k, cell l]

/-- The row `(i, j, k)`: the counted cells of `α₄`, which have `l ≤ k`. -/
def row (i j k : ℕ) : ℕ :=
  sumTo (k + 1) (fun l => if counted4 i j k l then bound4 (e i) (e j) (e k) (e l) else 0)

/-- The cost of decomposing the cell `(i, j)`: its counted cells of depth 4. -/
def refcost (i j : ℕ) : ℕ := sumTo n (fun k => if inKK i j k && ne3 i j k then row i j k else 0)

/-- The cell `(i, j)` is decomposed. -/
def dec (i j : ℕ) : Bool := allowed i j && decide (refcost i j ≤ bound2 (e i) (e j))

/-- The cost of the cell `(i, j)`. -/
def cost (i j : ℕ) : ℕ := if cand i j then (if dec i j then refcost i j else bound2 (e i) (e j)) else 0

/-- The certificate's total, in units of `1/K`. -/
def total : ℕ := sumTo n (fun i => sumTo n (fun j => cost i j))

/-! ### Sums -/

omit [Grid] in
theorem foldl_add_eq (f : ℕ → ℕ) (m a : ℕ) :
    (List.range m).foldl (fun s i => s + f i) a = a + ∑ i ∈ Finset.range m, f i := by
  induction m generalizing a with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; simp [add_assoc]

omit [Grid] in
theorem sumTo_eq (m : ℕ) (f : ℕ → ℕ) : sumTo m f = ∑ i ∈ Finset.range m, f i := by
  simp [sumTo, foldl_add_eq]

/-- The total is the double sum of the costs. -/
theorem total_eq : total = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, cost i j := by
  simp [total, sumTo_eq]

/-- The certificate in the reals: if `total ≤ 0.88K` in the natural numbers, then `total/K ≤ 0.88`. -/
theorem total_div_le (htot : total ≤ 88 * K / 100) : (total : ℝ) / K ≤ 88 / 100 := by
  have hK : (0 : ℝ) < K := by norm_num [K]
  rw [div_le_iff₀ hK]
  have h1 : (total : ℝ) ≤ ((88 * K / 100 : ℕ) : ℝ) := by exact_mod_cast htot
  have h2 : ((88 * K / 100 : ℕ) : ℝ) ≤ 88 * K / 100 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 100)]
    exact_mod_cast Nat.div_mul_le_self (88 * K) 100
  linarith

/-! ### Facts about the grid -/

omit [Grid] in
theorem DEN_pos : 0 < DEN := by decide

/-- **The facts about a grid** that the lemmas below and the route's proofs use. For a given grid each is checked
by `decide`. -/
class GridOK : Prop where
  H_pos : 0 < H
  U1_lt_U2 : U1 < U2
  two_U2_lt : 2 * U2 < DEN
  two_e_lt : 2 * e (n - 1) < DEN
  four_H_le_V : 4 * H ≤ V
  DEN_lt_top : DEN < 2 * (V + n * H)

variable [GridOK]

theorem H_pos : 0 < H := GridOK.H_pos
theorem U1_lt_U2 : U1 < U2 := GridOK.U1_lt_U2
theorem two_U2_lt : 2 * U2 < DEN := GridOK.two_U2_lt
theorem U2_le_DEN : U2 ≤ DEN := by have := two_U2_lt; omega
theorem U1_le_DEN : U1 ≤ DEN := le_trans U1_lt_U2.le U2_le_DEN
theorem V_pos : 0 < V := by unfold V; have := U1_lt_U2; omega
theorem two_e_lt (i : ℕ) (hi : i < n) : 2 * e i < DEN := by
  have h : 2 * e (n - 1) < DEN := GridOK.two_e_lt
  have hle : e i ≤ e (n - 1) := by
    unfold e
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  omega
theorem n_pos : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · have h0 := H_pos
    unfold H at h0
    rw [h, Nat.div_zero] at h0
    exact absurd h0 (lt_irrefl 0)
  · exact h
theorem two_V_lt : 2 * V < DEN := by simpa [e] using two_e_lt 0 n_pos
/-- The grid's top `V + nH` lies above `DEN/2`. -/
theorem DEN_lt_top : DEN < 2 * (V + n * H) := GridOK.DEN_lt_top
/-- For a grid with `GridOK`, the grid's top `V + nH` is at most `DEN`. -/
theorem top_le_DEN : V + n * H ≤ DEN := by
  have h1 : 2 * e (n - 1) < DEN := GridOK.two_e_lt
  have h2 : 4 * H ≤ V := GridOK.four_H_le_V
  have h3 := two_V_lt
  have hn : n * H = H * (n - 1) + H := by
    calc n * H = ((n - 1) + 1) * H := by rw [Nat.sub_add_cancel n_pos]
      _ = H * (n - 1) + H := by ring
  unfold e at h1
  omega

/-! ### Points -/

noncomputable section

/-- The window's left end in the exponents. -/
def u1 : ℝ := (U1 : ℝ) / DEN
/-- The window's right end in the exponents. -/
def u2 : ℝ := (U2 : ℝ) / DEN

/-- `s ∈ U = (u₁, u₂) ∪ (1 − u₂, 1 − u₁)`. -/
def InU (s : ℝ) : Prop := (u1 < s ∧ s < u2) ∨ (1 - u2 < s ∧ s < 1 - u1)

/-- A point is evaluable when some sub-sum of its exponents lies in `U`. -/
def Eval (αs : List ℝ) : Prop := ∃ l : List ℝ, l.Sublist αs ∧ InU l.sum

/-- `α ∈ [p.1, p.2]/DEN`. -/
def InRange (p : ℕ × ℕ) (α : ℝ) : Prop := (p.1 : ℝ) ≤ α * DEN ∧ α * DEN ≤ p.2

/-- `α ∈ [e k, e k + H)/DEN`. -/
def InCell (k : ℕ) (α : ℝ) : Prop := (e k : ℝ) ≤ α * DEN ∧ α * DEN < e k + H

omit [Grid] [GridOK] in
theorem DEN_pos' : (0 : ℝ) < DEN := by exact_mod_cast DEN_pos

omit [GridOK] in
theorem inRange_of_inCell {k : ℕ} {α : ℝ} (h : InCell k α) : InRange (cell k) α := by
  refine ⟨h.1, ?_⟩
  simp only [cell]
  push_cast
  exact h.2.le

omit [Grid] [GridOK] in
theorem subsetSums_sound {xs : List (ℕ × ℕ)} {αs : List ℝ} (h : List.Forall₂ InRange xs αs) :
    ∀ s ∈ subsetSums xs, ∃ l : List ℝ, l.Sublist αs ∧ (s.1 : ℝ) ≤ l.sum * DEN ∧ l.sum * DEN ≤ s.2 := by
  induction h with
  | nil =>
    intro s hs
    simp [subsetSums] at hs
    subst hs
    exact ⟨[], List.Sublist.slnil, by simp, by simp⟩
  | @cons p α ps αs' hp _ ih =>
    intro s hs
    simp only [subsetSums, List.mem_append, List.mem_map] at hs
    rcases hs with hs | ⟨s', hs', rfl⟩
    · obtain ⟨l, hl, h1, h2⟩ := ih s hs
      exact ⟨l, hl.cons α, h1, h2⟩
    · obtain ⟨l, hl, h1, h2⟩ := ih s' hs'
      refine ⟨α :: l, hl.cons_cons α, ?_, ?_⟩
      · simp only [List.sum_cons]; push_cast; nlinarith [hp.1]
      · simp only [List.sum_cons]; push_cast; nlinarith [hp.2]

/-- On a grid with `GridOK`, if `surelyEval` holds on a box, every point of the box is evaluable. -/
theorem eval_of_surelyEval {xs : List (ℕ × ℕ)} {αs : List ℝ} (h : List.Forall₂ InRange xs αs)
    (hs : surelyEval xs = true) : Eval αs := by
  simp only [surelyEval, List.any_eq_true] at hs
  obtain ⟨s, hs, hin⟩ := hs
  obtain ⟨l, hl, h1, h2⟩ := subsetSums_sound h s hs
  refine ⟨l, hl, ?_⟩
  have hD := DEN_pos'
  simp only [inside, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hin
  rcases hin with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    have ha' : (U1 : ℝ) < s.1 := by exact_mod_cast ha
    have hb' : (s.2 : ℝ) < U2 := by exact_mod_cast hb
    constructor
    · rw [u1, div_lt_iff₀ hD]; linarith
    · rw [u2, lt_div_iff₀ hD]; linarith
  · right
    have ha' : ((DEN - U2 : ℕ) : ℝ) < s.1 := by exact_mod_cast ha
    have hb' : (s.2 : ℝ) < ((DEN - U1 : ℕ) : ℝ) := by exact_mod_cast hb
    rw [Nat.cast_sub U2_le_DEN] at ha'
    rw [Nat.cast_sub U1_le_DEN] at hb'
    have e1 : 1 - u2 = ((DEN : ℝ) - U2) / DEN := by rw [u2]; field_simp
    have e2 : 1 - u1 = ((DEN : ℝ) - U1) / DEN := by rw [u1]; field_simp
    rw [e1, e2]
    constructor
    · rw [div_lt_iff₀ hD]; linarith
    · rw [lt_div_iff₀ hD]; linarith

theorem not_surelyEval {xs : List (ℕ × ℕ)} {αs : List ℝ} (h : List.Forall₂ InRange xs αs) (hne : ¬ Eval αs) :
    surelyEval xs = false := by
  cases hs : surelyEval xs
  · rfl
  · exact absurd (eval_of_surelyEval h hs) hne

theorem exists_cell {α : ℝ} (h0 : (V : ℝ) ≤ α * DEN) (h1 : α * DEN < V + n * H) : ∃ k < n, InCell k α := by
  have hH : (0 : ℝ) < H := by exact_mod_cast H_pos
  set y := (α * DEN - V) / H with hy
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hH.le
  refine ⟨⌊y⌋₊, ?_, ?_, ?_⟩
  · have : y < n := by rw [hy, div_lt_iff₀ hH]; linarith
    exact_mod_cast (Nat.floor_lt hy0).2 this
  · have hf := Nat.floor_le hy0
    simp only [e]
    push_cast
    have : (⌊y⌋₊ : ℝ) * H ≤ α * DEN - V := by
      calc (⌊y⌋₊ : ℝ) * H ≤ y * H := by gcongr
        _ = α * DEN - V := by rw [hy]; field_simp
    linarith
  · have hf := Nat.lt_floor_add_one y
    simp only [e]
    push_cast
    have : α * DEN - V < ((⌊y⌋₊ : ℝ) + 1) * H := by
      calc α * DEN - V = y * H := by rw [hy]; field_simp
        _ < ((⌊y⌋₊ : ℝ) + 1) * H := by gcongr
    linarith

/-- A point of the region of depth 2 that is not evaluable lies in a candidate cell. The region's conditions:
`α₂ ≥ v`, `α₂ < α₁`, `α₁` below the grid's end, and `α₁ + 2α₂ < 1 + 1/DEN` (written in units of
`1/DEN`). -/
theorem cover2 {α₁ α₂ : ℝ} (h2 : (V : ℝ) ≤ α₂ * DEN) (h21 : α₂ < α₁) (h1 : α₁ * DEN < V + n * H)
    (hreg : α₁ * DEN + 2 * (α₂ * DEN) < DEN + 1) (hne : ¬ Eval [α₁, α₂]) :
    ∃ i < n, ∃ j < n, cand i j = true ∧ InCell i α₁ ∧ InCell j α₂ := by
  have hD := DEN_pos'
  have h21' : α₂ * DEN < α₁ * DEN := mul_lt_mul_of_pos_right h21 hD
  obtain ⟨i, hi, hci⟩ := exists_cell (by linarith) h1
  obtain ⟨j, hj, hcj⟩ := exists_cell h2 (by linarith)
  refine ⟨i, hi, j, hj, ?_, hci, hcj⟩
  have hne2 : surelyEval [cell i, cell j] = false :=
    not_surelyEval (List.Forall₂.cons (inRange_of_inCell hci)
      (List.Forall₂.cons (inRange_of_inCell hcj) List.Forall₂.nil)) hne
  have c1 : e j < e i + H := by
    have : (e j : ℝ) < e i + H := by linarith [hcj.1, hci.2]
    exact_mod_cast this
  have c3 : e i + 2 * e j ≤ DEN := by
    have : (e i : ℝ) + 2 * e j < DEN + 1 := by linarith [hci.1, hcj.1]
    have : e i + 2 * e j < DEN + 1 := by exact_mod_cast this
    omega
  have c4 : ¬ (U1 < e i ∧ e i + H < U2) := by
    rintro ⟨ha, hb⟩
    apply hne
    refine ⟨[α₁], (List.Sublist.cons_cons α₁ (List.nil_sublist _)), Or.inl ⟨?_, ?_⟩⟩
    · have : (U1 : ℝ) < e i := by exact_mod_cast ha
      simp only [List.sum_cons, List.sum_nil, add_zero]
      rw [u1, div_lt_iff₀ hD]; linarith [hci.1]
    · have : (e i : ℝ) + H < U2 := by exact_mod_cast hb
      simp only [List.sum_cons, List.sum_nil, add_zero]
      rw [u2, lt_div_iff₀ hD]; linarith [hci.2]
  simp only [cand, hne2, Bool.not_false, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨⟨⟨c1, two_e_lt i hi⟩, c3⟩, not_and_or.mp c4⟩

theorem lim_div : (lim : ℝ) / DEN = 1 - u1 := by
  have hD := DEN_pos'
  rw [lim, Nat.cast_sub U1_le_DEN, u1]
  field_simp

theorem lt_one_sub_u1 {x : ℝ} {N : ℕ} (hx : x * DEN < N) (hN : N < lim) : x < 1 - u1 := by
  have hD := DEN_pos'
  rw [← lim_div, lt_div_iff₀ hD]
  have : (N : ℝ) < lim := by exact_mod_cast hN
  linarith

omit [GridOK] in
theorem le_of_not_inU {s : ℝ} (hlt : s < 1 - u1) (hne : ¬ InU s) : s ≤ 1 - u2 := by
  by_contra h
  exact hne (Or.inr ⟨not_le.mp h, hlt⟩)

omit [GridOK] in
theorem e_add_H_le {j : ℕ} (hj : j < n) : (e j : ℝ) + H ≤ V + n * H := by
  have : e j + H ≤ V + n * H := by
    unfold e
    have : H * j + H ≤ n * H := by nlinarith
    omega
  exact_mod_cast this

/-- On a grid with `GridOK`, on a cell that may be decomposed, a non-evaluable point has `α₁ + α₂ ≤ 1 − u₂`. -/
theorem sum_le_of_allowed {i j : ℕ} {α₁ α₂ : ℝ} (ha : allowed i j = true) (hci : InCell i α₁)
    (hcj : InCell j α₂) (hne : ¬ Eval [α₁, α₂]) : α₁ + α₂ ≤ 1 - u2 := by
  simp only [allowed, Bool.and_eq_true, decide_eq_true_eq] at ha
  have hlt : α₁ + α₂ < 1 - u1 := by
    apply lt_one_sub_u1 (N := e i + H + (e j + H)) _ ha.1
    push_cast
    linarith [hci.2, hcj.2]
  refine le_of_not_inU hlt fun hU => hne ⟨[α₁, α₂], List.Sublist.refl _, ?_⟩
  simpa using hU

/-- On a cell that may be decomposed, a non-evaluable `α₃` of the region of depth 3 keeps
`α₁ + α₂ + α₃ ≤ 1 − u₂`, and lies in a counted row. -/
theorem cover3 {i j : ℕ} {α₁ α₂ α₃ : ℝ} (hj : j < n) (ha : allowed i j = true) (hci : InCell i α₁)
    (hcj : InCell j α₂) (h3 : (V : ℝ) ≤ α₃ * DEN) (h32 : α₃ < α₂)
    (hreg : α₁ * DEN + α₂ * DEN + 2 * (α₃ * DEN) < DEN + 1) (hne : ¬ Eval [α₁, α₂, α₃]) :
    α₁ + α₂ + α₃ ≤ 1 - u2 ∧ ∃ k < n, inKK i j k = true ∧ ne3 i j k = true ∧ InCell k α₃ := by
  have hD := DEN_pos'
  have h32' : α₃ * DEN < α₂ * DEN := mul_lt_mul_of_pos_right h32 hD
  obtain ⟨k, hk, hck⟩ := exists_cell h3 (by linarith [hcj.2, e_add_H_le hj])
  have hkk : inKK i j k = true := by
    simp only [inKK, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · have : (e k : ℝ) < e j + H := by linarith [hck.1, hcj.2]
      exact_mod_cast this
    · have : (e i : ℝ) + e j + 2 * e k < DEN + 1 := by linarith [hci.1, hcj.1, hck.1]
      have : e i + e j + 2 * e k < DEN + 1 := by exact_mod_cast this
      omega
  have hn3 : ne3 i j k = true := by
    simp only [ne3, Bool.not_eq_true']
    exact not_surelyEval (List.Forall₂.cons (inRange_of_inCell hci) (List.Forall₂.cons (inRange_of_inCell hcj)
      (List.Forall₂.cons (inRange_of_inCell hck) List.Forall₂.nil))) hne
  refine ⟨?_, k, hk, hkk, hn3, hck⟩
  simp only [allowed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at ha
  have hk' := ha.2 k hk
  simp only [hkk, hn3, Bool.and_self, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hk'
  have hlt : α₁ + α₂ + α₃ < 1 - u1 := by
    apply lt_one_sub_u1 (N := e i + H + (e j + H) + (e k + H)) _ hk'
    push_cast
    linarith [hci.2, hcj.2, hck.2]
  refine le_of_not_inU hlt fun hU => hne ⟨[α₁, α₂, α₃], List.Sublist.refl _, ?_⟩
  simpa [add_assoc] using hU

/-- A non-evaluable point of the region of depth 4 lies in a counted cell, with `l ≤ k`. -/
theorem cover4 {i j k : ℕ} {α₁ α₂ α₃ α₄ : ℝ} (hk : k < n) (hci : InCell i α₁) (hcj : InCell j α₂)
    (hck : InCell k α₃) (h4 : (V : ℝ) ≤ α₄ * DEN) (h43 : α₄ < α₃)
    (hreg : α₁ * DEN + α₂ * DEN + α₃ * DEN + 2 * (α₄ * DEN) < DEN + 1) (hne : ¬ Eval [α₁, α₂, α₃, α₄]) :
    ∃ l < k + 1, counted4 i j k l = true ∧ InCell l α₄ := by
  have hD := DEN_pos'
  have h43' : α₄ * DEN < α₃ * DEN := mul_lt_mul_of_pos_right h43 hD
  obtain ⟨l, -, hcl⟩ := exists_cell h4 (by linarith [hck.2, e_add_H_le hk])
  refine ⟨l, ?_, ?_, hcl⟩
  · have h1 : (e l : ℝ) < e k + H := by linarith [hcl.1, hck.2]
    have h2 : e l < e k + H := by exact_mod_cast h1
    have h3 : H * l < H * (k + 1) := by unfold e at h2; rw [Nat.mul_succ]; omega
    exact Nat.lt_of_mul_lt_mul_left h3
  · simp only [counted4, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    constructor
    · have : (e i : ℝ) + e j + e k + 2 * e l < DEN + 1 := by linarith [hci.1, hcj.1, hck.1, hcl.1]
      have : e i + e j + e k + 2 * e l < DEN + 1 := by exact_mod_cast this
      omega
    · exact not_surelyEval (List.Forall₂.cons (inRange_of_inCell hci) (List.Forall₂.cons (inRange_of_inCell hcj)
        (List.Forall₂.cons (inRange_of_inCell hck) (List.Forall₂.cons (inRange_of_inCell hcl)
          List.Forall₂.nil)))) hne

/-! ### The crude `ω` -/

/-- The crude upper bound for Buchstab's `ω`: `0` below `1`, `1/u` on `[1, 2)` and `0.5672` from `2` on. -/
def omegaC (u : ℝ) : ℝ := if u < 1 then 0 else if u < 2 then 1 / u else 5672 / 10000

omit [Grid] [GridOK] in
theorem K_pos' : (0 : ℝ) < K := by norm_num [K]

omit [Grid] [GridOK] in
theorem topK_ge : (5672 / 10000 : ℝ) ≤ topK / K := by
  rw [le_div_iff₀ K_pos']
  have h : K * 5672 ≤ topK * 10000 := by decide
  have h' : (K : ℝ) * 5672 ≤ topK * 10000 := by exact_mod_cast h
  linarith

omit [Grid] [GridOK] in
theorem div_le_cdiv (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ cdiv a b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have h := Nat.lt_div_mul_add (a := a + b - 1) hb
  have h2 : a ≤ cdiv a b * b := by unfold cdiv; omega
  exact_mod_cast h2

omit [GridOK] in
/-- **The crude `ω` on a cell.** Let the other exponents sum to `σ` and the last be `α`, with `s ≤ σ·DEN`,
`t ≤ α·DEN ≤ t + H` and `(σ + α)DEN ≤ s + t + mH`, as for the lower corner `(s, t)` of a cell of `m` variables. Then
on the argument `(1 − σ − α + τ)/α`, widened by `0 ≤ τ < 1/DEN`, the crude `ω` is at most `omK s t m / K`. -/
theorem omegaC_le {s t m : ℕ} {σ α τ : ℝ} (ht : 0 < t) (hσ : (s : ℝ) ≤ σ * DEN) (hα : (t : ℝ) ≤ α * DEN)
    (hαH : α * DEN ≤ t + H) (hsum : (σ + α) * DEN ≤ s + t + m * H) (hτ0 : 0 ≤ τ) (hτ : τ * DEN < 1) :
    omegaC ((1 - σ - α + τ) / α) ≤ (omK s t m : ℝ) / K := by
  have hD := DEN_pos'
  have hK := K_pos'
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hα0 : 0 < α := by
    by_contra h
    have : α * DEN ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hD.le
    linarith
  set u := (1 - σ - α + τ) / α with hu
  have hua : u * α = 1 - σ - α + τ := by rw [hu]; field_simp
  -- `u < 1` when `DEN < s + 2t`
  have lt1 : DEN < s + 2 * t → u < 1 := by
    intro h
    have h' : (DEN : ℝ) + 1 ≤ s + 2 * t := by exact_mod_cast h
    have : (1 + τ) * DEN < (σ + 2 * α) * DEN := by nlinarith
    have : 1 + τ < σ + 2 * α := lt_of_mul_lt_mul_right this hD.le
    nlinarith
  -- `u ≥ 2` when `s + 3t + (m + 2)H ≤ DEN`
  have ge2 : s + 3 * t + (m + 2) * H ≤ DEN → 2 ≤ u := by
    intro h
    have h' : (s : ℝ) + 3 * t + (m + 2) * H ≤ DEN := by exact_mod_cast h
    have : (σ + 3 * α) * DEN ≤ (1 + τ) * DEN := by nlinarith
    have : σ + 3 * α ≤ 1 + τ := le_of_mul_le_mul_right this hD
    nlinarith
  -- `u < 2` when `DEN < s + 3t`
  have lt2 : DEN < s + 3 * t → u < 2 := by
    intro h
    have h' : (DEN : ℝ) + 1 ≤ s + 3 * t := by exact_mod_cast h
    have : (1 + τ) * DEN < (σ + 3 * α) * DEN := by nlinarith
    have : 1 + τ < σ + 3 * α := lt_of_mul_lt_mul_right this hD.le
    nlinarith
  -- `1/u ≤ (t + H)/D` when `u ≥ 1` and `D = DEN − s − t − mH > 0`
  have inv_le : ∀ D : ℝ, D = DEN - s - t - m * H → 0 < D → 1 ≤ u → 1 / u ≤ (t + H) / D := by
    intro D hD' hDpos hu1
    have hu0 : 0 < u := by linarith
    have h1 : D / DEN ≤ u * α := by
      rw [hua, div_le_iff₀ hD]
      nlinarith
    have h2 : D ≤ u * (t + H) := by
      have : D ≤ u * α * DEN := by rwa [div_le_iff₀ hD] at h1
      nlinarith
    rw [div_le_div_iff₀ hu0 hDpos]
    linarith
  have hcases : omegaC u = 0 ∨ (1 ≤ u ∧ u < 2 ∧ omegaC u = 1 / u) ∨ (2 ≤ u ∧ omegaC u = 5672 / 10000) := by
    unfold omegaC
    by_cases h1 : u < 1
    · left; simp [h1]
    · by_cases h2 : u < 2
      · right; left; exact ⟨not_lt.mp h1, h2, by simp [h1, h2]⟩
      · right; right; exact ⟨not_lt.mp h2, by simp [h1, h2]⟩
  -- `1/u ≤ invK/K` for `u ≥ 1`
  have hinv : 1 ≤ u → 1 / u ≤ (invK s t m : ℝ) / K := by
    intro hu1
    have hu0 : 0 < u := by linarith
    unfold invK
    by_cases hC : DEN ≤ s + 2 * t + (m + 1) * H
    · simp only [hC, ite_true, div_self (ne_of_gt hK)]
      rw [div_le_one hu0]; exact hu1
    · simp only [hC, ite_false]
      have hmH : (m + 1) * H = m * H + H := by ring
      have hDnat : s + t + m * H < DEN := by omega
      have hpos : 0 < DEN - s - t - m * H := by omega
      have hDcast : ((DEN - s - t - m * H : ℕ) : ℝ) = (DEN : ℝ) - s - t - m * H := by
        have h1 : s ≤ DEN := by omega
        have h2 : t ≤ DEN - s := by omega
        have h3 : m * H ≤ DEN - s - t := by omega
        rw [Nat.cast_sub h3, Nat.cast_sub h2, Nat.cast_sub h1]; push_cast; ring
      have hc := div_le_cdiv (K * (t + H)) (DEN - s - t - m * H) hpos
      rw [hDcast] at hc
      push_cast at hc
      have hDpos : (0 : ℝ) < (DEN : ℝ) - s - t - m * H := by
        have : (s : ℝ) + t + m * H < DEN := by exact_mod_cast hDnat
        linarith
      have hi := inv_le _ rfl hDpos hu1
      rw [le_div_iff₀ hK]
      calc 1 / u * K ≤ (t + H) / ((DEN : ℝ) - s - t - m * H) * K := by gcongr
        _ = K * (t + H) / ((DEN : ℝ) - s - t - m * H) := by ring
        _ ≤ _ := hc
  have hinv0 : (0 : ℝ) ≤ (invK s t m : ℝ) / K := by positivity
  have htop0 : (0 : ℝ) ≤ (topK : ℝ) / K := by positivity
  -- the cases of `omK`
  by_cases hA : DEN < s + 2 * t
  · have hu := lt1 hA
    have h0 : omK s t m = 0 := by simp [omK, hA]
    rw [h0]
    simp [omegaC, hu]
  by_cases hB : s + 3 * t + (m + 2) * H ≤ DEN
  · have hu := ge2 hB
    have h0 : omK s t m = topK := by simp [omK, hA, hB]
    rw [h0]
    have : omegaC u = 5672 / 10000 := by
      simp [omegaC, show ¬ u < 1 by linarith, show ¬ u < 2 by linarith]
    rw [this]; exact topK_ge
  by_cases hC2 : DEN < s + 3 * t
  · have hu2 := lt2 hC2
    have h0 : omK s t m = invK s t m := by simp [omK, hA, hB, hC2]
    rw [h0]
    rcases hcases with h | ⟨h1, -, h⟩ | ⟨h2, -⟩
    · rw [h]; exact hinv0
    · rw [h]; exact hinv h1
    · linarith
  · have h0 : omK s t m = max (invK s t m) topK := by simp [omK, hA, hB, hC2]
    rw [h0, Nat.cast_max, ← max_div_div_right hK.le]
    rcases hcases with h | ⟨h1, -, h⟩ | ⟨-, h⟩
    · rw [h]; exact le_trans hinv0 (le_max_left _ _)
    · rw [h]; exact le_trans (hinv h1) (le_max_left _ _)
    · rw [h]; exact le_trans topK_ge (le_max_right _ _)

/-! ### The cells' bounds -/

theorem e_pos (k : ℕ) : 0 < e k := by unfold e; have := V_pos; omega

omit [GridOK] in
/-- A cell of depth 2 with lower corner `(a, b)` costs at least `h²` times `omK/K` times `1/(ab²)`, in the
exponents. -/
theorem bound2_ge {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ((H : ℝ) / DEN) ^ 2 * ((omK a b 2 : ℝ) / K) / (((a : ℝ) / DEN) * ((b : ℝ) / DEN) ^ 2) ≤
      (bound2 a b : ℝ) / K := by
  have hD := DEN_pos'
  have hK := K_pos'
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hc := div_le_cdiv (H * H * DEN * omK a b 2) (a * b * b) (by positivity)
  have heq : ((H : ℝ) / DEN) ^ 2 * ((omK a b 2 : ℝ) / K) / (((a : ℝ) / DEN) * ((b : ℝ) / DEN) ^ 2) =
      ((H * H * DEN * omK a b 2 : ℕ) : ℝ) / ((a * b * b : ℕ) : ℝ) / K := by
    push_cast; field_simp
  rw [heq, bound2]
  exact div_le_div_of_nonneg_right hc hK.le

omit [GridOK] in
/-- A cell of depth 4 with lower corner `(a, b, c, d)` costs at least `h⁴` times `omK/K` times `1/(abcd²)`. -/
theorem bound4_ge {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ((H : ℝ) / DEN) ^ 4 * ((omK (a + b + c) d 4 : ℝ) / K) /
        (((a : ℝ) / DEN) * ((b : ℝ) / DEN) * ((c : ℝ) / DEN) * ((d : ℝ) / DEN) ^ 2) ≤
      (bound4 a b c d : ℝ) / K := by
  have hD := DEN_pos'
  have hK := K_pos'
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hcd := div_le_cdiv (H ^ 4 * DEN * omK (a + b + c) d 4) (a * b * c * d * d) (by positivity)
  have heq : ((H : ℝ) / DEN) ^ 4 * ((omK (a + b + c) d 4 : ℝ) / K) /
        (((a : ℝ) / DEN) * ((b : ℝ) / DEN) * ((c : ℝ) / DEN) * ((d : ℝ) / DEN) ^ 2) =
      ((H ^ 4 * DEN * omK (a + b + c) d 4 : ℕ) : ℝ) / ((a * b * c * d * d : ℕ) : ℝ) / K := by
    push_cast; field_simp
  rw [heq, bound4]
  exact div_le_div_of_nonneg_right hcd hK.le

/-! ### The costs -/

omit [GridOK] in
theorem allowed_of_dec {i j : ℕ} (h : dec i j = true) : allowed i j = true := by
  simp only [dec, Bool.and_eq_true] at h
  exact h.1

omit [GridOK] in
theorem cost_of_dec {i j : ℕ} (hc : cand i j = true) (hd : dec i j = true) : cost i j = refcost i j := by
  simp [cost, hc, hd]

omit [GridOK] in
theorem cost_of_not_dec {i j : ℕ} (hc : cand i j = true) (hd : dec i j = false) :
    cost i j = bound2 (e i) (e j) := by
  simp [cost, hc, hd]

omit [GridOK] in
theorem refcost_eq (i j : ℕ) : refcost i j = ∑ k ∈ Finset.range n, if inKK i j k && ne3 i j k then
    ∑ l ∈ Finset.range (k + 1), (if counted4 i j k l then bound4 (e i) (e j) (e k) (e l) else 0) else 0 := by
  simp only [refcost, row, sumTo_eq]

end

end SieveCert

namespace SieveCert

/-- **The grid of `SieveTypeII.typeII_step`'s window**: `U1 = ⌈(401/1000)DEN⌉`, `U2 = ⌊(485/1000)DEN⌋`, `n = 70`. -/
@[instance_reducible] def grid2333 : Grid := ⟨(401 * DEN + 999) / 1000, 485 * DEN / 1000, 70⟩

theorem gridOK2333 : @GridOK grid2333 :=
  @GridOK.mk grid2333 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **The certificate on `grid2333`**: the loss's bound is at most `0.88`, checked by the kernel. -/
theorem total_le_2333 : @total grid2333 ≤ 88 * K / 100 := by decide +kernel

end SieveCert

#print axioms SieveCert.total_le_2333
#print axioms SieveCert.gridOK2333
#print axioms SieveCert.total_eq
#print axioms SieveCert.total_div_le
#print axioms SieveCert.eval_of_surelyEval
#print axioms SieveCert.cover2
#print axioms SieveCert.sum_le_of_allowed
#print axioms SieveCert.cover3
#print axioms SieveCert.cover4
#print axioms SieveCert.omegaC_le
#print axioms SieveCert.bound2_ge
#print axioms SieveCert.bound4_ge
#print axioms SieveCert.refcost_eq
