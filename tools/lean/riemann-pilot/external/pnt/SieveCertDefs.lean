/-
# Round 618: the certificate's definitions, without Mathlib

The definitions of the loss certificate of `SieveCert.lean` (round 595: `DEN`, `Grid`, `K`, `topK`, `subsetSums`,
`cdiv`, `sumTo`, `V`, `H`, `e`, `lim`, `inside`, `surelyEval`, `invK`, `omK`, `bound2`, `bound4`, `cell`, `cand`,
`inKK`, `ne3`, `allowed`, `counted4`, `row`, `refcost`, `dec`, `cost`, `total`) and of its class `GridOK` (round 607),
and round 609's `rows` (from `SieveCert232.lean`), moved here from those files: verbatim, except that `rows` takes the
section's `[Grid]` in place of its own binder. They are arithmetic on natural numbers, lists and booleans, and the file
imports only `Mathlib.Data.Nat.Notation` (the notation `ℕ`, nothing else), so a file that imports no more than this
one, such as a certificate's part files (`SieveCert226P1.lean` … `SieveCert226P5.lean`), runs its kernel checks without
Mathlib's environment, which `import Mathlib` loads into every process. The lemmas about these definitions, in the reals
and over `Finset`, stay in `SieveCert.lean`, which imports this file and Mathlib.
-/
import Mathlib.Data.Nat.Notation

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

/-- The sum of the rows `a ≤ i < b` of the total. -/
def rows (a b : ℕ) : ℕ := sumTo (b - a) (fun i => sumTo n (fun j => cost (a + i) j))

/-! ### Facts about the grid -/

/-- **The facts about a grid** that the lemmas of `SieveCert.lean` and the route's proofs use. For a given grid each
is checked by `decide`. -/
class GridOK : Prop where
  H_pos : 0 < H
  U1_lt_U2 : U1 < U2
  two_U2_lt : 2 * U2 < DEN
  two_e_lt : 2 * e (n - 1) < DEN
  four_H_le_V : 4 * H ≤ V
  DEN_lt_top : DEN < 2 * (V + n * H)

end SieveCert
