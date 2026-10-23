/-
# Round 705: the refined certificate's definitions, without Mathlib

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

The certificate of `SieveCertDefs.lean` with the evaluable two-prime parts of its dropped cells of depth 2 kept
(`frontier/linnik/SIEVE-ROUTE.md` §28). A dropped term `S(A_{p₁p₂}, p₂)` counts the `n = p₁p₂m` whose cofactor `m` has
no prime factor below `p₂`; its part with `m = q₁q₂`, `p₂ < q₁ < q₂` primes, is a Type II sum where some subset sum of
the exponents lies in the window, so a refined route keeps it instead of dropping it, and its `B`-count comes off the
cell's cost.

* `reg2`: the box of the cell `(i, j)` lies in the region of the kept parts, `e_j + H ≤ e_i` and `2(e_i + H) ≤ DEN`
  (`α₂ < α₁ < 1/2` on the box).
* `keep`: the cell `k` of `q₁` is kept below `(i, j)`: `e_j + H ≤ e_k` (`q₁ > p₂` on the box),
  `2(e_k + H) + e_i + e_j + 2H ≤ DEN` (`q₁ < q₂` on the box), and the box `(i, j, k)` surely evaluable.
* `keepK`: the kept share of the cell `k`, `⌊K·H³·DEN/((e_i + H)(e_j + H)(e_k + H)(DEN − e_i − e_j − e_k))⌋`, a lower
  bound for the `B`-density `dα₁dα₂dβ/(α₁α₂βγ)` over the box in units of `1/K`.
* `sub2`: the kept shares below `(i, j)`, for a cell of `reg2`; `cost2`: a candidate cell that is not decomposed costs
  its bound less `sub2`, truncated at `0`; the other cells cost as in `cost`.
* `total2`, `rows2`, `rowsJ2`: `total`, `rows` and `rowsJ` (`SieveCertColsDefs.lean`) with `cost2`.

The decisions `cand` and `dec` are the certificate's own, so the decomposition of `SieveBuch.lean` is unchanged. These
are arithmetic on natural numbers, lists and booleans, and the file imports only `SieveCertDefs.lean`, so a part file
that imports no more than this one runs its kernel checks without `Mathlib` (round 618).
-/
import SieveCertDefs

namespace SieveCert

variable [Grid]

/-- The box of the cell `(i, j)` lies in the region of the kept parts: `e_j + H ≤ e_i` and `2(e_i + H) ≤ DEN`. -/
def reg2 (i j : ℕ) : Bool := decide (e j + H ≤ e i) && decide (2 * (e i + H) ≤ DEN)

/-- The cell `k` of `q₁` is kept below the cell `(i, j)`: `e_j + H ≤ e_k`, `2(e_k + H) + e_i + e_j + 2H ≤ DEN`, and the
box `(i, j, k)` surely evaluable. -/
def keep (i j k : ℕ) : Bool :=
  decide (e j + H ≤ e k) && decide (2 * (e k + H) + e i + e j + 2 * H ≤ DEN) && surelyEval [cell i, cell j, cell k]

/-- The kept share of the cell `k` below `(i, j)`, in units of `1/K`, rounded down:
`⌊K·H³·DEN/((e_i + H)(e_j + H)(e_k + H)(DEN − e_i − e_j − e_k))⌋`. -/
def keepK (i j k : ℕ) : ℕ := K * H ^ 3 * DEN / ((e i + H) * (e j + H) * (e k + H) * (DEN - e i - e j - e k))

/-- The kept shares below the cell `(i, j)`, for a cell of `reg2`. -/
def sub2 (i j : ℕ) : ℕ := if reg2 i j then sumTo n (fun k => if keep i j k then keepK i j k else 0) else 0

/-- The refined cost of the cell `(i, j)`: a candidate cell that is not decomposed costs its bound less `sub2`, truncated
at `0`. -/
def cost2 (i j : ℕ) : ℕ :=
  if cand i j then (if dec i j then refcost i j else bound2 (e i) (e j) - sub2 i j) else 0

/-- The refined certificate's total, in units of `1/K`. -/
def total2 : ℕ := sumTo n (fun i => sumTo n (fun j => cost2 i j))

/-- The sum of the rows `a ≤ i < b` of the refined total. -/
def rows2 (a b : ℕ) : ℕ := sumTo (b - a) (fun i => sumTo n (fun j => cost2 (a + i) j))

/-- The sum of the refined costs of the rows `a ≤ i < b` over the columns `j₀ ≤ j < j₁`. -/
def rowsJ2 (a b j₀ j₁ : ℕ) : ℕ := sumTo (b - a) (fun i => sumTo (j₁ - j₀) (fun j => cost2 (a + i) (j₀ + j)))

end SieveCert
