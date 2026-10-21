/-
# Round 624: the certificate's rows cut by columns (the definition)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

`rowsJ a b j₀ j₁` is the sum of the costs of the rows `a ≤ i < b` over the columns `j₀ ≤ j < j₁`, so that a heavy row
of a certificate can be checked by the kernel in several pieces (`rows a b` is `rowsJ a b 0 n`, `SieveCertCols.lean`).
A row's kernel memory grows with its depth-4 tests; the heaviest rows of a grid with `n = 400` exceed the shell's
memory alone (the lead's probe of round 624: killed at 13.1 GiB).

The file imports `SieveCertDefs.lean` only, so the part files that use it load no more than it does.
-/
import SieveCertDefs

namespace SieveCert

section

variable [Grid]

/-- The sum of the costs of the rows `a ≤ i < b` over the columns `j₀ ≤ j < j₁`. -/
def rowsJ (a b j₀ j₁ : ℕ) : ℕ := sumTo (b - a) (fun i => sumTo (j₁ - j₀) (fun j => cost (a + i) (j₀ + j)))

end

end SieveCert
