/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 31–35 of 503

File 8 of 127: the parts `rows2249R_31` … `rows2249R_35` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (5 parts, 25741 tests: row 44 columns 35–43, row 44 columns 44–299, row 45 columns 0–34,
row 45 columns 35–43, row 45 columns 44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound,
by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_31 : rowsJ2 44 45 35 44 ≤ 382749301307439 := by decide +kernel

theorem rows2249R_32 : rowsJ2 44 45 44 300 ≤ 53638282917201 := by decide +kernel

theorem rows2249R_33 : rowsJ2 45 46 0 35 ≤ 1852130869516239 := by decide +kernel

theorem rows2249R_34 : rowsJ2 45 46 35 44 ≤ 369068929933099 := by decide +kernel

theorem rows2249R_35 : rowsJ2 45 46 44 300 ≤ 112438360854648 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_31
#print axioms SieveCert.rows2249R_35
