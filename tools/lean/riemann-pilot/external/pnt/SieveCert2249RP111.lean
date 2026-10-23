/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 426–429 of 503

File 111 of 127: the parts `rows2249R_426` … `rows2249R_429` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 23497 tests: row 134 columns 44–106, row 134 columns 107–299, row 135 columns
0–43, row 135 columns 44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_426 : rowsJ2 134 135 44 107 ≤ 298244071243531 := by decide +kernel

theorem rows2249R_427 : rowsJ2 134 135 107 300 ≤ 2092357411396954 := by decide +kernel

theorem rows2249R_428 : rowsJ2 135 136 0 44 ≤ 120620739406726 := by decide +kernel

theorem rows2249R_429 : rowsJ2 135 136 44 300 ≤ 2387851987979107 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_426
#print axioms SieveCert.rows2249R_429
