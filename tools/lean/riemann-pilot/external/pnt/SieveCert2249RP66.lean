/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 251–254 of 503

File 66 of 127: the parts `rows2249R_251` … `rows2249R_254` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 25910 tests: row 93 columns 62–66, row 93 columns 67–72, row 93 columns 73–79,
row 93 columns 80–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_251 : rowsJ2 93 94 62 67 ≤ 0 := by decide +kernel

theorem rows2249R_252 : rowsJ2 93 94 67 73 ≤ 285471596724 := by decide +kernel

theorem rows2249R_253 : rowsJ2 93 94 73 80 ≤ 15689284951034 := by decide +kernel

theorem rows2249R_254 : rowsJ2 93 94 80 300 ≤ 1209489876494376 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_251
#print axioms SieveCert.rows2249R_254
