/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 224–227 of 534

File 58 of 135: the parts `rows22475R_224` … `rows22475R_227` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28349 tests: row 87 columns 38–61, row 87 columns 62–66, row 87 columns
67–71, row 87 columns 72–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_224 : rowsJ2 87 88 38 62 ≤ 323590897493301 := by decide +kernel

theorem rows22475R_225 : rowsJ2 87 88 62 67 ≤ 699517963654 := by decide +kernel

theorem rows22475R_226 : rowsJ2 87 88 67 72 ≤ 1876239492990 := by decide +kernel

theorem rows22475R_227 : rowsJ2 87 88 72 77 ≤ 824681519637 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_224
#print axioms SieveCert.rows22475R_227
