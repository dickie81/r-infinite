/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 284–287 of 534

File 73 of 135: the parts `rows22475R_284` … `rows22475R_287` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29586 tests: row 96 columns 0–52, row 96 columns 53–60, row 96 columns 61–65,
row 96 columns 66–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_284 : rowsJ2 96 97 0 53 ≤ 636124650515289 := by decide +kernel

theorem rows22475R_285 : rowsJ2 96 97 53 61 ≤ 0 := by decide +kernel

theorem rows22475R_286 : rowsJ2 96 97 61 66 ≤ 0 := by decide +kernel

theorem rows22475R_287 : rowsJ2 96 97 66 72 ≤ 147742541284 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_284
#print axioms SieveCert.rows22475R_287
