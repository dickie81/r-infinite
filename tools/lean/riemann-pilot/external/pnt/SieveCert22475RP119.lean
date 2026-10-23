/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 461–463 of 534

File 119 of 135: the parts `rows22475R_461` … `rows22475R_463` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 23083 tests: row 138 columns 0–42, row 138 columns 43–299, row 139 columns
0–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_461 : rowsJ2 138 139 0 43 ≤ 125969427731252 := by decide +kernel

theorem rows22475R_462 : rowsJ2 138 139 43 300 ≤ 2502850407331762 := by decide +kernel

theorem rows22475R_463 : rowsJ2 139 140 0 43 ≤ 129786125246716 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_461
#print axioms SieveCert.rows22475R_463
