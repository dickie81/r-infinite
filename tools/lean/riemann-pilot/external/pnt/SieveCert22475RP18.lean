/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 71–74 of 534

File 18 of 135: the parts `rows22475R_71` … `rows22475R_74` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26371 tests: row 56 columns 0–34, row 56 columns 35–43, row 56 columns 44–51,
row 56 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_71 : rowsJ2 56 57 0 35 ≤ 1353789101749041 := by decide +kernel

theorem rows22475R_72 : rowsJ2 56 57 35 44 ≤ 359905779362755 := by decide +kernel

theorem rows22475R_73 : rowsJ2 56 57 44 52 ≤ 563413059638404 := by decide +kernel

theorem rows22475R_74 : rowsJ2 56 57 52 300 ≤ 301304718317598 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_71
#print axioms SieveCert.rows22475R_74
