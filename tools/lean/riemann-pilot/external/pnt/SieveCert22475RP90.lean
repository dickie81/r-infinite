/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 347–350 of 534

File 90 of 135: the parts `rows22475R_347` … `rows22475R_350` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26733 tests: row 107 columns 59–65, row 107 columns 66–74, row 107 columns
75–299, row 108 columns 0–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_347 : rowsJ2 107 108 59 66 ≤ 4727767975390 := by decide +kernel

theorem rows22475R_348 : rowsJ2 107 108 66 75 ≤ 8147420757390 := by decide +kernel

theorem rows22475R_349 : rowsJ2 107 108 75 300 ≤ 908030248207457 := by decide +kernel

theorem rows22475R_350 : rowsJ2 108 109 0 52 ≤ 384996785695958 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_347
#print axioms SieveCert.rows22475R_350
