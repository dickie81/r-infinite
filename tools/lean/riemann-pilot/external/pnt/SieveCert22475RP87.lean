/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 335–338 of 534

File 87 of 135: the parts `rows22475R_335` … `rows22475R_338` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29867 tests: row 105 columns 0–52, row 105 columns 53–58, row 105 columns
59–64, row 105 columns 65–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_335 : rowsJ2 105 106 0 53 ≤ 439112959090043 := by decide +kernel

theorem rows22475R_336 : rowsJ2 105 106 53 59 ≤ 15841533246687 := by decide +kernel

theorem rows22475R_337 : rowsJ2 105 106 59 65 ≤ 1689884958355 := by decide +kernel

theorem rows22475R_338 : rowsJ2 105 106 65 73 ≤ 1770067300787 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_335
#print axioms SieveCert.rows22475R_338
