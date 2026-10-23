/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 239–242 of 534

File 62 of 135: the parts `rows22475R_239` … `rows22475R_242` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29633 tests: row 89 columns 62–66, row 89 columns 67–71, row 89 columns
72–77, row 89 columns 78–84), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_239 : rowsJ2 89 90 62 67 ≤ 511995670225 := by decide +kernel

theorem rows22475R_240 : rowsJ2 89 90 67 72 ≤ 502009230336 := by decide +kernel

theorem rows22475R_241 : rowsJ2 89 90 72 78 ≤ 2630873898882 := by decide +kernel

theorem rows22475R_242 : rowsJ2 89 90 78 85 ≤ 32677908932621 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_239
#print axioms SieveCert.rows22475R_242
