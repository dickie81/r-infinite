/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 44–47 of 534

File 11 of 135: the parts `rows22475R_44` … `rows22475R_47` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27695 tests: row 48 columns 44–299, row 49 columns 0–34, row 49 columns
35–43, row 49 columns 44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_44 : rowsJ2 48 49 44 300 ≤ 330662487202243 := by decide +kernel

theorem rows22475R_45 : rowsJ2 49 50 0 35 ≤ 1861835308241234 := by decide +kernel

theorem rows22475R_46 : rowsJ2 49 50 35 44 ≤ 370361490793237 := by decide +kernel

theorem rows22475R_47 : rowsJ2 49 50 44 300 ≤ 418731712107913 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_44
#print axioms SieveCert.rows22475R_47
