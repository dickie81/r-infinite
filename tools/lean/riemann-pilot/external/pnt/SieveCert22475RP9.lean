/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 36–39 of 534

File 9 of 135: the parts `rows22475R_36` … `rows22475R_39` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26194 tests: row 46 columns 0–34, row 46 columns 35–43, row 46 columns
44–299, row 47 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_36 : rowsJ2 46 47 0 35 ≤ 2093209297102824 := by decide +kernel

theorem rows22475R_37 : rowsJ2 46 47 35 44 ≤ 414026548681453 := by decide +kernel

theorem rows22475R_38 : rowsJ2 46 47 44 300 ≤ 177968039771773 := by decide +kernel

theorem rows22475R_39 : rowsJ2 47 48 0 35 ≤ 2015635340544131 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_36
#print axioms SieveCert.rows22475R_39
