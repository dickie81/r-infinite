/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 235–238 of 534

File 61 of 135: the parts `rows22475R_235` … `rows22475R_238` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26082 tests: row 88 columns 78–84, row 88 columns 85–299, row 89 columns
0–39, row 89 columns 40–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_235 : rowsJ2 88 89 78 85 ≤ 29495361896173 := by decide +kernel

theorem rows22475R_236 : rowsJ2 88 89 85 300 ≤ 216939695147375 := by decide +kernel

theorem rows22475R_237 : rowsJ2 89 90 0 40 ≤ 654139091656218 := by decide +kernel

theorem rows22475R_238 : rowsJ2 89 90 40 62 ≤ 203604354133364 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_235
#print axioms SieveCert.rows22475R_238
