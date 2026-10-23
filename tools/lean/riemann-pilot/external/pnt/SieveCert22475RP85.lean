/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 328–330 of 534

File 85 of 135: the parts `rows22475R_328` … `rows22475R_330` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 22235 tests: row 103 columns 66–72, row 103 columns 73–299, row 104 columns
0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_328 : rowsJ2 103 104 66 73 ≤ 1444401956148 := by decide +kernel

theorem rows22475R_329 : rowsJ2 103 104 73 300 ≤ 1182659109388418 := by decide +kernel

theorem rows22475R_330 : rowsJ2 104 105 0 53 ≤ 458595539900065 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_328
#print axioms SieveCert.rows22475R_330
