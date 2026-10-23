/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 131–134 of 534

File 33 of 135: the parts `rows22475R_131` … `rows22475R_134` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28524 tests: row 71 columns 0–34, row 71 columns 35–47, row 71 columns 48–67,
row 71 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_131 : rowsJ2 71 72 0 35 ≤ 612790992711462 := by decide +kernel

theorem rows22475R_132 : rowsJ2 71 72 35 48 ≤ 710757397221817 := by decide +kernel

theorem rows22475R_133 : rowsJ2 71 72 48 68 ≤ 517979729250950 := by decide +kernel

theorem rows22475R_134 : rowsJ2 71 72 68 300 ≤ 33888481222142 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_131
#print axioms SieveCert.rows22475R_134
