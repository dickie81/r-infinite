/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 493–496 of 534

File 126 of 135: the parts `rows22475R_493` … `rows22475R_496` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 23898 tests: row 154 columns 0–93, row 154 columns 94–299, rows 155–155, rows
156–156), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_493 : rowsJ2 154 155 0 94 ≤ 1215518959315780 := by decide +kernel

theorem rows22475R_494 : rowsJ2 154 155 94 300 ≤ 1604563511629705 := by decide +kernel

theorem rows22475R_495 : rows2 155 156 ≤ 2845448946103984 := by decide +kernel

theorem rows22475R_496 : rows2 156 157 ≤ 2940782478124234 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_493
#print axioms SieveCert.rows22475R_496
