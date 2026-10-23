/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 510–513 of 534

File 130 of 135: the parts `rows22475R_510` … `rows22475R_513` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29834 tests: rows 173–175, rows 176–178, rows 179–182, rows 183–186), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_510 : rows2 173 176 ≤ 16453498034575916 := by decide +kernel

theorem rows22475R_511 : rows2 176 179 ≤ 17741136566751118 := by decide +kernel

theorem rows22475R_512 : rows2 179 183 ≤ 25760559606013029 := by decide +kernel

theorem rows22475R_513 : rows2 183 187 ≤ 28088680303374081 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_510
#print axioms SieveCert.rows22475R_513
