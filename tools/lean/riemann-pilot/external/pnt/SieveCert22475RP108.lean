/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 416–419 of 534

File 108 of 135: the parts `rows22475R_416` … `rows22475R_419` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24653 tests: row 123 columns 56–67, row 123 columns 68–299, row 124 columns
0–47, row 124 columns 48–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_416 : rowsJ2 123 124 56 68 ≤ 9551851684758 := by decide +kernel

theorem rows22475R_417 : rowsJ2 123 124 68 300 ≤ 863396778785827 := by decide +kernel

theorem rows22475R_418 : rowsJ2 124 125 0 48 ≤ 185219285547750 := by decide +kernel

theorem rows22475R_419 : rowsJ2 124 125 48 56 ≤ 58215510382095 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_416
#print axioms SieveCert.rows22475R_419
