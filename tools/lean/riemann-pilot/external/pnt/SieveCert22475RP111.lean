/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 428–431 of 534

File 111 of 135: the parts `rows22475R_428` … `rows22475R_431` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28801 tests: row 126 columns 56–299, row 127 columns 0–46, row 127 columns
47–55, row 127 columns 56–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_428 : rowsJ2 126 127 56 300 ≤ 1401323319910481 := by decide +kernel

theorem rows22475R_429 : rowsJ2 127 128 0 47 ≤ 163003153778352 := by decide +kernel

theorem rows22475R_430 : rowsJ2 127 128 47 56 ≤ 59022038176383 := by decide +kernel

theorem rows22475R_431 : rowsJ2 127 128 56 300 ≤ 1561504888194726 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_428
#print axioms SieveCert.rows22475R_431
