/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 161–164 of 534

File 41 of 135: the parts `rows22475R_161` … `rows22475R_164` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 23004 tests: row 77 columns 59–67, row 77 columns 68–72, row 77 columns
73–76, row 77 columns 77–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_161 : rowsJ2 77 78 59 68 ≤ 63118940792433 := by decide +kernel

theorem rows22475R_162 : rowsJ2 77 78 68 73 ≤ 14387999039288 := by decide +kernel

theorem rows22475R_163 : rowsJ2 77 78 73 77 ≤ 12459392187728 := by decide +kernel

theorem rows22475R_164 : rowsJ2 77 78 77 300 ≤ 2519178409035 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_161
#print axioms SieveCert.rows22475R_164
