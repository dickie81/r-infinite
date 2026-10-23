/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 444–447 of 534

File 115 of 135: the parts `rows22475R_444` … `rows22475R_447` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26527 tests: row 132 columns 0–44, row 132 columns 45–54, row 132 columns
55–299, row 133 columns 0–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_444 : rowsJ2 132 133 0 45 ≤ 135716006211479 := by decide +kernel

theorem rows22475R_445 : rowsJ2 132 133 45 55 ≤ 60685615362513 := by decide +kernel

theorem rows22475R_446 : rowsJ2 132 133 55 300 ≤ 2314830584924077 := by decide +kernel

theorem rows22475R_447 : rowsJ2 133 134 0 45 ≤ 135965216999614 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_444
#print axioms SieveCert.rows22475R_447
