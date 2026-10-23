/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 111–114 of 534

File 28 of 135: the parts `rows22475R_111` … `rows22475R_114` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24531 tests: row 66 columns 0–34, row 66 columns 35–44, row 66 columns 45–63,
row 66 columns 64–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_111 : rowsJ2 66 67 0 35 ≤ 783370005811213 := by decide +kernel

theorem rows22475R_112 : rowsJ2 66 67 35 45 ≤ 555484632115599 := by decide +kernel

theorem rows22475R_113 : rowsJ2 66 67 45 64 ≤ 792017722584325 := by decide +kernel

theorem rows22475R_114 : rowsJ2 66 67 64 300 ≤ 62998648758241 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_111
#print axioms SieveCert.rows22475R_114
