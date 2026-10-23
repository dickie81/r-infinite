/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 138–141 of 534

File 35 of 135: the parts `rows22475R_138` … `rows22475R_141` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29817 tests: row 72 columns 68–299, row 73 columns 0–34, row 73 columns
35–49, row 73 columns 50–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_138 : rowsJ2 72 73 68 300 ≤ 35451185384504 := by decide +kernel

theorem rows22475R_139 : rowsJ2 73 74 0 35 ≤ 569234202807582 := by decide +kernel

theorem rows22475R_140 : rowsJ2 73 74 35 50 ≤ 765469374651800 := by decide +kernel

theorem rows22475R_141 : rowsJ2 73 74 50 68 ≤ 369475783973029 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_138
#print axioms SieveCert.rows22475R_141
