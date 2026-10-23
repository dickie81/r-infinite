/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 9–13 of 534

File 3 of 135: the parts `rows22475R_9` … `rows22475R_13` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (5 parts, 29891 tests: rows 32–32, rows 33–33, rows 34–34, row 35 columns 0–34, row 35
columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_9 : rows2 32 33 ≤ 2916889486893183 := by decide +kernel

theorem rows22475R_10 : rows2 33 34 ≤ 2987440979278841 := by decide +kernel

theorem rows22475R_11 : rows2 34 35 ≤ 3035196108295978 := by decide +kernel

theorem rows22475R_12 : rowsJ2 35 36 0 35 ≤ 2958005793398881 := by decide +kernel

theorem rows22475R_13 : rowsJ2 35 36 35 300 ≤ 103801302766624 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_9
#print axioms SieveCert.rows22475R_13
