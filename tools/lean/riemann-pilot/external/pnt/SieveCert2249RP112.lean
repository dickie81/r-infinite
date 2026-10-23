/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 430–433 of 503

File 112 of 127: the parts `rows2249R_430` … `rows2249R_433` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29139 tests: row 136 columns 0–42, row 136 columns 43–299, row 137 columns
0–42, row 137 columns 43–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_430 : rowsJ2 136 137 0 43 ≤ 112777104987637 := by decide +kernel

theorem rows2249R_431 : rowsJ2 136 137 43 300 ≤ 2385939309594974 := by decide +kernel

theorem rows2249R_432 : rowsJ2 137 138 0 43 ≤ 117985037779556 := by decide +kernel

theorem rows2249R_433 : rowsJ2 137 138 43 300 ≤ 2384368918653471 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_430
#print axioms SieveCert.rows2249R_433
