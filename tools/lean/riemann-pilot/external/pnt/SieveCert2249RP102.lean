/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 389–391 of 503

File 102 of 127: the parts `rows2249R_389` … `rows2249R_391` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22877 tests: row 122 columns 0–47, row 122 columns 48–56, row 122 columns
57–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_389 : rowsJ2 122 123 0 48 ≤ 164901208033900 := by decide +kernel

theorem rows2249R_390 : rowsJ2 122 123 48 57 ≤ 49687599848979 := by decide +kernel

theorem rows2249R_391 : rowsJ2 122 123 57 300 ≤ 671729385868402 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_389
#print axioms SieveCert.rows2249R_391
