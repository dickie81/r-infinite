/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 185–188 of 503

File 49 of 127: the parts `rows2249R_185` … `rows2249R_188` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28656 tests: row 82 columns 78–299, row 83 columns 0–36, row 83 columns 37–62,
row 83 columns 63–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_185 : rowsJ2 82 83 78 300 ≤ 7156117631491 := by decide +kernel

theorem rows2249R_186 : rowsJ2 83 84 0 37 ≤ 558302208378827 := by decide +kernel

theorem rows2249R_187 : rowsJ2 83 84 37 63 ≤ 377888828930080 := by decide +kernel

theorem rows2249R_188 : rowsJ2 83 84 63 68 ≤ 2324366129281 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_185
#print axioms SieveCert.rows2249R_188
