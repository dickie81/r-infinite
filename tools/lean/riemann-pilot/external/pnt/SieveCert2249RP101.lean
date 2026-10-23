/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 385–388 of 503

File 101 of 127: the parts `rows2249R_385` … `rows2249R_388` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 23565 tests: row 121 columns 0–47, row 121 columns 48–55, row 121 columns
56–68, row 121 columns 69–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_385 : rowsJ2 121 122 0 48 ≤ 169983213886526 := by decide +kernel

theorem rows2249R_386 : rowsJ2 121 122 48 56 ≤ 51293484067115 := by decide +kernel

theorem rows2249R_387 : rowsJ2 121 122 56 69 ≤ 6371424875910 := by decide +kernel

theorem rows2249R_388 : rowsJ2 121 122 69 300 ≤ 482374791167103 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_385
#print axioms SieveCert.rows2249R_388
