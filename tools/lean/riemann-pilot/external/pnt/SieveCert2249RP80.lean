/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 304–307 of 503

File 80 of 127: the parts `rows2249R_304` … `rows2249R_307` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27888 tests: row 102 columns 67–74, row 102 columns 75–299, row 103 columns
0–52, row 103 columns 53–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_304 : rowsJ2 102 103 67 75 ≤ 5743059144036 := by decide +kernel

theorem rows2249R_305 : rowsJ2 102 103 75 300 ≤ 1048779560492768 := by decide +kernel

theorem rows2249R_306 : rowsJ2 103 104 0 53 ≤ 397664167005372 := by decide +kernel

theorem rows2249R_307 : rowsJ2 103 104 53 60 ≤ 7178076300898 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_304
#print axioms SieveCert.rows2249R_307
