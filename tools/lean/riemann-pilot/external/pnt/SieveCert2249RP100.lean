/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 381–384 of 503

File 100 of 127: the parts `rows2249R_381` … `rows2249R_384` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24216 tests: row 120 columns 0–47, row 120 columns 48–55, row 120 columns
56–67, row 120 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_381 : rowsJ2 120 121 0 48 ≤ 174110385637374 := by decide +kernel

theorem rows2249R_382 : rowsJ2 120 121 48 56 ≤ 53311911707477 := by decide +kernel

theorem rows2249R_383 : rowsJ2 120 121 56 68 ≤ 7522723958769 := by decide +kernel

theorem rows2249R_384 : rowsJ2 120 121 68 300 ≤ 293844779000778 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_381
#print axioms SieveCert.rows2249R_384
