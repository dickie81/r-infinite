/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 334–337 of 503

File 88 of 127: the parts `rows2249R_334` … `rows2249R_337` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 22833 tests: row 108 columns 67–81, row 108 columns 82–299, row 109 columns
0–50, row 109 columns 51–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_334 : rowsJ2 108 109 67 82 ≤ 468662438825894 := by decide +kernel

theorem rows2249R_335 : rowsJ2 108 109 82 300 ≤ 206402927820222 := by decide +kernel

theorem rows2249R_336 : rowsJ2 109 110 0 51 ≤ 300600091475915 := by decide +kernel

theorem rows2249R_337 : rowsJ2 109 110 51 58 ≤ 31814406288336 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_334
#print axioms SieveCert.rows2249R_337
