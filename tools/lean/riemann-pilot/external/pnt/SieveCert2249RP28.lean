/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 107–109 of 503

File 28 of 127: the parts `rows2249R_107` … `rows2249R_109` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22909 tests: row 66 columns 0–34, row 66 columns 35–45, row 66 columns 46–299),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_107 : rowsJ2 66 67 0 35 ≤ 637782872655850 := by decide +kernel

theorem rows2249R_108 : rowsJ2 66 67 35 46 ≤ 600631538824626 := by decide +kernel

theorem rows2249R_109 : rowsJ2 66 67 46 300 ≤ 653630927104382 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_107
#print axioms SieveCert.rows2249R_109
