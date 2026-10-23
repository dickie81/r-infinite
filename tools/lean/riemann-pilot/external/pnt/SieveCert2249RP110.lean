/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 422–425 of 503

File 110 of 127: the parts `rows2249R_422` … `rows2249R_425` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24013 tests: row 133 columns 0–43, row 133 columns 44–56, row 133 columns
57–299, row 134 columns 0–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_422 : rowsJ2 133 134 0 44 ≤ 115490240992490 := by decide +kernel

theorem rows2249R_423 : rowsJ2 133 134 44 57 ≤ 47056925560202 := by decide +kernel

theorem rows2249R_424 : rowsJ2 133 134 57 300 ≤ 2347431521241270 := by decide +kernel

theorem rows2249R_425 : rowsJ2 134 135 0 44 ≤ 116737371964880 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_422
#print axioms SieveCert.rows2249R_425
