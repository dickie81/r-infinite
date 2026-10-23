/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 28–30 of 503

File 7 of 127: the parts `rows2249R_28` … `rows2249R_30` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22950 tests: row 43 columns 0–34, row 43 columns 35–299, row 44 columns 0–34),
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

theorem rows2249R_28 : rowsJ2 43 44 0 35 ≤ 2001649621268448 := by decide +kernel

theorem rows2249R_29 : rowsJ2 43 44 35 300 ≤ 399103403751106 := by decide +kernel

theorem rows2249R_30 : rowsJ2 44 45 0 35 ≤ 1926723617035296 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_28
#print axioms SieveCert.rows2249R_30
