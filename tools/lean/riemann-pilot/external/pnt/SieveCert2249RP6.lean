/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 24–27 of 503

File 6 of 127: the parts `rows2249R_24` … `rows2249R_27` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27434 tests: row 41 columns 0–34, row 41 columns 35–299, row 42 columns 0–34,
row 42 columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_24 : rowsJ2 41 42 0 35 ≤ 2153281610656756 := by decide +kernel

theorem rows2249R_25 : rowsJ2 41 42 35 300 ≤ 338498407044153 := by decide +kernel

theorem rows2249R_26 : rowsJ2 42 43 0 35 ≤ 2077415278140167 := by decide +kernel

theorem rows2249R_27 : rowsJ2 42 43 35 300 ≤ 367138075761177 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_24
#print axioms SieveCert.rows2249R_27
