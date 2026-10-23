/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 136–138 of 503

File 36 of 127: the parts `rows2249R_136` … `rows2249R_138` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 23493 tests: row 73 columns 69–299, row 74 columns 0–34, row 74 columns 35–59),
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

theorem rows2249R_136 : rowsJ2 73 74 69 300 ≤ 20882448883795 := by decide +kernel

theorem rows2249R_137 : rowsJ2 74 75 0 35 ≤ 499893428731881 := by decide +kernel

theorem rows2249R_138 : rowsJ2 74 75 35 60 ≤ 838589640785691 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_136
#print axioms SieveCert.rows2249R_138
