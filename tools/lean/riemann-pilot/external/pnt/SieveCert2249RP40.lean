/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 150–153 of 503

File 40 of 127: the parts `rows2249R_150` … `rows2249R_153` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27642 tests: row 76 columns 69–73, row 76 columns 74–299, row 77 columns 0–34,
row 77 columns 35–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_150 : rowsJ2 76 77 69 74 ≤ 15090973527872 := by decide +kernel

theorem rows2249R_151 : rowsJ2 76 77 74 300 ≤ 7430992488290 := by decide +kernel

theorem rows2249R_152 : rowsJ2 77 78 0 35 ≤ 490350553870899 := by decide +kernel

theorem rows2249R_153 : rowsJ2 77 78 35 61 ≤ 712647861414596 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_150
#print axioms SieveCert.rows2249R_153
