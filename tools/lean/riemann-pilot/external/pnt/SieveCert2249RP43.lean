/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 161–164 of 503

File 43 of 127: the parts `rows2249R_161` … `rows2249R_164` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29243 tests: row 78 columns 74–299, row 79 columns 0–34, row 79 columns 35–61,
row 79 columns 62–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_161 : rowsJ2 78 79 74 300 ≤ 7033892957640 := by decide +kernel

theorem rows2249R_162 : rowsJ2 79 80 0 35 ≤ 485842142607126 := by decide +kernel

theorem rows2249R_163 : rowsJ2 79 80 35 62 ≤ 626808887739659 := by decide +kernel

theorem rows2249R_164 : rowsJ2 79 80 62 68 ≤ 5298303207410 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_161
#print axioms SieveCert.rows2249R_164
