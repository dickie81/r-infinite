/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 173–176 of 503

File 46 of 127: the parts `rows2249R_173` … `rows2249R_176` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 26135 tests: row 80 columns 78–299, row 81 columns 0–35, row 81 columns 36–61,
row 81 columns 62–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_173 : rowsJ2 80 81 78 300 ≤ 2396906852473 := by decide +kernel

theorem rows2249R_174 : rowsJ2 81 82 0 36 ≤ 526948422797070 := by decide +kernel

theorem rows2249R_175 : rowsJ2 81 82 36 62 ≤ 494760054773378 := by decide +kernel

theorem rows2249R_176 : rowsJ2 81 82 62 68 ≤ 2663334522314 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_173
#print axioms SieveCert.rows2249R_176
