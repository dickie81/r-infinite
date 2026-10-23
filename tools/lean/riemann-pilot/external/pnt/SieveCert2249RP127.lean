/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 498–502 of 503

File 127 of 127: the parts `rows2249R_498` … `rows2249R_502` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (5 parts, 29178 tests: rows 237–286, rows 287–290, rows 291–294, rows 295–297, rows
298–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_498 : rows2 237 287 ≤ 43600993062232119 := by decide +kernel

theorem rows2249R_499 : rows2 287 291 ≤ 50169760312711228 := by decide +kernel

theorem rows2249R_500 : rows2 291 295 ≤ 53839439217421140 := by decide +kernel

theorem rows2249R_501 : rows2 295 298 ≤ 43051080651691740 := by decide +kernel

theorem rows2249R_502 : rows2 298 300 ≤ 30121889536853467 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_498
#print axioms SieveCert.rows2249R_502
