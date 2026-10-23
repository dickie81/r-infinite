/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 408–412 of 503

File 107 of 127: the parts `rows2249R_408` … `rows2249R_412` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (5 parts, 29950 tests: row 128 columns 46–56, row 128 columns 57–299, row 129 columns
0–44, row 129 columns 45–55, row 129 columns 56–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_408 : rowsJ2 128 129 46 57 ≤ 47268446169886 := by decide +kernel

theorem rows2249R_409 : rowsJ2 128 129 57 300 ≤ 1683093890960624 := by decide +kernel

theorem rows2249R_410 : rowsJ2 129 130 0 45 ≤ 121378920114756 := by decide +kernel

theorem rows2249R_411 : rowsJ2 129 130 45 56 ≤ 53540729418708 := by decide +kernel

theorem rows2249R_412 : rowsJ2 129 130 56 300 ≤ 1838575116552971 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_408
#print axioms SieveCert.rows2249R_412
