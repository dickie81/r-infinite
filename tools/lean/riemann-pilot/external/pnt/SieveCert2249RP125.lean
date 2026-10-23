/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 490–493 of 503

File 125 of 127: the parts `rows2249R_490` … `rows2249R_493` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27379 tests: rows 210–212, rows 213–215, rows 216–218, rows 219–221), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows2249R_490 : rows2 210 213 ≤ 29113228823808895 := by decide +kernel

theorem rows2249R_491 : rows2 213 216 ≤ 29932005532275535 := by decide +kernel

theorem rows2249R_492 : rows2 216 219 ≤ 30055684867087826 := by decide +kernel

theorem rows2249R_493 : rows2 219 222 ≤ 30404866481252302 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_490
#print axioms SieveCert.rows2249R_493
