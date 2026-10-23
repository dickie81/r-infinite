/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 473–477 of 503

File 121 of 127: the parts `rows2249R_473` … `rows2249R_477` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (5 parts, 27919 tests: rows 162–162, rows 163–163, rows 164–164, rows 165–166, rows
167–168), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows2249R_473 : rows2 162 163 ≤ 3703792664334152 := by decide +kernel

theorem rows2249R_474 : rows2 163 164 ≤ 3846865017115867 := by decide +kernel

theorem rows2249R_475 : rows2 164 165 ≤ 3984784698868832 := by decide +kernel

theorem rows2249R_476 : rows2 165 167 ≤ 8373535340936311 := by decide +kernel

theorem rows2249R_477 : rows2 167 169 ≤ 8894655424219731 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_473
#print axioms SieveCert.rows2249R_477
