/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 468–472 of 503

File 120 of 127: the parts `rows2249R_468` … `rows2249R_472` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (5 parts, 28518 tests: rows 157–157, rows 158–158, rows 159–159, rows 160–160, rows
161–161), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows2249R_468 : rows2 157 158 ≤ 2949653789705563 := by decide +kernel

theorem rows2249R_469 : rows2 158 159 ≤ 3105177159611773 := by decide +kernel

theorem rows2249R_470 : rows2 159 160 ≤ 3260008481280293 := by decide +kernel

theorem rows2249R_471 : rows2 160 161 ≤ 3410187016530830 := by decide +kernel

theorem rows2249R_472 : rows2 161 162 ≤ 3559428425988450 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_468
#print axioms SieveCert.rows2249R_472
