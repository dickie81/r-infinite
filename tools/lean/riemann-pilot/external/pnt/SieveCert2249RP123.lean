/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 482–485 of 503

File 123 of 127: the parts `rows2249R_482` … `rows2249R_485` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28209 tests: rows 181–184, rows 185–188, rows 189–192, rows 193–196), each a
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

theorem rows2249R_482 : rows2 181 185 ≤ 26317008018249441 := by decide +kernel

theorem rows2249R_483 : rows2 185 189 ≤ 27900754587198382 := by decide +kernel

theorem rows2249R_484 : rows2 189 193 ≤ 29181332347512890 := by decide +kernel

theorem rows2249R_485 : rows2 193 197 ≤ 30692419390907211 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_482
#print axioms SieveCert.rows2249R_485
