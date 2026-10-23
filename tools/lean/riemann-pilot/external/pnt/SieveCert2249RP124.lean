/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 486–489 of 503

File 124 of 127: the parts `rows2249R_486` … `rows2249R_489` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27482 tests: rows 197–200, rows 201–203, rows 204–206, rows 207–209), each a
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

theorem rows2249R_486 : rows2 197 201 ≤ 32385383980509868 := by decide +kernel

theorem rows2249R_487 : rows2 201 204 ≤ 25475989050769634 := by decide +kernel

theorem rows2249R_488 : rows2 204 207 ≤ 26621569237785891 := by decide +kernel

theorem rows2249R_489 : rows2 207 210 ≤ 27786878509879885 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_486
#print axioms SieveCert.rows2249R_489
