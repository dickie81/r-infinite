/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 497–500 of 534

File 127 of 135: the parts `rows22475R_497` … `rows22475R_500` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26895 tests: rows 157–157, rows 158–158, rows 159–159, rows 160–160), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_497 : rows2 157 158 ≤ 3101410780356648 := by decide +kernel

theorem rows22475R_498 : rows2 158 159 ≤ 3260348265385632 := by decide +kernel

theorem rows22475R_499 : rows2 159 160 ≤ 3415708234385464 := by decide +kernel

theorem rows22475R_500 : rows2 160 161 ≤ 3569456447098275 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_497
#print axioms SieveCert.rows22475R_500
