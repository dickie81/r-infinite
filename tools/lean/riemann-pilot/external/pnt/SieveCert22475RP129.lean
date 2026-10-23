/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 506–509 of 534

File 129 of 135: the parts `rows22475R_506` … `rows22475R_509` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25216 tests: rows 166–166, rows 167–168, rows 169–170, rows 171–172), each a
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

theorem rows22475R_506 : rows2 166 167 ≤ 4425128590411747 := by decide +kernel

theorem rows22475R_507 : rows2 167 169 ≤ 9239151023784888 := by decide +kernel

theorem rows22475R_508 : rows2 169 171 ≤ 9755070521830385 := by decide +kernel

theorem rows22475R_509 : rows2 171 173 ≤ 10282480285199498 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_506
#print axioms SieveCert.rows22475R_509
