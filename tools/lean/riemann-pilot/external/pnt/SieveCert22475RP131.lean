/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 514–517 of 534

File 131 of 135: the parts `rows22475R_514` … `rows22475R_517` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27095 tests: rows 187–190, rows 191–194, rows 195–197, rows 198–200), each a
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

theorem rows22475R_514 : rows2 187 191 ≤ 29453872020956613 := by decide +kernel

theorem rows22475R_515 : rows2 191 195 ≤ 30922031251146796 := by decide +kernel

theorem rows22475R_516 : rows2 195 198 ≤ 24303565107286565 := by decide +kernel

theorem rows22475R_517 : rows2 198 201 ≤ 25284114685677987 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_514
#print axioms SieveCert.rows22475R_517
