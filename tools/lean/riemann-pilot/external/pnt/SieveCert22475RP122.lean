/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 472–476 of 534

File 122 of 135: the parts `rows22475R_472` … `rows22475R_476` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (5 parts, 29708 tests: row 143 columns 42–299, row 144 columns 0–41, row 144 columns
42–299, row 145 columns 0–40, row 145 columns 41–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_472 : rowsJ2 143 144 42 300 ≤ 2503070275382163 := by decide +kernel

theorem rows22475R_473 : rowsJ2 144 145 0 42 ≤ 147852536176022 := by decide +kernel

theorem rows22475R_474 : rowsJ2 144 145 42 300 ≤ 2499268160725212 := by decide +kernel

theorem rows22475R_475 : rowsJ2 145 146 0 41 ≤ 143718971517566 := by decide +kernel

theorem rows22475R_476 : rowsJ2 145 146 41 300 ≤ 2518192346611023 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_472
#print axioms SieveCert.rows22475R_476
