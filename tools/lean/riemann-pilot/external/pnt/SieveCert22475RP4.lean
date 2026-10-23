/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 14–19 of 534

File 4 of 135: the parts `rows22475R_14` … `rows22475R_19` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (6 parts, 29679 tests: row 36 columns 0–34, row 36 columns 35–299, row 37 columns 0–34,
row 37 columns 35–299, row 38 columns 0–34, row 38 columns 35–299), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_14 : rowsJ2 36 37 0 35 ≤ 2880189190195769 := by decide +kernel

theorem rows22475R_15 : rowsJ2 36 37 35 300 ≤ 188665621984508 := by decide +kernel

theorem rows22475R_16 : rowsJ2 37 38 0 35 ≤ 2802072834234413 := by decide +kernel

theorem rows22475R_17 : rowsJ2 37 38 35 300 ≤ 257164295208035 := by decide +kernel

theorem rows22475R_18 : rowsJ2 38 39 0 35 ≤ 2723532475828743 := by decide +kernel

theorem rows22475R_19 : rowsJ2 38 39 35 300 ≤ 312243202110485 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_14
#print axioms SieveCert.rows22475R_19
