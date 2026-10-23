/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 486–492 of 534

File 125 of 135: the parts `rows22475R_486` … `rows22475R_492` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (7 parts, 29278 tests: row 150 columns 41–299, row 151 columns 0–40, row 151 columns
41–299, row 152 columns 0–40, row 152 columns 41–299, row 153 columns 0–84, row 153 columns 85–299), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_486 : rowsJ2 150 151 41 300 ≤ 2552125826174358 := by decide +kernel

theorem rows22475R_487 : rowsJ2 151 152 0 41 ≤ 190414070049673 := by decide +kernel

theorem rows22475R_488 : rowsJ2 151 152 41 300 ≤ 2563104114614143 := by decide +kernel

theorem rows22475R_489 : rowsJ2 152 153 0 41 ≤ 197806503872045 := by decide +kernel

theorem rows22475R_490 : rowsJ2 152 153 41 300 ≤ 2576177211110473 := by decide +kernel

theorem rows22475R_491 : rowsJ2 153 154 0 85 ≤ 204352486222989 := by decide +kernel

theorem rows22475R_492 : rowsJ2 153 154 85 300 ≤ 2591443517831346 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_486
#print axioms SieveCert.rows22475R_492
