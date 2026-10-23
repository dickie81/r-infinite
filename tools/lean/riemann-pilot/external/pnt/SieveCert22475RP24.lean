/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 95–98 of 534

File 24 of 135: the parts `rows22475R_95` … `rows22475R_98` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25410 tests: row 62 columns 0–34, row 62 columns 35–43, row 62 columns 44–55,
row 62 columns 56–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_95 : rowsJ2 62 63 0 35 ≤ 981215489807805 := by decide +kernel

theorem rows22475R_96 : rowsJ2 62 63 35 44 ≤ 443865100528620 := by decide +kernel

theorem rows22475R_97 : rowsJ2 62 63 44 56 ≤ 692965219821127 := by decide +kernel

theorem rows22475R_98 : rowsJ2 62 63 56 300 ≤ 277063704005111 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_95
#print axioms SieveCert.rows22475R_98
