/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 48–50 of 534

File 12 of 135: the parts `rows22475R_48` … `rows22475R_50` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 23129 tests: row 50 columns 0–34, row 50 columns 35–43, row 50 columns
44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_48 : rowsJ2 50 51 0 35 ≤ 1785997283942698 := by decide +kernel

theorem rows22475R_49 : rowsJ2 50 51 35 44 ≤ 361083350372079 := by decide +kernel

theorem rows22475R_50 : rowsJ2 50 51 44 300 ≤ 501287401027466 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_48
#print axioms SieveCert.rows22475R_50
