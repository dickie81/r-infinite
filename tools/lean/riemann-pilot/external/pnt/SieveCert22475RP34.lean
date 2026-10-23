/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 135–137 of 534

File 34 of 135: the parts `rows22475R_135` … `rows22475R_137` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 23291 tests: row 72 columns 0–34, row 72 columns 35–48, row 72 columns
49–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_135 : rowsJ2 72 73 0 35 ≤ 589210973226734 := by decide +kernel

theorem rows22475R_136 : rowsJ2 72 73 35 49 ≤ 743552494626367 := by decide +kernel

theorem rows22475R_137 : rowsJ2 72 73 49 68 ≤ 440440649166478 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_135
#print axioms SieveCert.rows22475R_137
