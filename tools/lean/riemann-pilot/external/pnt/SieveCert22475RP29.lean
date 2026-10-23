/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 115–118 of 534

File 29 of 135: the parts `rows22475R_115` … `rows22475R_118` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24864 tests: row 67 columns 0–34, row 67 columns 35–44, row 67 columns 45–64,
row 67 columns 65–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_115 : rowsJ2 67 68 0 35 ≤ 742079433523646 := by decide +kernel

theorem rows22475R_116 : rowsJ2 67 68 35 45 ≤ 561306033906654 := by decide +kernel

theorem rows22475R_117 : rowsJ2 67 68 45 65 ≤ 777046293595108 := by decide +kernel

theorem rows22475R_118 : rowsJ2 67 68 65 300 ≤ 53573071267761 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_115
#print axioms SieveCert.rows22475R_118
