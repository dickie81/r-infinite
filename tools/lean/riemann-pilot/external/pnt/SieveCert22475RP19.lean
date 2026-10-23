/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 75–78 of 534

File 19 of 135: the parts `rows22475R_75` … `rows22475R_78` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26446 tests: row 57 columns 0–34, row 57 columns 35–43, row 57 columns 44–51,
row 57 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_75 : rowsJ2 57 58 0 35 ≤ 1286840788306697 := by decide +kernel

theorem rows22475R_76 : rowsJ2 57 58 35 44 ≤ 369164656340119 := by decide +kernel

theorem rows22475R_77 : rowsJ2 57 58 44 52 ≤ 554648125822559 := by decide +kernel

theorem rows22475R_78 : rowsJ2 57 58 52 300 ≤ 345596864004898 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_75
#print axioms SieveCert.rows22475R_78
