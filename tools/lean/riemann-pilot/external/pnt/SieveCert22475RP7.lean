/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 28–30 of 534

File 7 of 135: the parts `rows22475R_28` … `rows22475R_30` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 22950 tests: row 43 columns 0–34, row 43 columns 35–299, row 44 columns
0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_28 : rowsJ2 43 44 0 35 ≤ 2328858350829390 := by decide +kernel

theorem rows22475R_29 : rowsJ2 43 44 35 300 ≤ 479998291153372 := by decide +kernel

theorem rows22475R_30 : rowsJ2 44 45 0 35 ≤ 2250006760818168 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_28
#print axioms SieveCert.rows22475R_30
