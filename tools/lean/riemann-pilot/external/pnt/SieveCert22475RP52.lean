/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 202–204 of 534

File 52 of 135: the parts `rows22475R_202` … `rows22475R_204` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 22885 tests: row 84 columns 0–35, row 84 columns 36–61, row 84 columns
62–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_202 : rowsJ2 84 85 0 36 ≤ 550598338825331 := by decide +kernel

theorem rows22475R_203 : rowsJ2 84 85 36 62 ≤ 517053998936643 := by decide +kernel

theorem rows22475R_204 : rowsJ2 84 85 62 68 ≤ 1857302490356 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_202
#print axioms SieveCert.rows22475R_204
