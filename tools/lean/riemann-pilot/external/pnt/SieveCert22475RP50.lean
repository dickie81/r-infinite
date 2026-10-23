/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 196–198 of 534

File 50 of 135: the parts `rows22475R_196` … `rows22475R_198` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 22748 tests: row 83 columns 0–35, row 83 columns 36–61, row 83 columns
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

theorem rows22475R_196 : rowsJ2 83 84 0 36 ≤ 553125897429050 := by decide +kernel

theorem rows22475R_197 : rowsJ2 83 84 36 62 ≤ 560220403218257 := by decide +kernel

theorem rows22475R_198 : rowsJ2 83 84 62 68 ≤ 2793216511576 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_196
#print axioms SieveCert.rows22475R_198
