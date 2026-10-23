/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 216–219 of 534

File 56 of 135: the parts `rows22475R_216` … `rows22475R_219` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29376 tests: row 86 columns 0–36, row 86 columns 37–61, row 86 columns 62–66,
row 86 columns 67–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_216 : rowsJ2 86 87 0 37 ≤ 583266212182133 := by decide +kernel

theorem rows22475R_217 : rowsJ2 86 87 37 62 ≤ 395389770823056 := by decide +kernel

theorem rows22475R_218 : rowsJ2 86 87 62 67 ≤ 706668866731 := by decide +kernel

theorem rows22475R_219 : rowsJ2 86 87 67 72 ≤ 2909244301289 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_216
#print axioms SieveCert.rows22475R_219
