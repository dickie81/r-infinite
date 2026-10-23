/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 183–186 of 534

File 47 of 135: the parts `rows22475R_183` … `rows22475R_186` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28990 tests: row 81 columns 0–34, row 81 columns 35–60, row 81 columns 61–67,
row 81 columns 68–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22475R_183 : rowsJ2 81 82 0 35 ≤ 509334355720850 := by decide +kernel

theorem rows22475R_184 : rowsJ2 81 82 35 61 ≤ 696946377066663 := by decide +kernel

theorem rows22475R_185 : rowsJ2 81 82 61 68 ≤ 11623094088452 := by decide +kernel

theorem rows22475R_186 : rowsJ2 81 82 68 72 ≤ 7210496552561 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_183
#print axioms SieveCert.rows22475R_186
