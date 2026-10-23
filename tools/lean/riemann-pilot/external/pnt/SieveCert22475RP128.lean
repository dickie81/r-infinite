/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 501–505 of 534

File 128 of 135: the parts `rows22475R_501` … `rows22475R_505` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (5 parts, 26310 tests: rows 161–161, rows 162–162, rows 163–163, rows 164–164, rows
165–165), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_501 : rows2 161 162 ≤ 3719239468286577 := by decide +kernel

theorem rows22475R_502 : rows2 162 163 ≤ 3867349023564853 := by decide +kernel

theorem rows22475R_503 : rows2 163 164 ≤ 4011164085857891 := by decide +kernel

theorem rows22475R_504 : rows2 164 165 ≤ 4153026173135827 := by decide +kernel

theorem rows22475R_505 : rows2 165 166 ≤ 4290066720899324 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_501
#print axioms SieveCert.rows22475R_505
