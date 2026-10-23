/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 172–174 of 534

File 44 of 135: the parts `rows22475R_172` … `rows22475R_174` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 22730 tests: row 79 columns 35–60, row 79 columns 61–67, row 79 columns
68–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_172 : rowsJ2 79 80 35 61 ≤ 789767804273605 := by decide +kernel

theorem rows22475R_173 : rowsJ2 79 80 61 68 ≤ 23551394597153 := by decide +kernel

theorem rows22475R_174 : rowsJ2 79 80 68 73 ≤ 11350315656317 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_172
#print axioms SieveCert.rows22475R_174
