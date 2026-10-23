/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 191–195 of 534

File 49 of 135: the parts `rows22475R_191` … `rows22475R_195` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (5 parts, 29924 tests: row 82 columns 61–67, row 82 columns 68–71, row 82 columns
72–76, row 82 columns 77–81, row 82 columns 82–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_191 : rowsJ2 82 83 61 68 ≤ 7578326263841 := by decide +kernel

theorem rows22475R_192 : rowsJ2 82 83 68 72 ≤ 6356147184107 := by decide +kernel

theorem rows22475R_193 : rowsJ2 82 83 72 77 ≤ 5151059318343 := by decide +kernel

theorem rows22475R_194 : rowsJ2 82 83 77 82 ≤ 5398826287715 := by decide +kernel

theorem rows22475R_195 : rowsJ2 82 83 82 300 ≤ 2377173311517 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_191
#print axioms SieveCert.rows22475R_195
