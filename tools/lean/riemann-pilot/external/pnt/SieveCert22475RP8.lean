/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 31–35 of 534

File 8 of 135: the parts `rows22475R_31` … `rows22475R_35` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (5 parts, 25741 tests: row 44 columns 35–43, row 44 columns 44–299, row 45 columns
0–34, row 45 columns 35–43, row 45 columns 44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22475R_31 : rowsJ2 44 45 35 44 ≤ 455605530503667 := by decide +kernel

theorem rows22475R_32 : rowsJ2 44 45 44 300 ≤ 55820857269539 := by decide +kernel

theorem rows22475R_33 : rowsJ2 45 46 0 35 ≤ 2171589028356869 := by decide +kernel

theorem rows22475R_34 : rowsJ2 45 46 35 44 ≤ 433421845310564 := by decide +kernel

theorem rows22475R_35 : rowsJ2 45 46 44 300 ≤ 114441786157273 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_31
#print axioms SieveCert.rows22475R_35
