/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 35–38 of 117

File 9 of 27: the parts `rows225R_35` … `rows225R_38` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 25510 tests: row 52 columns 0–45, row 52 columns 46–199, row 53 columns 0–45, row
53 columns 46–199), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_35 : rowsJ2 52 53 0 46 ≤ 1875216630400165 := by decide +kernel

theorem rows225R_36 : rowsJ2 52 53 46 200 ≤ 38855286432226 := by decide +kernel

theorem rows225R_37 : rowsJ2 53 54 0 46 ≤ 1759188005194375 := by decide +kernel

theorem rows225R_38 : rowsJ2 53 54 46 200 ≤ 34538979761757 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_35
#print axioms SieveCert.rows225R_38
