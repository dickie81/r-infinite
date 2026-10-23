/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 43–46 of 117

File 11 of 27: the parts `rows225R_43` … `rows225R_46` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 28827 tests: row 56 columns 0–45, row 56 columns 46–199, row 57 columns 0–45, row
57 columns 46–199), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
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

theorem rows225R_43 : rowsJ2 56 57 0 46 ≤ 1462925561398928 := by decide +kernel

theorem rows225R_44 : rowsJ2 56 57 46 200 ≤ 67876768755727 := by decide +kernel

theorem rows225R_45 : rowsJ2 57 58 0 46 ≤ 1369167641469056 := by decide +kernel

theorem rows225R_46 : rowsJ2 57 58 46 200 ≤ 101388684381222 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_43
#print axioms SieveCert.rows225R_46
