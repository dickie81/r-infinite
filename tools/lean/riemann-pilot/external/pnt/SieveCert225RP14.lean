/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 55–58 of 117

File 14 of 27: the parts `rows225R_55` … `rows225R_58` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 26113 tests: row 62 columns 0–44, row 62 columns 45–199, row 63 columns 0–44, row
63 columns 45–199), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
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

theorem rows225R_55 : rowsJ2 62 63 0 45 ≤ 1007293894919061 := by decide +kernel

theorem rows225R_56 : rowsJ2 62 63 45 200 ≤ 2149953673493421 := by decide +kernel

theorem rows225R_57 : rowsJ2 63 64 0 45 ≤ 943400048510703 := by decide +kernel

theorem rows225R_58 : rowsJ2 63 64 45 200 ≤ 2365111715512198 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_55
#print axioms SieveCert.rows225R_58
