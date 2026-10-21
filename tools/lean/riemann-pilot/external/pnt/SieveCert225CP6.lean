/-
# Round 625: the certificate at `L = 9/4`, parts 47–55 of 1374

File 6 of 167: the parts `rows225C_47` … `rows225C_55` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 55150 depth-4 tests: row 49 columns 44–399, row 50 columns 0–34, row 50 columns
35–43, row 50 columns 44–49, row 50 columns 50–399, row 51 columns 0–34, row 51 columns 35–43, row 51 columns 44–49,
row 51 columns 50–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_47 : rowsJ 49 50 44 400 ≤ 185466159962697 := by decide +kernel

theorem rows225C_48 : rowsJ 50 51 0 35 ≤ 1063513724918928 := by decide +kernel

theorem rows225C_49 : rowsJ 50 51 35 44 ≤ 401584110457443 := by decide +kernel

theorem rows225C_50 : rowsJ 50 51 44 50 ≤ 174543842844862 := by decide +kernel

theorem rows225C_51 : rowsJ 50 51 50 400 ≤ 24575207466975 := by decide +kernel

theorem rows225C_52 : rowsJ 51 52 0 35 ≤ 1046845962780267 := by decide +kernel

theorem rows225C_53 : rowsJ 51 52 35 44 ≤ 381404027935833 := by decide +kernel

theorem rows225C_54 : rowsJ 51 52 44 50 ≤ 164115993979245 := by decide +kernel

theorem rows225C_55 : rowsJ 51 52 50 400 ≤ 45855934935256 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_47
#print axioms SieveCert.rows225C_55
