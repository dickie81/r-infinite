/-
# Round 625: the certificate at `L = 9/4`, parts 1164–1171 of 1374

File 143 of 167: the parts `rows225C_1164` … `rows225C_1171` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 53967 depth-4 tests: row 166 columns 55–59, row 166 columns 60–64, row 166
columns 65–69, row 166 columns 70–75, row 166 columns 76–83, row 166 columns 84–399, row 167 columns 0–54, row 167
columns 55–59), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_1164 : rowsJ 166 167 55 60 ≤ 19866176572452 := by decide +kernel

theorem rows225C_1165 : rowsJ 166 167 60 65 ≤ 25711452489442 := by decide +kernel

theorem rows225C_1166 : rowsJ 166 167 65 70 ≤ 14134008196426 := by decide +kernel

theorem rows225C_1167 : rowsJ 166 167 70 76 ≤ 6061746983391 := by decide +kernel

theorem rows225C_1168 : rowsJ 166 167 76 84 ≤ 600771139564 := by decide +kernel

theorem rows225C_1169 : rowsJ 166 167 84 400 ≤ 850639860408026 := by decide +kernel

theorem rows225C_1170 : rowsJ 167 168 0 55 ≤ 53770128595347 := by decide +kernel

theorem rows225C_1171 : rowsJ 167 168 55 60 ≤ 21339684251269 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1164
#print axioms SieveCert.rows225C_1171
