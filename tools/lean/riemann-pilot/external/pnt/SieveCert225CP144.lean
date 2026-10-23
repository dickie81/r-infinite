/-
# Round 625: the certificate at `L = 9/4`, parts 1172–1179 of 1374

File 144 of 167: the parts `rows225C_1172` … `rows225C_1179` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54034 depth-4 tests: row 167 columns 60–64, row 167 columns 65–69, row 167
columns 70–75, row 167 columns 76–83, row 167 columns 84–399, row 168 columns 0–53, row 168 columns 54–59, row 168
columns 60–64), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1172 : rowsJ 167 168 60 65 ≤ 25186102209140 := by decide +kernel

theorem rows225C_1173 : rowsJ 167 168 65 70 ≤ 13292063916622 := by decide +kernel

theorem rows225C_1174 : rowsJ 167 168 70 76 ≤ 5446889009115 := by decide +kernel

theorem rows225C_1175 : rowsJ 167 168 76 84 ≤ 456549936576 := by decide +kernel

theorem rows225C_1176 : rowsJ 167 168 84 400 ≤ 953161201656203 := by decide +kernel

theorem rows225C_1177 : rowsJ 168 169 0 54 ≤ 48615006775545 := by decide +kernel

theorem rows225C_1178 : rowsJ 168 169 54 60 ≤ 25991640525057 := by decide +kernel

theorem rows225C_1179 : rowsJ 168 169 60 65 ≤ 24642140900246 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1172
#print axioms SieveCert.rows225C_1179
