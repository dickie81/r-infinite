/-
# Round 625: the certificate at `L = 9/4`, parts 1180–1187 of 1374

File 145 of 167: the parts `rows225C_1180` … `rows225C_1187` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 59255 depth-4 tests: row 168 columns 65–70, row 168 columns 71–77, row 168
columns 78–399, row 169 columns 0–53, row 169 columns 54–58, row 169 columns 59–63, row 169 columns 64–69, row 169
columns 70–76), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1180 : rowsJ 168 169 65 71 ≤ 13829856363726 := by decide +kernel

theorem rows225C_1181 : rowsJ 168 169 71 78 ≤ 3689229650500 := by decide +kernel

theorem rows225C_1182 : rowsJ 168 169 78 400 ≤ 1049657078751925 := by decide +kernel

theorem rows225C_1183 : rowsJ 169 170 0 54 ≤ 47336230708360 := by decide +kernel

theorem rows225C_1184 : rowsJ 169 170 54 59 ≤ 21931947758176 := by decide +kernel

theorem rows225C_1185 : rowsJ 169 170 59 64 ≤ 25876491550797 := by decide +kernel

theorem rows225C_1186 : rowsJ 169 170 64 70 ≤ 15235674674490 := by decide +kernel

theorem rows225C_1187 : rowsJ 169 170 70 77 ≤ 4403358940380 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1180
#print axioms SieveCert.rows225C_1187
