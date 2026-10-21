/-
# Round 625: the certificate at `L = 9/4`, parts 1066–1074 of 1374

File 131 of 167: the parts `rows225C_1066` … `rows225C_1074` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59850 depth-4 tests: row 153 columns 82–87, row 153 columns 88–95, row 153
columns 96–399, row 154 columns 0–58, row 154 columns 59–63, row 154 columns 64–67, row 154 columns 68–71, row 154
columns 72–75, row 154 columns 76–80), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_1066 : rowsJ 153 154 82 88 ≤ 702419278585 := by decide +kernel

theorem rows225C_1067 : rowsJ 153 154 88 96 ≤ 0 := by decide +kernel

theorem rows225C_1068 : rowsJ 153 154 96 400 ≤ 211955166072009 := by decide +kernel

theorem rows225C_1069 : rowsJ 154 155 0 59 ≤ 107908143025098 := by decide +kernel

theorem rows225C_1070 : rowsJ 154 155 59 64 ≤ 13245278084528 := by decide +kernel

theorem rows225C_1071 : rowsJ 154 155 64 68 ≤ 16914159697379 := by decide +kernel

theorem rows225C_1072 : rowsJ 154 155 68 72 ≤ 14313746100552 := by decide +kernel

theorem rows225C_1073 : rowsJ 154 155 72 76 ≤ 8494719945466 := by decide +kernel

theorem rows225C_1074 : rowsJ 154 155 76 81 ≤ 4744912902393 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1066
#print axioms SieveCert.rows225C_1074
