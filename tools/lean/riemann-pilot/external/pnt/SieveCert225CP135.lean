/-
# Round 625: the certificate at `L = 9/4`, parts 1100–1107 of 1374

File 135 of 167: the parts `rows225C_1100` … `rows225C_1107` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 57588 depth-4 tests: row 157 columns 76–81, row 157 columns 82–88, row 157
columns 89–399, row 158 columns 0–57, row 158 columns 58–62, row 158 columns 63–66, row 158 columns 67–70, row 158
columns 71–75), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1100 : rowsJ 157 158 76 82 ≤ 3652246172591 := by decide +kernel

theorem rows225C_1101 : rowsJ 157 158 82 89 ≤ 187359735723 := by decide +kernel

theorem rows225C_1102 : rowsJ 157 158 89 400 ≤ 633262788820 := by decide +kernel

theorem rows225C_1103 : rowsJ 158 159 0 58 ≤ 87828622937605 := by decide +kernel

theorem rows225C_1104 : rowsJ 158 159 58 63 ≤ 15858253581692 := by decide +kernel

theorem rows225C_1105 : rowsJ 158 159 63 67 ≤ 19257256574010 := by decide +kernel

theorem rows225C_1106 : rowsJ 158 159 67 71 ≤ 14223676287310 := by decide +kernel

theorem rows225C_1107 : rowsJ 158 159 71 76 ≤ 9235567696681 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1100
#print axioms SieveCert.rows225C_1107
