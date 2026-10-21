/-
# Round 625: the certificate at `L = 9/4`, parts 1116–1123 of 1374

File 137 of 167: the parts `rows225C_1116` … `rows225C_1123` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 53744 depth-4 tests: row 159 columns 76–81, row 159 columns 82–89, row 159
columns 90–399, row 160 columns 0–56, row 160 columns 57–61, row 160 columns 62–65, row 160 columns 66–69, row 160
columns 70–74), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1116 : rowsJ 159 160 76 82 ≤ 2744889051421 := by decide +kernel

theorem rows225C_1117 : rowsJ 159 160 82 90 ≤ 68555250982 := by decide +kernel

theorem rows225C_1118 : rowsJ 159 160 90 400 ≤ 109522324490708 := by decide +kernel

theorem rows225C_1119 : rowsJ 160 161 0 57 ≤ 77954228439591 := by decide +kernel

theorem rows225C_1120 : rowsJ 160 161 57 62 ≤ 16271754555725 := by decide +kernel

theorem rows225C_1121 : rowsJ 160 161 62 66 ≤ 19953706696843 := by decide +kernel

theorem rows225C_1122 : rowsJ 160 161 66 70 ≤ 14715107723208 := by decide +kernel

theorem rows225C_1123 : rowsJ 160 161 70 75 ≤ 9470167953637 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1116
#print axioms SieveCert.rows225C_1123
