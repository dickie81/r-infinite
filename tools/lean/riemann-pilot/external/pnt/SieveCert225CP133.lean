/-
# Round 625: the certificate at `L = 9/4`, parts 1083–1091 of 1374

File 133 of 167: the parts `rows225C_1083` … `rows225C_1091` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59451 depth-4 tests: row 155 columns 77–81, row 155 columns 82–87, row 155
columns 88–95, row 155 columns 96–399, row 156 columns 0–57, row 156 columns 58–63, row 156 columns 64–67, row 156
columns 68–71, row 156 columns 72–76), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_1083 : rowsJ 155 156 77 82 ≤ 3354756695429 := by decide +kernel

theorem rows225C_1084 : rowsJ 155 156 82 88 ≤ 392103386495 := by decide +kernel

theorem rows225C_1085 : rowsJ 155 156 88 96 ≤ 0 := by decide +kernel

theorem rows225C_1086 : rowsJ 155 156 96 400 ≤ 106970197226489 := by decide +kernel

theorem rows225C_1087 : rowsJ 156 157 0 58 ≤ 96479498935583 := by decide +kernel

theorem rows225C_1088 : rowsJ 156 157 58 64 ≤ 17466123296141 := by decide +kernel

theorem rows225C_1089 : rowsJ 156 157 64 68 ≤ 18403471126023 := by decide +kernel

theorem rows225C_1090 : rowsJ 156 157 68 72 ≤ 13556325034317 := by decide +kernel

theorem rows225C_1091 : rowsJ 156 157 72 77 ≤ 8934977527846 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1083
#print axioms SieveCert.rows225C_1091
