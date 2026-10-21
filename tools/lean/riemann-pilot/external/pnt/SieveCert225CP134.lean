/-
# Round 625: the certificate at `L = 9/4`, parts 1092–1099 of 1374

File 134 of 167: the parts `rows225C_1092` … `rows225C_1099` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56733 depth-4 tests: row 156 columns 77–82, row 156 columns 83–89, row 156
columns 90–399, row 157 columns 0–57, row 157 columns 58–62, row 157 columns 63–66, row 157 columns 67–70, row 157
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

theorem rows225C_1092 : rowsJ 156 157 77 83 ≤ 3085329446180 := by decide +kernel

theorem rows225C_1093 : rowsJ 156 157 83 90 ≤ 105652478517 := by decide +kernel

theorem rows225C_1094 : rowsJ 156 157 90 400 ≤ 106484407502982 := by decide +kernel

theorem rows225C_1095 : rowsJ 157 158 0 58 ≤ 92396771779445 := by decide +kernel

theorem rows225C_1096 : rowsJ 157 158 58 63 ≤ 14713427202304 := by decide +kernel

theorem rows225C_1097 : rowsJ 157 158 63 67 ≤ 18534017760483 := by decide +kernel

theorem rows225C_1098 : rowsJ 157 158 67 71 ≤ 14796132989242 := by decide +kernel

theorem rows225C_1099 : rowsJ 157 158 71 76 ≤ 9920985904495 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1092
#print axioms SieveCert.rows225C_1099
