/-
# Round 625: the certificate at `L = 9/4`, parts 1108–1115 of 1374

File 136 of 167: the parts `rows225C_1108` … `rows225C_1115` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56331 depth-4 tests: row 158 columns 76–81, row 158 columns 82–88, row 158
columns 89–399, row 159 columns 0–56, row 159 columns 57–62, row 159 columns 63–66, row 159 columns 67–70, row 159
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

theorem rows225C_1108 : rowsJ 158 159 76 82 ≤ 3162263492932 := by decide +kernel

theorem rows225C_1109 : rowsJ 158 159 82 89 ≤ 108284851960 := by decide +kernel

theorem rows225C_1110 : rowsJ 158 159 89 400 ≤ 0 := by decide +kernel

theorem rows225C_1111 : rowsJ 159 160 0 57 ≤ 82110315069840 := by decide +kernel

theorem rows225C_1112 : rowsJ 159 160 57 63 ≤ 19356740299886 := by decide +kernel

theorem rows225C_1113 : rowsJ 159 160 63 67 ≤ 19552534688877 := by decide +kernel

theorem rows225C_1114 : rowsJ 159 160 67 71 ≤ 13610211543141 := by decide +kernel

theorem rows225C_1115 : rowsJ 159 160 71 76 ≤ 8573934036011 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1108
#print axioms SieveCert.rows225C_1115
