/-
# Round 625: the certificate at `L = 9/4`, parts 1124–1131 of 1374

File 138 of 167: the parts `rows225C_1124` … `rows225C_1131` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55220 depth-4 tests: row 160 columns 75–80, row 160 columns 81–88, row 160
columns 89–399, row 161 columns 0–56, row 161 columns 57–61, row 161 columns 62–65, row 161 columns 66–70, row 161
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

theorem rows225C_1124 : rowsJ 160 161 75 81 ≤ 3242314246808 := by decide +kernel

theorem rows225C_1125 : rowsJ 160 161 81 89 ≤ 111023862943 := by decide +kernel

theorem rows225C_1126 : rowsJ 160 161 89 400 ≤ 218081788274342 := by decide +kernel

theorem rows225C_1127 : rowsJ 161 162 0 57 ≤ 74859031256570 := by decide +kernel

theorem rows225C_1128 : rowsJ 161 162 57 62 ≤ 17546145507601 := by decide +kernel

theorem rows225C_1129 : rowsJ 161 162 62 66 ≤ 20195252262460 := by decide +kernel

theorem rows225C_1130 : rowsJ 161 162 66 71 ≤ 16419062969290 := by decide +kernel

theorem rows225C_1131 : rowsJ 161 162 71 76 ≤ 7273991087701 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1124
#print axioms SieveCert.rows225C_1131
