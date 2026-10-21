/-
# Round 625: the certificate at `L = 9/4`, parts 1140–1147 of 1374

File 140 of 167: the parts `rows225C_1140` … `rows225C_1147` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 57826 depth-4 tests: row 162 columns 77–83, row 162 columns 84–399, row 163
columns 0–55, row 163 columns 56–60, row 163 columns 61–64, row 163 columns 65–69, row 163 columns 70–75, row 163
columns 76–82), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1140 : rowsJ 162 163 77 84 ≤ 999313219700 := by decide +kernel

theorem rows225C_1141 : rowsJ 162 163 84 400 ≤ 432415390159061 := by decide +kernel

theorem rows225C_1142 : rowsJ 163 164 0 56 ≤ 66127697779179 := by decide +kernel

theorem rows225C_1143 : rowsJ 163 164 56 61 ≤ 18013327207690 := by decide +kernel

theorem rows225C_1144 : rowsJ 163 164 61 65 ≤ 20736463519559 := by decide +kernel

theorem rows225C_1145 : rowsJ 163 164 65 70 ≤ 16847397743693 := by decide +kernel

theorem rows225C_1146 : rowsJ 163 164 70 76 ≤ 8174321766207 := by decide +kernel

theorem rows225C_1147 : rowsJ 163 164 76 83 ≤ 1317034749707 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1140
#print axioms SieveCert.rows225C_1147
