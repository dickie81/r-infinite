/-
# Round 625: the certificate at `L = 9/4`, parts 1132–1139 of 1374

File 139 of 167: the parts `rows225C_1132` … `rows225C_1139` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 53903 depth-4 tests: row 161 columns 76–81, row 161 columns 82–89, row 161
columns 90–399, row 162 columns 0–55, row 162 columns 56–61, row 162 columns 62–65, row 162 columns 66–70, row 162
columns 71–76), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1132 : rowsJ 161 162 76 82 ≤ 1963392348715 := by decide +kernel

theorem rows225C_1133 : rowsJ 161 162 82 90 ≤ 14058791343 := by decide +kernel

theorem rows225C_1134 : rowsJ 161 162 90 400 ≤ 325704317334668 := by decide +kernel

theorem rows225C_1135 : rowsJ 162 163 0 56 ≤ 68828791610166 := by decide +kernel

theorem rows225C_1136 : rowsJ 162 163 56 62 ≤ 21364994598093 := by decide +kernel

theorem rows225C_1137 : rowsJ 162 163 62 66 ≤ 20393212546637 := by decide +kernel

theorem rows225C_1138 : rowsJ 162 163 66 71 ≤ 15505416685960 := by decide +kernel

theorem rows225C_1139 : rowsJ 162 163 71 77 ≤ 7237860070726 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1132
#print axioms SieveCert.rows225C_1139
