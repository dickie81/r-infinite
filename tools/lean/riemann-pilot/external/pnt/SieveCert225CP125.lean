/-
# Round 625: the certificate at `L = 9/4`, parts 1018–1025 of 1374

File 125 of 167: the parts `rows225C_1018` … `rows225C_1025` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 59186 depth-4 tests: row 148 columns 70–73, row 148 columns 74–77, row 148
columns 78–81, row 148 columns 82–86, row 148 columns 87–92, row 148 columns 93–399, row 149 columns 0–59, row 149
columns 60–65), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1018 : rowsJ 148 149 70 74 ≤ 11733910418277 := by decide +kernel

theorem rows225C_1019 : rowsJ 148 149 74 78 ≤ 6714213516304 := by decide +kernel

theorem rows225C_1020 : rowsJ 148 149 78 82 ≤ 3152223151189 := by decide +kernel

theorem rows225C_1021 : rowsJ 148 149 82 87 ≤ 976745714342 := by decide +kernel

theorem rows225C_1022 : rowsJ 148 149 87 93 ≤ 0 := by decide +kernel

theorem rows225C_1023 : rowsJ 148 149 93 400 ≤ 518662902816923 := by decide +kernel

theorem rows225C_1024 : rowsJ 149 150 0 60 ≤ 137983831827201 := by decide +kernel

theorem rows225C_1025 : rowsJ 149 150 60 66 ≤ 12899894119653 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1018
#print axioms SieveCert.rows225C_1025
