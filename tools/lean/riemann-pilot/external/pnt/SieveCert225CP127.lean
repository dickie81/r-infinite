/-
# Round 625: the certificate at `L = 9/4`, parts 1034–1041 of 1374

File 127 of 167: the parts `rows225C_1034` … `rows225C_1041` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55975 depth-4 tests: row 150 columns 60–65, row 150 columns 66–69, row 150
columns 70–73, row 150 columns 74–77, row 150 columns 78–82, row 150 columns 83–88, row 150 columns 89–95, row 150
columns 96–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1034 : rowsJ 150 151 60 66 ≤ 14012732191761 := by decide +kernel

theorem rows225C_1035 : rowsJ 150 151 66 70 ≤ 14618698678675 := by decide +kernel

theorem rows225C_1036 : rowsJ 150 151 70 74 ≤ 11853530708188 := by decide +kernel

theorem rows225C_1037 : rowsJ 150 151 74 78 ≤ 6825749278380 := by decide +kernel

theorem rows225C_1038 : rowsJ 150 151 78 83 ≤ 3673038581093 := by decide +kernel

theorem rows225C_1039 : rowsJ 150 151 83 89 ≤ 710858134598 := by decide +kernel

theorem rows225C_1040 : rowsJ 150 151 89 96 ≤ 0 := by decide +kernel

theorem rows225C_1041 : rowsJ 150 151 96 400 ≤ 417704648898128 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1034
#print axioms SieveCert.rows225C_1041
