/-
# Round 625: the certificate at `L = 9/4`, parts 1026–1033 of 1374

File 126 of 167: the parts `rows225C_1026` … `rows225C_1033` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 57784 depth-4 tests: row 149 columns 66–69, row 149 columns 70–73, row 149
columns 74–77, row 149 columns 78–82, row 149 columns 83–87, row 149 columns 88–93, row 149 columns 94–399, row 150
columns 0–59), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1026 : rowsJ 149 150 66 70 ≤ 13598025699434 := by decide +kernel

theorem rows225C_1027 : rowsJ 149 150 70 74 ≤ 11844844759044 := by decide +kernel

theorem rows225C_1028 : rowsJ 149 150 74 78 ≤ 6820550658707 := by decide +kernel

theorem rows225C_1029 : rowsJ 149 150 78 83 ≤ 3670230567583 := by decide +kernel

theorem rows225C_1030 : rowsJ 149 150 83 88 ≤ 710432367123 := by decide +kernel

theorem rows225C_1031 : rowsJ 149 150 88 94 ≤ 0 := by decide +kernel

theorem rows225C_1032 : rowsJ 149 150 94 400 ≤ 417467800269294 := by decide +kernel

theorem rows225C_1033 : rowsJ 150 151 0 60 ≤ 131485495993923 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1026
#print axioms SieveCert.rows225C_1033
