/-
# Round 625: the certificate at `L = 9/4`, parts 1075–1082 of 1374

File 132 of 167: the parts `rows225C_1075` … `rows225C_1082` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54283 depth-4 tests: row 154 columns 81–86, row 154 columns 87–94, row 154
columns 95–399, row 155 columns 0–57, row 155 columns 58–63, row 155 columns 64–67, row 155 columns 68–71, row 155
columns 72–76), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1075 : rowsJ 154 155 81 87 ≤ 904945262637 := by decide +kernel

theorem rows225C_1076 : rowsJ 154 155 87 95 ≤ 0 := by decide +kernel

theorem rows225C_1077 : rowsJ 154 155 95 400 ≤ 211654401953843 := by decide +kernel

theorem rows225C_1078 : rowsJ 155 156 0 58 ≤ 101607716572898 := by decide +kernel

theorem rows225C_1079 : rowsJ 155 156 58 64 ≤ 16173664218071 := by decide +kernel

theorem rows225C_1080 : rowsJ 155 156 64 68 ≤ 17666664587987 := by decide +kernel

theorem rows225C_1081 : rowsJ 155 156 68 72 ≤ 13985730445498 := by decide +kernel

theorem rows225C_1082 : rowsJ 155 156 72 77 ≤ 9474723640267 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1075
#print axioms SieveCert.rows225C_1082
