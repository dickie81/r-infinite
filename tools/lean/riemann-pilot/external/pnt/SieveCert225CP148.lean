/-
# Round 625: the certificate at `L = 9/4`, parts 1204–1212 of 1374

File 148 of 167: the parts `rows225C_1204` … `rows225C_1212` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 58769 depth-4 tests: row 172 columns 63–68, row 172 columns 69–76, row 172
columns 77–399, row 173 columns 0–51, row 173 columns 52–57, row 173 columns 58–62, row 173 columns 63–68, row 173
columns 69–76, row 173 columns 77–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_1204 : rowsJ 172 173 63 69 ≤ 14603504664455 := by decide +kernel

theorem rows225C_1205 : rowsJ 172 173 69 77 ≤ 3927196107603 := by decide +kernel

theorem rows225C_1206 : rowsJ 172 173 77 400 ≤ 1428536824160249 := by decide +kernel

theorem rows225C_1207 : rowsJ 173 174 0 52 ≤ 36609967708023 := by decide +kernel

theorem rows225C_1208 : rowsJ 173 174 52 58 ≤ 29465736734878 := by decide +kernel

theorem rows225C_1209 : rowsJ 173 174 58 63 ≤ 24892704154296 := by decide +kernel

theorem rows225C_1210 : rowsJ 173 174 63 69 ≤ 13628383745240 := by decide +kernel

theorem rows225C_1211 : rowsJ 173 174 69 77 ≤ 3382822240936 := by decide +kernel

theorem rows225C_1212 : rowsJ 173 174 77 400 ≤ 1524278811197649 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1204
#print axioms SieveCert.rows225C_1212
