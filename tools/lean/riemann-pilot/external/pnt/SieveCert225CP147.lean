/-
# Round 625: the certificate at `L = 9/4`, parts 1196–1203 of 1374

File 147 of 167: the parts `rows225C_1196` … `rows225C_1203` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55817 depth-4 tests: row 171 columns 53–58, row 171 columns 59–63, row 171
columns 64–69, row 171 columns 70–77, row 171 columns 78–399, row 172 columns 0–52, row 172 columns 53–57, row 172
columns 58–62), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1196 : rowsJ 171 172 53 59 ≤ 28648212190100 := by decide +kernel

theorem rows225C_1197 : rowsJ 171 172 59 64 ≤ 24210303503917 := by decide +kernel

theorem rows225C_1198 : rowsJ 171 172 64 70 ≤ 13257374118339 := by decide +kernel

theorem rows225C_1199 : rowsJ 171 172 70 78 ≤ 3291076670362 := by decide +kernel

theorem rows225C_1200 : rowsJ 171 172 78 400 ≤ 1332651500336745 := by decide +kernel

theorem rows225C_1201 : rowsJ 172 173 0 53 ≤ 40449203755534 := by decide +kernel

theorem rows225C_1202 : rowsJ 172 173 53 58 ≤ 24134919475843 := by decide +kernel

theorem rows225C_1203 : rowsJ 172 173 58 63 ≤ 26031094267943 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1196
#print axioms SieveCert.rows225C_1203
