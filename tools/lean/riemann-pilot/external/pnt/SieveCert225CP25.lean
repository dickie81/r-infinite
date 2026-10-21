/-
# Round 625: the certificate at `L = 9/4`, parts 205–212 of 1374

File 25 of 167: the parts `rows225C_205` … `rows225C_212` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56069 depth-4 tests: row 75 columns 35–43, row 75 columns 44–49, row 75 columns
50–54, row 75 columns 55–58, row 75 columns 59–63, row 75 columns 64–69, row 75 columns 70–399, row 76 columns
0–34), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_205 : rowsJ 75 76 35 44 ≤ 58335853861969 := by decide +kernel

theorem rows225C_206 : rowsJ 75 76 44 50 ≤ 62359949023118 := by decide +kernel

theorem rows225C_207 : rowsJ 75 76 50 55 ≤ 109604642774083 := by decide +kernel

theorem rows225C_208 : rowsJ 75 76 55 59 ≤ 133611234959031 := by decide +kernel

theorem rows225C_209 : rowsJ 75 76 59 64 ≤ 164959908356512 := by decide +kernel

theorem rows225C_210 : rowsJ 75 76 64 70 ≤ 175691583058179 := by decide +kernel

theorem rows225C_211 : rowsJ 75 76 70 400 ≤ 150663247399156 := by decide +kernel

theorem rows225C_212 : rowsJ 76 77 0 35 ≤ 517664621464634 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_205
#print axioms SieveCert.rows225C_212
