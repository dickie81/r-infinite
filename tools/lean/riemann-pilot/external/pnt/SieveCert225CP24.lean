/-
# Round 625: the certificate at `L = 9/4`, parts 197–204 of 1374

File 24 of 167: the parts `rows225C_197` … `rows225C_204` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56099 depth-4 tests: row 74 columns 35–43, row 74 columns 44–49, row 74 columns
50–54, row 74 columns 55–58, row 74 columns 59–63, row 74 columns 64–69, row 74 columns 70–399, row 75 columns
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

theorem rows225C_197 : rowsJ 74 75 35 44 ≤ 64385211290693 := by decide +kernel

theorem rows225C_198 : rowsJ 74 75 44 50 ≤ 60543024464510 := by decide +kernel

theorem rows225C_199 : rowsJ 74 75 50 55 ≤ 104833492736512 := by decide +kernel

theorem rows225C_200 : rowsJ 74 75 55 59 ≤ 130925036018159 := by decide +kernel

theorem rows225C_201 : rowsJ 74 75 59 64 ≤ 168136837262283 := by decide +kernel

theorem rows225C_202 : rowsJ 74 75 64 70 ≤ 179689365385996 := by decide +kernel

theorem rows225C_203 : rowsJ 74 75 70 400 ≤ 130848906126519 := by decide +kernel

theorem rows225C_204 : rowsJ 75 76 0 35 ≤ 540609127522630 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_197
#print axioms SieveCert.rows225C_204
