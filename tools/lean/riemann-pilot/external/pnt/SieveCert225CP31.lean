/-
# Round 625: the certificate at `L = 9/4`, parts 253–260 of 1374

File 31 of 167: the parts `rows225C_253` … `rows225C_260` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 53326 depth-4 tests: row 81 columns 35–43, row 81 columns 44–49, row 81 columns
50–54, row 81 columns 55–59, row 81 columns 60–66, row 81 columns 67–77, row 81 columns 78–399, row 82 columns
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

theorem rows225C_253 : rowsJ 81 82 35 44 ≤ 37706863316300 := by decide +kernel

theorem rows225C_254 : rowsJ 81 82 44 50 ≤ 84685181991979 := by decide +kernel

theorem rows225C_255 : rowsJ 81 82 50 55 ≤ 141476246899009 := by decide +kernel

theorem rows225C_256 : rowsJ 81 82 55 60 ≤ 159238480135574 := by decide +kernel

theorem rows225C_257 : rowsJ 81 82 60 67 ≤ 193678553186003 := by decide +kernel

theorem rows225C_258 : rowsJ 81 82 67 78 ≤ 232223841839160 := by decide +kernel

theorem rows225C_259 : rowsJ 81 82 78 400 ≤ 61991817391731 := by decide +kernel

theorem rows225C_260 : rowsJ 82 83 0 35 ≤ 383665049880326 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_253
#print axioms SieveCert.rows225C_260
