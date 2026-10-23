/-
# Round 625: the certificate at `L = 9/4`, parts 277–284 of 1374

File 34 of 167: the parts `rows225C_277` … `rows225C_284` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 57707 depth-4 tests: row 84 columns 50–54, row 84 columns 55–60, row 84 columns
61–69, row 84 columns 70–399, row 85 columns 0–34, row 85 columns 35–43, row 85 columns 44–49, row 85 columns
50–54), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_277 : rowsJ 84 85 50 55 ≤ 151236940169757 := by decide +kernel

theorem rows225C_278 : rowsJ 84 85 55 61 ≤ 177229832274138 := by decide +kernel

theorem rows225C_279 : rowsJ 84 85 61 70 ≤ 217270791201637 := by decide +kernel

theorem rows225C_280 : rowsJ 84 85 70 400 ≤ 228305406870495 := by decide +kernel

theorem rows225C_281 : rowsJ 85 86 0 35 ≤ 321007309446620 := by decide +kernel

theorem rows225C_282 : rowsJ 85 86 35 44 ≤ 40241845823162 := by decide +kernel

theorem rows225C_283 : rowsJ 85 86 44 50 ≤ 106315431128529 := by decide +kernel

theorem rows225C_284 : rowsJ 85 86 50 55 ≤ 153277903365462 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_277
#print axioms SieveCert.rows225C_284
