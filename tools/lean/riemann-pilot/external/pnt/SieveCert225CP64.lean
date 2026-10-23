/-
# Round 625: the certificate at `L = 9/4`, parts 518–525 of 1374

File 64 of 167: the parts `rows225C_518` … `rows225C_525` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 53141 depth-4 tests: row 108 columns 105–107, row 108 columns 108–399, row 109
columns 0–34, row 109 columns 35–44, row 109 columns 45–67, row 109 columns 68–80, row 109 columns 81–84, row 109
columns 85–87), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_518 : rowsJ 108 109 105 108 ≤ 1320340616154 := by decide +kernel

theorem rows225C_519 : rowsJ 108 109 108 400 ≤ 818297500804 := by decide +kernel

theorem rows225C_520 : rowsJ 109 110 0 35 ≤ 62948234470819 := by decide +kernel

theorem rows225C_521 : rowsJ 109 110 35 45 ≤ 204854918072747 := by decide +kernel

theorem rows225C_522 : rowsJ 109 110 45 68 ≤ 298856807454293 := by decide +kernel

theorem rows225C_523 : rowsJ 109 110 68 81 ≤ 28441544885082 := by decide +kernel

theorem rows225C_524 : rowsJ 109 110 81 85 ≤ 14546247626 := by decide +kernel

theorem rows225C_525 : rowsJ 109 110 85 88 ≤ 468804143367 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_518
#print axioms SieveCert.rows225C_525
