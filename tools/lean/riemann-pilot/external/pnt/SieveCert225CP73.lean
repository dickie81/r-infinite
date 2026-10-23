/-
# Round 625: the certificate at `L = 9/4`, parts 588–595 of 1374

File 73 of 167: the parts `rows225C_588` … `rows225C_595` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 58121 depth-4 tests: row 113 columns 106–109, row 113 columns 110–399, row 114
columns 0–34, row 114 columns 35–47, row 114 columns 48–75, row 114 columns 76–80, row 114 columns 81–83, row 114
columns 84–86), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_588 : rowsJ 113 114 106 110 ≤ 5591830831803 := by decide +kernel

theorem rows225C_589 : rowsJ 113 114 110 400 ≤ 11686280046324 := by decide +kernel

theorem rows225C_590 : rowsJ 114 115 0 35 ≤ 68354264589839 := by decide +kernel

theorem rows225C_591 : rowsJ 114 115 35 48 ≤ 256170015022246 := by decide +kernel

theorem rows225C_592 : rowsJ 114 115 48 76 ≤ 181031649317131 := by decide +kernel

theorem rows225C_593 : rowsJ 114 115 76 81 ≤ 0 := by decide +kernel

theorem rows225C_594 : rowsJ 114 115 81 84 ≤ 0 := by decide +kernel

theorem rows225C_595 : rowsJ 114 115 84 87 ≤ 217481637363 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_588
#print axioms SieveCert.rows225C_595
