/-
# Round 625: the certificate at `L = 9/4`, parts 694–701 of 1374

File 86 of 167: the parts `rows225C_694` … `rows225C_701` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 57584 depth-4 tests: row 121 columns 0–34, row 121 columns 35–67, row 121 columns
68–75, row 121 columns 76–79, row 121 columns 80–82, row 121 columns 83–85, row 121 columns 86–88, row 121 columns
89–91), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_694 : rowsJ 121 122 0 35 ≤ 107813685393803 := by decide +kernel

theorem rows225C_695 : rowsJ 121 122 35 68 ≤ 296184238405479 := by decide +kernel

theorem rows225C_696 : rowsJ 121 122 68 76 ≤ 92600436396 := by decide +kernel

theorem rows225C_697 : rowsJ 121 122 76 80 ≤ 0 := by decide +kernel

theorem rows225C_698 : rowsJ 121 122 80 83 ≤ 0 := by decide +kernel

theorem rows225C_699 : rowsJ 121 122 83 86 ≤ 0 := by decide +kernel

theorem rows225C_700 : rowsJ 121 122 86 89 ≤ 0 := by decide +kernel

theorem rows225C_701 : rowsJ 121 122 89 92 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_694
#print axioms SieveCert.rows225C_701
