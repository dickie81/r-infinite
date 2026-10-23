/-
# Round 625: the certificate at `L = 9/4`, parts 572–579 of 1374

File 71 of 167: the parts `rows225C_572` … `rows225C_579` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56555 depth-4 tests: row 112 columns 100–102, row 112 columns 103–105, row 112
columns 106–109, row 112 columns 110–399, row 113 columns 0–34, row 113 columns 35–46, row 113 columns 47–74, row
113 columns 75–80), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_572 : rowsJ 112 113 100 103 ≤ 178121143718 := by decide +kernel

theorem rows225C_573 : rowsJ 112 113 103 106 ≤ 1225735703124 := by decide +kernel

theorem rows225C_574 : rowsJ 112 113 106 110 ≤ 4992447838696 := by decide +kernel

theorem rows225C_575 : rowsJ 112 113 110 400 ≤ 7444651094998 := by decide +kernel

theorem rows225C_576 : rowsJ 113 114 0 35 ≤ 65661403954731 := by decide +kernel

theorem rows225C_577 : rowsJ 113 114 35 47 ≤ 243703717213330 := by decide +kernel

theorem rows225C_578 : rowsJ 113 114 47 75 ≤ 212845569101902 := by decide +kernel

theorem rows225C_579 : rowsJ 113 114 75 81 ≤ 361457844474 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_572
#print axioms SieveCert.rows225C_579
