/-
# Round 625: the certificate at `L = 9/4`, parts 605–612 of 1374

File 75 of 167: the parts `rows225C_605` … `rows225C_612` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 58976 depth-4 tests: row 115 columns 0–34, row 115 columns 35–48, row 115 columns
49–75, row 115 columns 76–80, row 115 columns 81–83, row 115 columns 84–86, row 115 columns 87–89, row 115 columns
90–92), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_605 : rowsJ 115 116 0 35 ≤ 71745320513679 := by decide +kernel

theorem rows225C_606 : rowsJ 115 116 35 49 ≤ 266364209419321 := by decide +kernel

theorem rows225C_607 : rowsJ 115 116 49 76 ≤ 151830543998318 := by decide +kernel

theorem rows225C_608 : rowsJ 115 116 76 81 ≤ 0 := by decide +kernel

theorem rows225C_609 : rowsJ 115 116 81 84 ≤ 0 := by decide +kernel

theorem rows225C_610 : rowsJ 115 116 84 87 ≤ 216289886094 := by decide +kernel

theorem rows225C_611 : rowsJ 115 116 87 90 ≤ 427122182258 := by decide +kernel

theorem rows225C_612 : rowsJ 115 116 90 93 ≤ 193214151771 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_605
#print axioms SieveCert.rows225C_612
