/-
# Round 625: the certificate at `L = 9/4`, parts 596–604 of 1374

File 74 of 167: the parts `rows225C_596` … `rows225C_604` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59584 depth-4 tests: row 114 columns 87–89, row 114 columns 90–92, row 114
columns 93–95, row 114 columns 96–98, row 114 columns 99–101, row 114 columns 102–104, row 114 columns 105–108, row
114 columns 109–112, row 114 columns 113–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_596 : rowsJ 114 115 87 90 ≤ 636703435830 := by decide +kernel

theorem rows225C_597 : rowsJ 114 115 90 93 ≤ 344018564511 := by decide +kernel

theorem rows225C_598 : rowsJ 114 115 93 96 ≤ 138681626072 := by decide +kernel

theorem rows225C_599 : rowsJ 114 115 96 99 ≤ 22272067476 := by decide +kernel

theorem rows225C_600 : rowsJ 114 115 99 102 ≤ 158996153033 := by decide +kernel

theorem rows225C_601 : rowsJ 114 115 102 105 ≤ 1234263786430 := by decide +kernel

theorem rows225C_602 : rowsJ 114 115 105 109 ≤ 4936432788971 := by decide +kernel

theorem rows225C_603 : rowsJ 114 115 109 113 ≤ 10720877962230 := by decide +kernel

theorem rows225C_604 : rowsJ 114 115 113 400 ≤ 8269941103899 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_596
#print axioms SieveCert.rows225C_604
