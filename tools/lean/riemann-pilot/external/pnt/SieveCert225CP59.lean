/-
# Round 625: the certificate at `L = 9/4`, parts 478–485 of 1374

File 59 of 167: the parts `rows225C_478` … `rows225C_485` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56003 depth-4 tests: row 105 columns 101–103, row 105 columns 104–399, row 106
columns 0–34, row 106 columns 35–43, row 106 columns 44–56, row 106 columns 57–79, row 106 columns 80–84, row 106
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

theorem rows225C_478 : rowsJ 105 106 101 104 ≤ 1317980804562 := by decide +kernel

theorem rows225C_479 : rowsJ 105 106 104 400 ≤ 708085849224 := by decide +kernel

theorem rows225C_480 : rowsJ 106 107 0 35 ≤ 69165807694699 := by decide +kernel

theorem rows225C_481 : rowsJ 106 107 35 44 ≤ 168698840100045 := by decide +kernel

theorem rows225C_482 : rowsJ 106 107 44 57 ≤ 255310563025055 := by decide +kernel

theorem rows225C_483 : rowsJ 106 107 57 80 ≤ 161057815772904 := by decide +kernel

theorem rows225C_484 : rowsJ 106 107 80 85 ≤ 1771604569372 := by decide +kernel

theorem rows225C_485 : rowsJ 106 107 85 88 ≤ 477705459809 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_478
#print axioms SieveCert.rows225C_485
