/-
# Round 625: the certificate at `L = 9/4`, parts 462–469 of 1374

File 57 of 167: the parts `rows225C_462` … `rows225C_469` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 53947 depth-4 tests: row 104 columns 93–94, row 104 columns 95–96, row 104
columns 97–99, row 104 columns 100–102, row 104 columns 103–399, row 105 columns 0–34, row 105 columns 35–43, row
105 columns 44–55), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_462 : rowsJ 104 105 93 95 ≤ 2389623242619 := by decide +kernel

theorem rows225C_463 : rowsJ 104 105 95 97 ≤ 2059021654334 := by decide +kernel

theorem rows225C_464 : rowsJ 104 105 97 100 ≤ 2515309806868 := by decide +kernel

theorem rows225C_465 : rowsJ 104 105 100 103 ≤ 1885806470302 := by decide +kernel

theorem rows225C_466 : rowsJ 104 105 103 400 ≤ 947417981133 := by decide +kernel

theorem rows225C_467 : rowsJ 105 106 0 35 ≤ 72786211518203 := by decide +kernel

theorem rows225C_468 : rowsJ 105 106 35 44 ≤ 163122352223763 := by decide +kernel

theorem rows225C_469 : rowsJ 105 106 44 56 ≤ 249443168102160 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_462
#print axioms SieveCert.rows225C_469
