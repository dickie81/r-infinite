/-
# Round 625: the certificate at `L = 9/4`, parts 526–533 of 1374

File 65 of 167: the parts `rows225C_526` … `rows225C_533` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 52304 depth-4 tests: row 109 columns 88–90, row 109 columns 91–93, row 109
columns 94–96, row 109 columns 97–99, row 109 columns 100–102, row 109 columns 103–105, row 109 columns 106–108, row
109 columns 109–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_526 : rowsJ 109 110 88 91 ≤ 1617246626546 := by decide +kernel

theorem rows225C_527 : rowsJ 109 110 91 94 ≤ 1569693212021 := by decide +kernel

theorem rows225C_528 : rowsJ 109 110 94 97 ≤ 1087362342849 := by decide +kernel

theorem rows225C_529 : rowsJ 109 110 97 100 ≤ 686542920485 := by decide +kernel

theorem rows225C_530 : rowsJ 109 110 100 103 ≤ 387882304147 := by decide +kernel

theorem rows225C_531 : rowsJ 109 110 103 106 ≤ 696221443001 := by decide +kernel

theorem rows225C_532 : rowsJ 109 110 106 109 ≤ 2144056091967 := by decide +kernel

theorem rows225C_533 : rowsJ 109 110 109 400 ≤ 1229329507011 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_526
#print axioms SieveCert.rows225C_533
