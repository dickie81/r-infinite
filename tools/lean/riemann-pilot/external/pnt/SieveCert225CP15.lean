/-
# Round 625: the certificate at `L = 9/4`, parts 124–131 of 1374

File 15 of 167: the parts `rows225C_124` … `rows225C_131` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55339 depth-4 tests: row 64 columns 59–62, row 64 columns 63–399, row 65 columns
0–34, row 65 columns 35–43, row 65 columns 44–49, row 65 columns 50–54, row 65 columns 55–58, row 65 columns 59–62),
each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_124 : rowsJ 64 65 59 63 ≤ 133854089018297 := by decide +kernel

theorem rows225C_125 : rowsJ 64 65 63 400 ≤ 76660380573246 := by decide +kernel

theorem rows225C_126 : rowsJ 65 66 0 35 ≤ 769860273089190 := by decide +kernel

theorem rows225C_127 : rowsJ 65 66 35 44 ≤ 150054668384310 := by decide +kernel

theorem rows225C_128 : rowsJ 65 66 44 50 ≤ 69034310508400 := by decide +kernel

theorem rows225C_129 : rowsJ 65 66 50 55 ≤ 79974702261976 := by decide +kernel

theorem rows225C_130 : rowsJ 65 66 55 59 ≤ 97324901700089 := by decide +kernel

theorem rows225C_131 : rowsJ 65 66 59 63 ≤ 137931723061412 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_124
#print axioms SieveCert.rows225C_131
