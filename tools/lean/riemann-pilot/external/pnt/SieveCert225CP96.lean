/-
# Round 625: the certificate at `L = 9/4`, parts 777–784 of 1374

File 96 of 167: the parts `rows225C_777` … `rows225C_784` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56223 depth-4 tests: row 127 columns 0–35, row 127 columns 36–69, row 127 columns
70–74, row 127 columns 75–78, row 127 columns 79–81, row 127 columns 82–84, row 127 columns 85–87, row 127 columns
88–90), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_777 : rowsJ 127 128 0 36 ≤ 159055522715766 := by decide +kernel

theorem rows225C_778 : rowsJ 127 128 36 70 ≤ 173421202407727 := by decide +kernel

theorem rows225C_779 : rowsJ 127 128 70 75 ≤ 0 := by decide +kernel

theorem rows225C_780 : rowsJ 127 128 75 79 ≤ 0 := by decide +kernel

theorem rows225C_781 : rowsJ 127 128 79 82 ≤ 0 := by decide +kernel

theorem rows225C_782 : rowsJ 127 128 82 85 ≤ 0 := by decide +kernel

theorem rows225C_783 : rowsJ 127 128 85 88 ≤ 0 := by decide +kernel

theorem rows225C_784 : rowsJ 127 128 88 91 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_777
#print axioms SieveCert.rows225C_784
