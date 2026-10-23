/-
# Round 625: the certificate at `L = 9/4`, parts 677–685 of 1374

File 84 of 167: the parts `rows225C_677` … `rows225C_685` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 58879 depth-4 tests: row 119 columns 106–109, row 119 columns 110–114, row 119
columns 115–399, row 120 columns 0–34, row 120 columns 35–66, row 120 columns 67–75, row 120 columns 76–79, row 120
columns 80–82, row 120 columns 83–85), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_677 : rowsJ 119 120 106 110 ≤ 9408609387274 := by decide +kernel

theorem rows225C_678 : rowsJ 119 120 110 115 ≤ 23090409834723 := by decide +kernel

theorem rows225C_679 : rowsJ 119 120 115 400 ≤ 407214917946285 := by decide +kernel

theorem rows225C_680 : rowsJ 120 121 0 35 ≤ 100135194062432 := by decide +kernel

theorem rows225C_681 : rowsJ 120 121 35 67 ≤ 315775492442398 := by decide +kernel

theorem rows225C_682 : rowsJ 120 121 67 76 ≤ 906650357138 := by decide +kernel

theorem rows225C_683 : rowsJ 120 121 76 80 ≤ 0 := by decide +kernel

theorem rows225C_684 : rowsJ 120 121 80 83 ≤ 0 := by decide +kernel

theorem rows225C_685 : rowsJ 120 121 83 86 ≤ 20564505846 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_677
#print axioms SieveCert.rows225C_685
