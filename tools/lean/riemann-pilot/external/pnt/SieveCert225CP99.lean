/-
# Round 625: the certificate at `L = 9/4`, parts 801–809 of 1374

File 99 of 167: the parts `rows225C_801` … `rows225C_809` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59873 depth-4 tests: row 128 columns 104–108, row 128 columns 109–399, row 129
columns 0–36, row 129 columns 37–69, row 129 columns 70–74, row 129 columns 75–78, row 129 columns 79–81, row 129
columns 82–84, row 129 columns 85–87), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_801 : rowsJ 128 129 104 109 ≤ 16410113885085 := by decide +kernel

theorem rows225C_802 : rowsJ 128 129 109 400 ≤ 1437356546970005 := by decide +kernel

theorem rows225C_803 : rowsJ 129 130 0 37 ≤ 179179529468574 := by decide +kernel

theorem rows225C_804 : rowsJ 129 130 37 70 ≤ 131934182307075 := by decide +kernel

theorem rows225C_805 : rowsJ 129 130 70 75 ≤ 0 := by decide +kernel

theorem rows225C_806 : rowsJ 129 130 75 79 ≤ 0 := by decide +kernel

theorem rows225C_807 : rowsJ 129 130 79 82 ≤ 0 := by decide +kernel

theorem rows225C_808 : rowsJ 129 130 82 85 ≤ 0 := by decide +kernel

theorem rows225C_809 : rowsJ 129 130 85 88 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_801
#print axioms SieveCert.rows225C_809
