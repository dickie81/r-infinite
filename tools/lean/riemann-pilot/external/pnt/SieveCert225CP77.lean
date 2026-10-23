/-
# Round 625: the certificate at `L = 9/4`, parts 621–628 of 1374

File 77 of 167: the parts `rows225C_621` … `rows225C_628` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 58255 depth-4 tests: row 116 columns 35–49, row 116 columns 50–75, row 116
columns 76–80, row 116 columns 81–83, row 116 columns 84–86, row 116 columns 87–89, row 116 columns 90–92, row 116
columns 93–95), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_621 : rowsJ 116 117 35 50 ≤ 272505705681439 := by decide +kernel

theorem rows225C_622 : rowsJ 116 117 50 76 ≤ 125536683879558 := by decide +kernel

theorem rows225C_623 : rowsJ 116 117 76 81 ≤ 0 := by decide +kernel

theorem rows225C_624 : rowsJ 116 117 81 84 ≤ 0 := by decide +kernel

theorem rows225C_625 : rowsJ 116 117 84 87 ≤ 214455164199 := by decide +kernel

theorem rows225C_626 : rowsJ 116 117 87 90 ≤ 259188140860 := by decide +kernel

theorem rows225C_627 : rowsJ 116 117 90 93 ≤ 85723225755 := by decide +kernel

theorem rows225C_628 : rowsJ 116 117 93 96 ≤ 7255545619 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_621
#print axioms SieveCert.rows225C_628
