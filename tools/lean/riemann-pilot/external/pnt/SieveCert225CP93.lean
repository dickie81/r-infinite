/-
# Round 625: the certificate at `L = 9/4`, parts 752–759 of 1374

File 93 of 167: the parts `rows225C_752` … `rows225C_759` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54848 depth-4 tests: row 125 columns 69–74, row 125 columns 75–78, row 125
columns 79–81, row 125 columns 82–84, row 125 columns 85–87, row 125 columns 88–90, row 125 columns 91–93, row 125
columns 94–97), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_752 : rowsJ 125 126 69 75 ≤ 0 := by decide +kernel

theorem rows225C_753 : rowsJ 125 126 75 79 ≤ 0 := by decide +kernel

theorem rows225C_754 : rowsJ 125 126 79 82 ≤ 0 := by decide +kernel

theorem rows225C_755 : rowsJ 125 126 82 85 ≤ 0 := by decide +kernel

theorem rows225C_756 : rowsJ 125 126 85 88 ≤ 0 := by decide +kernel

theorem rows225C_757 : rowsJ 125 126 88 91 ≤ 0 := by decide +kernel

theorem rows225C_758 : rowsJ 125 126 91 94 ≤ 0 := by decide +kernel

theorem rows225C_759 : rowsJ 125 126 94 98 ≤ 226516695749 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_752
#print axioms SieveCert.rows225C_759
