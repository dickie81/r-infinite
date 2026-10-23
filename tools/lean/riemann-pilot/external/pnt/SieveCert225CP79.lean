/-
# Round 625: the certificate at `L = 9/4`, parts 637–644 of 1374

File 79 of 167: the parts `rows225C_637` … `rows225C_644` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56953 depth-4 tests: row 117 columns 51–75, row 117 columns 76–80, row 117
columns 81–83, row 117 columns 84–86, row 117 columns 87–89, row 117 columns 90–92, row 117 columns 93–95, row 117
columns 96–98), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_637 : rowsJ 117 118 51 76 ≤ 102077129307599 := by decide +kernel

theorem rows225C_638 : rowsJ 117 118 76 81 ≤ 0 := by decide +kernel

theorem rows225C_639 : rowsJ 117 118 81 84 ≤ 0 := by decide +kernel

theorem rows225C_640 : rowsJ 117 118 84 87 ≤ 158925333462 := by decide +kernel

theorem rows225C_641 : rowsJ 117 118 87 90 ≤ 133230851316 := by decide +kernel

theorem rows225C_642 : rowsJ 117 118 90 93 ≤ 21368494224 := by decide +kernel

theorem rows225C_643 : rowsJ 117 118 93 96 ≤ 0 := by decide +kernel

theorem rows225C_644 : rowsJ 117 118 96 99 ≤ 20372268054 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_637
#print axioms SieveCert.rows225C_644
