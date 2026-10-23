/-
# Round 625: the certificate at `L = 9/4`, parts 726–733 of 1374

File 90 of 167: the parts `rows225C_726` … `rows225C_733` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55161 depth-4 tests: row 123 columns 80–82, row 123 columns 83–85, row 123
columns 86–88, row 123 columns 89–91, row 123 columns 92–94, row 123 columns 95–98, row 123 columns 99–102, row 123
columns 103–106), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_726 : rowsJ 123 124 80 83 ≤ 0 := by decide +kernel

theorem rows225C_727 : rowsJ 123 124 83 86 ≤ 0 := by decide +kernel

theorem rows225C_728 : rowsJ 123 124 86 89 ≤ 0 := by decide +kernel

theorem rows225C_729 : rowsJ 123 124 89 92 ≤ 0 := by decide +kernel

theorem rows225C_730 : rowsJ 123 124 92 95 ≤ 0 := by decide +kernel

theorem rows225C_731 : rowsJ 123 124 95 99 ≤ 376665039344 := by decide +kernel

theorem rows225C_732 : rowsJ 123 124 99 103 ≤ 2641128752347 := by decide +kernel

theorem rows225C_733 : rowsJ 123 124 103 107 ≤ 7229527901102 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_726
#print axioms SieveCert.rows225C_733
