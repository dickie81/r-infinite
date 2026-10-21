/-
# Round 625: the certificate at `L = 9/4`, parts 718–725 of 1374

File 89 of 167: the parts `rows225C_718` … `rows225C_725` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54550 depth-4 tests: row 122 columns 99–102, row 122 columns 103–106, row 122
columns 107–111, row 122 columns 112–399, row 123 columns 0–34, row 123 columns 35–68, row 123 columns 69–75, row
123 columns 76–79), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_718 : rowsJ 122 123 99 103 ≤ 2339838389208 := by decide +kernel

theorem rows225C_719 : rowsJ 122 123 103 107 ≤ 6675505094066 := by decide +kernel

theorem rows225C_720 : rowsJ 122 123 107 112 ≤ 18235452318829 := by decide +kernel

theorem rows225C_721 : rowsJ 122 123 112 400 ≤ 894023539986927 := by decide +kernel

theorem rows225C_722 : rowsJ 123 124 0 35 ≤ 121200728147603 := by decide +kernel

theorem rows225C_723 : rowsJ 123 124 35 69 ≤ 257677264429098 := by decide +kernel

theorem rows225C_724 : rowsJ 123 124 69 76 ≤ 0 := by decide +kernel

theorem rows225C_725 : rowsJ 123 124 76 80 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_718
#print axioms SieveCert.rows225C_725
