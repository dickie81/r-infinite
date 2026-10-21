/-
# Round 625: the certificate at `L = 9/4`, parts 968–975 of 1374

File 119 of 167: the parts `rows225C_968` … `rows225C_975` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 58143 depth-4 tests: row 143 columns 71–73, row 143 columns 74–77, row 143
columns 78–81, row 143 columns 82–85, row 143 columns 86–90, row 143 columns 91–96, row 143 columns 97–399, row 144
columns 0–60), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_968 : rowsJ 143 144 71 74 ≤ 6411596601855 := by decide +kernel

theorem rows225C_969 : rowsJ 143 144 74 78 ≤ 5120713179885 := by decide +kernel

theorem rows225C_970 : rowsJ 143 144 78 82 ≤ 1580357151237 := by decide +kernel

theorem rows225C_971 : rowsJ 143 144 82 86 ≤ 0 := by decide +kernel

theorem rows225C_972 : rowsJ 143 144 86 91 ≤ 0 := by decide +kernel

theorem rows225C_973 : rowsJ 143 144 91 97 ≤ 352821548642 := by decide +kernel

theorem rows225C_974 : rowsJ 143 144 97 400 ≤ 715057027687605 := by decide +kernel

theorem rows225C_975 : rowsJ 144 145 0 61 ≤ 172785613025787 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_968
#print axioms SieveCert.rows225C_975
