/-
# Round 625: the certificate at `L = 9/4`, parts 901–908 of 1374

File 111 of 167: the parts `rows225C_901` … `rows225C_908` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54538 depth-4 tests: row 137 columns 69–72, row 137 columns 73–75, row 137
columns 76–78, row 137 columns 79–81, row 137 columns 82–85, row 137 columns 86–89, row 137 columns 90–94, row 137
columns 95–99), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_901 : rowsJ 137 138 69 73 ≤ 3649784677047 := by decide +kernel

theorem rows225C_902 : rowsJ 137 138 73 76 ≤ 1350107797620 := by decide +kernel

theorem rows225C_903 : rowsJ 137 138 76 79 ≤ 0 := by decide +kernel

theorem rows225C_904 : rowsJ 137 138 79 82 ≤ 0 := by decide +kernel

theorem rows225C_905 : rowsJ 137 138 82 86 ≤ 0 := by decide +kernel

theorem rows225C_906 : rowsJ 137 138 86 90 ≤ 0 := by decide +kernel

theorem rows225C_907 : rowsJ 137 138 90 95 ≤ 0 := by decide +kernel

theorem rows225C_908 : rowsJ 137 138 95 100 ≤ 2797707193020 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_901
#print axioms SieveCert.rows225C_908
