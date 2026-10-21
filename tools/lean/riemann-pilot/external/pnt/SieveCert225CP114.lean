/-
# Round 625: the certificate at `L = 9/4`, parts 927–934 of 1374

File 114 of 167: the parts `rows225C_927` … `rows225C_934` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 57224 depth-4 tests: row 139 columns 78–81, row 139 columns 82–85, row 139
columns 86–89, row 139 columns 90–94, row 139 columns 95–100, row 139 columns 101–399, row 140 columns 0–60, row 140
columns 61–67), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_927 : rowsJ 139 140 78 82 ≤ 0 := by decide +kernel

theorem rows225C_928 : rowsJ 139 140 82 86 ≤ 0 := by decide +kernel

theorem rows225C_929 : rowsJ 139 140 86 90 ≤ 0 := by decide +kernel

theorem rows225C_930 : rowsJ 139 140 90 95 ≤ 0 := by decide +kernel

theorem rows225C_931 : rowsJ 139 140 95 101 ≤ 4989843998005 := by decide +kernel

theorem rows225C_932 : rowsJ 139 140 101 400 ≤ 902559394304157 := by decide +kernel

theorem rows225C_933 : rowsJ 140 141 0 61 ≤ 204363458754065 := by decide +kernel

theorem rows225C_934 : rowsJ 140 141 61 68 ≤ 7458826086087 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_927
#print axioms SieveCert.rows225C_934
