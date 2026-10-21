/-
# Round 625: the certificate at `L = 9/4`, parts 1229–1236 of 1374

File 151 of 167: the parts `rows225C_1229` … `rows225C_1236` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 59077 depth-4 tests: row 177 columns 0–50, row 177 columns 51–56, row 177 columns
57–62, row 177 columns 63–69, row 177 columns 70–399, row 178 columns 0–50, row 178 columns 51–56, row 178 columns
57–62), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_1229 : rowsJ 177 178 0 51 ≤ 32598141914547 := by decide +kernel

theorem rows225C_1230 : rowsJ 177 178 51 57 ≤ 33952025064063 := by decide +kernel

theorem rows225C_1231 : rowsJ 177 178 57 63 ≤ 26282486479770 := by decide +kernel

theorem rows225C_1232 : rowsJ 177 178 63 70 ≤ 10517205695623 := by decide +kernel

theorem rows225C_1233 : rowsJ 177 178 70 400 ≤ 1813635500550599 := by decide +kernel

theorem rows225C_1234 : rowsJ 178 179 0 51 ≤ 32977652439332 := by decide +kernel

theorem rows225C_1235 : rowsJ 178 179 51 57 ≤ 35522792890496 := by decide +kernel

theorem rows225C_1236 : rowsJ 178 179 57 63 ≤ 24916989505488 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1229
#print axioms SieveCert.rows225C_1236
