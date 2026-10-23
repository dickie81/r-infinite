/-
# Round 625: the certificate at `L = 9/4`, parts 1050–1057 of 1374

File 129 of 167: the parts `rows225C_1050` … `rows225C_1057` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54435 depth-4 tests: row 151 columns 96–399, row 152 columns 0–58, row 152
columns 59–64, row 152 columns 65–68, row 152 columns 69–72, row 152 columns 73–76, row 152 columns 77–81, row 152
columns 82–87), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1050 : rowsJ 151 152 96 400 ≤ 315413875702631 := by decide +kernel

theorem rows225C_1051 : rowsJ 152 153 0 59 ≤ 118481135444773 := by decide +kernel

theorem rows225C_1052 : rowsJ 152 153 59 65 ≤ 14489511295885 := by decide +kernel

theorem rows225C_1053 : rowsJ 152 153 65 69 ≤ 15856825786533 := by decide +kernel

theorem rows225C_1054 : rowsJ 152 153 69 73 ≤ 13177644063249 := by decide +kernel

theorem rows225C_1055 : rowsJ 152 153 73 77 ≤ 7758293701997 := by decide +kernel

theorem rows225C_1056 : rowsJ 152 153 77 82 ≤ 4339186062677 := by decide +kernel

theorem rows225C_1057 : rowsJ 152 153 82 88 ≤ 872036377381 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1050
#print axioms SieveCert.rows225C_1057
