/-
# Round 625: the certificate at `L = 9/4`, parts 445–453 of 1374

File 55 of 167: the parts `rows225C_445` … `rows225C_453` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 55091 depth-4 tests: row 103 columns 78–83, row 103 columns 84–87, row 103
columns 88–90, row 103 columns 91–92, row 103 columns 93–94, row 103 columns 95–96, row 103 columns 97–99, row 103
columns 100–102, row 103 columns 103–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_445 : rowsJ 103 104 78 84 ≤ 10900017673001 := by decide +kernel

theorem rows225C_446 : rowsJ 103 104 84 88 ≤ 1386040479618 := by decide +kernel

theorem rows225C_447 : rowsJ 103 104 88 91 ≤ 1827815961106 := by decide +kernel

theorem rows225C_448 : rowsJ 103 104 91 93 ≤ 2390760204716 := by decide +kernel

theorem rows225C_449 : rowsJ 103 104 93 95 ≤ 2783927786167 := by decide +kernel

theorem rows225C_450 : rowsJ 103 104 95 97 ≤ 2427760196809 := by decide +kernel

theorem rows225C_451 : rowsJ 103 104 97 100 ≤ 3020654621137 := by decide +kernel

theorem rows225C_452 : rowsJ 103 104 100 103 ≤ 2332039731287 := by decide +kernel

theorem rows225C_453 : rowsJ 103 104 103 400 ≤ 638624028696 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_445
#print axioms SieveCert.rows225C_453
