/-
# Round 625: the certificate at `L = 9/4`, parts 428–435 of 1374

File 53 of 167: the parts `rows225C_428` … `rows225C_435` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56181 depth-4 tests: row 102 columns 0–34, row 102 columns 35–43, row 102 columns
44–52, row 102 columns 53–76, row 102 columns 77–83, row 102 columns 84–87, row 102 columns 88–90, row 102 columns
91–92), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_428 : rowsJ 102 103 0 35 ≤ 88633168395023 := by decide +kernel

theorem rows225C_429 : rowsJ 102 103 35 44 ≤ 140285686079050 := by decide +kernel

theorem rows225C_430 : rowsJ 102 103 44 53 ≤ 218016076496463 := by decide +kernel

theorem rows225C_431 : rowsJ 102 103 53 77 ≤ 282144898034687 := by decide +kernel

theorem rows225C_432 : rowsJ 102 103 77 84 ≤ 17195444617854 := by decide +kernel

theorem rows225C_433 : rowsJ 102 103 84 88 ≤ 2255134138690 := by decide +kernel

theorem rows225C_434 : rowsJ 102 103 88 91 ≤ 1839928340322 := by decide +kernel

theorem rows225C_435 : rowsJ 102 103 91 93 ≤ 2407059994254 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_428
#print axioms SieveCert.rows225C_435
