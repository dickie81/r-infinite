/-
# Round 625: the certificate at `L = 9/4`, parts 64–71 of 1374

File 8 of 167: the parts `rows225C_64` … `rows225C_71` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 58520 depth-4 tests: row 54 columns 0–34, row 54 columns 35–43, row 54 columns
44–49, row 54 columns 50–399, row 55 columns 0–34, row 55 columns 35–43, row 55 columns 44–49, row 55 columns
50–54), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_64 : rowsJ 54 55 0 35 ≤ 994595277876477 := by decide +kernel

theorem rows225C_65 : rowsJ 54 55 35 44 ≤ 322919948793828 := by decide +kernel

theorem rows225C_66 : rowsJ 54 55 44 50 ≤ 135657129430832 := by decide +kernel

theorem rows225C_67 : rowsJ 54 55 50 400 ≤ 98454809641200 := by decide +kernel

theorem rows225C_68 : rowsJ 55 56 0 35 ≤ 976311964575751 := by decide +kernel

theorem rows225C_69 : rowsJ 55 56 35 44 ≤ 304313247469484 := by decide +kernel

theorem rows225C_70 : rowsJ 55 56 44 50 ≤ 127147980837587 := by decide +kernel

theorem rows225C_71 : rowsJ 55 56 50 55 ≤ 94587416416068 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_64
#print axioms SieveCert.rows225C_71
