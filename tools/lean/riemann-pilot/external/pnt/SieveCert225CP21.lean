/-
# Round 625: the certificate at `L = 9/4`, parts 173–180 of 1374

File 21 of 167: the parts `rows225C_173` … `rows225C_180` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55386 depth-4 tests: row 71 columns 35–43, row 71 columns 44–49, row 71 columns
50–54, row 71 columns 55–58, row 71 columns 59–62, row 71 columns 63–67, row 71 columns 68–399, row 72 columns
0–34), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_173 : rowsJ 71 72 35 44 ≤ 86953916414859 := by decide +kernel

theorem rows225C_174 : rowsJ 71 72 44 50 ≤ 58505614471291 := by decide +kernel

theorem rows225C_175 : rowsJ 71 72 50 55 ≤ 92447445469175 := by decide +kernel

theorem rows225C_176 : rowsJ 71 72 55 59 ≤ 119371536635225 := by decide +kernel

theorem rows225C_177 : rowsJ 71 72 59 63 ≤ 143422727582607 := by decide +kernel

theorem rows225C_178 : rowsJ 71 72 63 68 ≤ 164581179135755 := by decide +kernel

theorem rows225C_179 : rowsJ 71 72 68 400 ≤ 119714580076409 := by decide +kernel

theorem rows225C_180 : rowsJ 72 73 0 35 ≤ 609998726940830 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_173
#print axioms SieveCert.rows225C_180
