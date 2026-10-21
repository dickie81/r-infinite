/-
# Round 625: the certificate at `L = 9/4`, parts 386–393 of 1374

File 48 of 167: the parts `rows225C_386` … `rows225C_393` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 57307 depth-4 tests: row 98 columns 52–64, row 98 columns 65–83, row 98 columns
84–88, row 98 columns 89–91, row 98 columns 92–94, row 98 columns 95–96, row 98 columns 97–399, row 99 columns
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

theorem rows225C_386 : rowsJ 98 99 52 65 ≤ 250280945164870 := by decide +kernel

theorem rows225C_387 : rowsJ 98 99 65 84 ≤ 151933228159051 := by decide +kernel

theorem rows225C_388 : rowsJ 98 99 84 89 ≤ 8963175492694 := by decide +kernel

theorem rows225C_389 : rowsJ 98 99 89 92 ≤ 3435252017205 := by decide +kernel

theorem rows225C_390 : rowsJ 98 99 92 95 ≤ 5126745341408 := by decide +kernel

theorem rows225C_391 : rowsJ 98 99 95 97 ≤ 4754810269340 := by decide +kernel

theorem rows225C_392 : rowsJ 98 99 97 400 ≤ 4290414301802 := by decide +kernel

theorem rows225C_393 : rowsJ 99 100 0 35 ≤ 111826255861217 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_386
#print axioms SieveCert.rows225C_393
