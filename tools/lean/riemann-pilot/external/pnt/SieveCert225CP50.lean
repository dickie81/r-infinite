/-
# Round 625: the certificate at `L = 9/4`, parts 402–409 of 1374

File 50 of 167: the parts `rows225C_402` … `rows225C_409` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55608 depth-4 tests: row 99 columns 96–97, row 99 columns 98–399, row 100 columns
0–34, row 100 columns 35–43, row 100 columns 44–51, row 100 columns 52–67, row 100 columns 68–83, row 100 columns
84–87), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_402 : rowsJ 99 100 96 98 ≤ 4001567706224 := by decide +kernel

theorem rows225C_403 : rowsJ 99 100 98 400 ≤ 3573794588510 := by decide +kernel

theorem rows225C_404 : rowsJ 100 101 0 35 ≤ 103288451529682 := by decide +kernel

theorem rows225C_405 : rowsJ 100 101 35 44 ≤ 123730517316187 := by decide +kernel

theorem rows225C_406 : rowsJ 100 101 44 52 ≤ 206642822271766 := by decide +kernel

theorem rows225C_407 : rowsJ 100 101 52 68 ≤ 266408326458475 := by decide +kernel

theorem rows225C_408 : rowsJ 100 101 68 84 ≤ 94255960531274 := by decide +kernel

theorem rows225C_409 : rowsJ 100 101 84 88 ≤ 4678681507587 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_402
#print axioms SieveCert.rows225C_409
