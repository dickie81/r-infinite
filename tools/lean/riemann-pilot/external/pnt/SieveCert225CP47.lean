/-
# Round 625: the certificate at `L = 9/4`, parts 378–385 of 1374

File 47 of 167: the parts `rows225C_378` … `rows225C_385` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55458 depth-4 tests: row 97 columns 82–87, row 97 columns 88–90, row 97 columns
91–93, row 97 columns 94–95, row 97 columns 96–399, row 98 columns 0–34, row 98 columns 35–43, row 98 columns
44–51), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_378 : rowsJ 97 98 82 88 ≤ 16464382536977 := by decide +kernel

theorem rows225C_379 : rowsJ 97 98 88 91 ≤ 4478645415861 := by decide +kernel

theorem rows225C_380 : rowsJ 97 98 91 94 ≤ 4556025452342 := by decide +kernel

theorem rows225C_381 : rowsJ 97 98 94 96 ≤ 4516832242670 := by decide +kernel

theorem rows225C_382 : rowsJ 97 98 96 400 ≤ 5072535179679 := by decide +kernel

theorem rows225C_383 : rowsJ 98 99 0 35 ≤ 121240751055695 := by decide +kernel

theorem rows225C_384 : rowsJ 98 99 35 44 ≤ 108259715534796 := by decide +kernel

theorem rows225C_385 : rowsJ 98 99 44 52 ≤ 212429835063036 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_378
#print axioms SieveCert.rows225C_385
