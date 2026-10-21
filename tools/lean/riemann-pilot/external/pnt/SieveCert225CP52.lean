/-
# Round 625: the certificate at `L = 9/4`, parts 419–427 of 1374

File 52 of 167: the parts `rows225C_419` … `rows225C_427` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 57760 depth-4 tests: row 101 columns 53–74, row 101 columns 75–83, row 101
columns 84–87, row 101 columns 88–90, row 101 columns 91–93, row 101 columns 94–95, row 101 columns 96–97, row 101
columns 98–99, row 101 columns 100–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_419 : rowsJ 101 102 53 75 ≤ 287918456275359 := by decide +kernel

theorem rows225C_420 : rowsJ 101 102 75 84 ≤ 30662482290068 := by decide +kernel

theorem rows225C_421 : rowsJ 101 102 84 88 ≤ 3356862199022 := by decide +kernel

theorem rows225C_422 : rowsJ 101 102 88 91 ≤ 1942396934013 := by decide +kernel

theorem rows225C_423 : rowsJ 101 102 91 94 ≤ 4088915178094 := by decide +kernel

theorem rows225C_424 : rowsJ 101 102 94 96 ≤ 3461476117567 := by decide +kernel

theorem rows225C_425 : rowsJ 101 102 96 98 ≤ 3064959066422 := by decide +kernel

theorem rows225C_426 : rowsJ 101 102 98 100 ≤ 2688067102775 := by decide +kernel

theorem rows225C_427 : rowsJ 101 102 100 400 ≤ 2331867789756 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_419
#print axioms SieveCert.rows225C_427
