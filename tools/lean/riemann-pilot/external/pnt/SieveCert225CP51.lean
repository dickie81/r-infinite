/-
# Round 625: the certificate at `L = 9/4`, parts 410–418 of 1374

File 51 of 167: the parts `rows225C_410` … `rows225C_418` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 56743 depth-4 tests: row 100 columns 88–90, row 100 columns 91–93, row 100
columns 94–95, row 100 columns 96–97, row 100 columns 98–99, row 100 columns 100–399, row 101 columns 0–34, row 101
columns 35–43, row 101 columns 44–52), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_410 : rowsJ 100 101 88 91 ≤ 2221525132646 := by decide +kernel

theorem rows225C_411 : rowsJ 100 101 91 94 ≤ 4115933129678 := by decide +kernel

theorem rows225C_412 : rowsJ 100 101 94 96 ≤ 3939203733260 := by decide +kernel

theorem rows225C_413 : rowsJ 100 101 96 98 ≤ 3516969596662 := by decide +kernel

theorem rows225C_414 : rowsJ 100 101 98 100 ≤ 3114324427244 := by decide +kernel

theorem rows225C_415 : rowsJ 100 101 100 400 ≤ 1411651829854 := by decide +kernel

theorem rows225C_416 : rowsJ 101 102 0 35 ≤ 95490416416884 := by decide +kernel

theorem rows225C_417 : rowsJ 101 102 35 44 ≤ 131902005702177 := by decide +kernel

theorem rows225C_418 : rowsJ 101 102 44 53 ≤ 224489319655752 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_410
#print axioms SieveCert.rows225C_418
