/-
# Round 625: the certificate at `L = 9/4`, parts 436–444 of 1374

File 54 of 167: the parts `rows225C_436` … `rows225C_444` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 57385 depth-4 tests: row 102 columns 93–94, row 102 columns 95–96, row 102
columns 97–98, row 102 columns 99–101, row 102 columns 102–399, row 103 columns 0–34, row 103 columns 35–43, row 103
columns 44–53, row 103 columns 54–77), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_436 : rowsJ 102 103 93 95 ≤ 3209542433652 := by decide +kernel

theorem rows225C_437 : rowsJ 102 103 95 97 ≤ 2828440402160 := by decide +kernel

theorem rows225C_438 : rowsJ 102 103 97 99 ≤ 2467118278715 := by decide +kernel

theorem rows225C_439 : rowsJ 102 103 99 102 ≤ 3069174727517 := by decide +kernel

theorem rows225C_440 : rowsJ 102 103 102 400 ≤ 863014859086 := by decide +kernel

theorem rows225C_441 : rowsJ 103 104 0 35 ≤ 82529278975031 := by decide +kernel

theorem rows225C_442 : rowsJ 103 104 35 44 ≤ 148895396034001 := by decide +kernel

theorem rows225C_443 : rowsJ 103 104 44 54 ≤ 230860444331786 := by decide +kernel

theorem rows225C_444 : rowsJ 103 104 54 78 ≤ 250198328841503 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_436
#print axioms SieveCert.rows225C_444
