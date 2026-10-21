/-
# Round 625: the certificate at `L = 9/4`, parts 494–501 of 1374

File 61 of 167: the parts `rows225C_494` … `rows225C_501` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 57563 depth-4 tests: row 107 columns 35–44, row 107 columns 45–60, row 107
columns 61–80, row 107 columns 81–84, row 107 columns 85–87, row 107 columns 88–90, row 107 columns 91–92, row 107
columns 93–95), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_494 : rowsJ 107 108 35 45 ≤ 198208119559540 := by decide +kernel

theorem rows225C_495 : rowsJ 107 108 45 61 ≤ 270979769756137 := by decide +kernel

theorem rows225C_496 : rowsJ 107 108 61 81 ≤ 99441393333686 := by decide +kernel

theorem rows225C_497 : rowsJ 107 108 81 85 ≤ 373416569620 := by decide +kernel

theorem rows225C_498 : rowsJ 107 108 85 88 ≤ 474918787256 := by decide +kernel

theorem rows225C_499 : rowsJ 107 108 88 91 ≤ 1779239276176 := by decide +kernel

theorem rows225C_500 : rowsJ 107 108 91 93 ≤ 1666858965754 := by decide +kernel

theorem rows225C_501 : rowsJ 107 108 93 96 ≤ 1993207819407 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_494
#print axioms SieveCert.rows225C_501
