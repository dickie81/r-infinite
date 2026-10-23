/-
# Round 625: the certificate at `L = 9/4`, parts 502–509 of 1374

File 62 of 167: the parts `rows225C_502` … `rows225C_509` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 59478 depth-4 tests: row 107 columns 96–98, row 107 columns 99–101, row 107
columns 102–104, row 107 columns 105–399, row 108 columns 0–34, row 108 columns 35–44, row 108 columns 45–63, row
108 columns 64–80), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_502 : rowsJ 107 108 96 99 ≤ 1443331759962 := by decide +kernel

theorem rows225C_503 : rowsJ 107 108 99 102 ≤ 973943593516 := by decide +kernel

theorem rows225C_504 : rowsJ 107 108 102 105 ≤ 677945536438 := by decide +kernel

theorem rows225C_505 : rowsJ 107 108 105 400 ≤ 1223444563622 := by decide +kernel

theorem rows225C_506 : rowsJ 108 109 0 35 ≤ 64236533068265 := by decide +kernel

theorem rows225C_507 : rowsJ 108 109 35 45 ≤ 201505689232290 := by decide +kernel

theorem rows225C_508 : rowsJ 108 109 45 64 ≤ 286862448549591 := by decide +kernel

theorem rows225C_509 : rowsJ 108 109 64 81 ≤ 61716000631628 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_502
#print axioms SieveCert.rows225C_509
