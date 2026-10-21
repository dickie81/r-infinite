/-
# Round 625: the certificate at `L = 9/4`, parts 785–792 of 1374

File 97 of 167: the parts `rows225C_785` … `rows225C_792` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56202 depth-4 tests: row 127 columns 91–94, row 127 columns 95–98, row 127
columns 99–102, row 127 columns 103–107, row 127 columns 108–399, row 128 columns 0–36, row 128 columns 37–69, row
128 columns 70–74), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_785 : rowsJ 127 128 91 95 ≤ 0 := by decide +kernel

theorem rows225C_786 : rowsJ 127 128 95 99 ≤ 677612547628 := by decide +kernel

theorem rows225C_787 : rowsJ 127 128 99 103 ≤ 3841073253577 := by decide +kernel

theorem rows225C_788 : rowsJ 127 128 103 108 ≤ 13099301032506 := by decide +kernel

theorem rows225C_789 : rowsJ 127 128 108 400 ≤ 1438977315840433 := by decide +kernel

theorem rows225C_790 : rowsJ 128 129 0 37 ≤ 176505886074741 := by decide +kernel

theorem rows225C_791 : rowsJ 128 129 37 70 ≤ 144654570810583 := by decide +kernel

theorem rows225C_792 : rowsJ 128 129 70 75 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_785
#print axioms SieveCert.rows225C_792
