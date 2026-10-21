/-
# Round 625: the certificate at `L = 9/4`, parts 486–493 of 1374

File 60 of 167: the parts `rows225C_486` … `rows225C_493` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55395 depth-4 tests: row 106 columns 88–90, row 106 columns 91–92, row 106
columns 93–94, row 106 columns 95–97, row 106 columns 98–100, row 106 columns 101–103, row 106 columns 104–399, row
107 columns 0–34), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_486 : rowsJ 106 107 88 91 ≤ 1791257863044 := by decide +kernel

theorem rows225C_487 : rowsJ 106 107 91 93 ≤ 1994400061456 := by decide +kernel

theorem rows225C_488 : rowsJ 106 107 93 95 ≤ 1693978319780 := by decide +kernel

theorem rows225C_489 : rowsJ 106 107 95 98 ≤ 2024984460337 := by decide +kernel

theorem rows225C_490 : rowsJ 106 107 98 101 ≤ 1465223304537 := by decide +kernel

theorem rows225C_491 : rowsJ 106 107 101 104 ≤ 988748961085 := by decide +kernel

theorem rows225C_492 : rowsJ 106 107 104 400 ≤ 959782616804 := by decide +kernel

theorem rows225C_493 : rowsJ 107 108 0 35 ≤ 66243790018035 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_486
#print axioms SieveCert.rows225C_493
