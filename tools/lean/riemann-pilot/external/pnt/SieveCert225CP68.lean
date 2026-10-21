/-
# Round 625: the certificate at `L = 9/4`, parts 549–555 of 1374

File 68 of 167: the parts `rows225C_549` … `rows225C_555` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (7 parts, 53016 depth-4 tests: row 111 columns 35–45, row 111 columns 46–73, row 111
columns 74–80, row 111 columns 81–84, row 111 columns 85–87, row 111 columns 88–90, row 111 columns 91–93), each a
sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_549 : rowsJ 111 112 35 46 ≤ 228027373518565 := by decide +kernel

theorem rows225C_550 : rowsJ 111 112 46 74 ≤ 263840334019728 := by decide +kernel

theorem rows225C_551 : rowsJ 111 112 74 81 ≤ 2970838055645 := by decide +kernel

theorem rows225C_552 : rowsJ 111 112 81 85 ≤ 14380407590 := by decide +kernel

theorem rows225C_553 : rowsJ 111 112 85 88 ≤ 462841543607 := by decide +kernel

theorem rows225C_554 : rowsJ 111 112 88 91 ≤ 1245111604532 := by decide +kernel

theorem rows225C_555 : rowsJ 111 112 91 94 ≤ 918084076644 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_549
#print axioms SieveCert.rows225C_555
