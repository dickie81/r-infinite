/-
# Round 625: the certificate at `L = 9/4`, parts 935–943 of 1374

File 115 of 167: the parts `rows225C_935` … `rows225C_943` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59396 depth-4 tests: row 140 columns 68–71, row 140 columns 72–74, row 140
columns 75–77, row 140 columns 78–81, row 140 columns 82–85, row 140 columns 86–89, row 140 columns 90–94, row 140
columns 95–100, row 140 columns 101–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_935 : rowsJ 140 141 68 72 ≤ 6143599330179 := by decide +kernel

theorem rows225C_936 : rowsJ 140 141 72 75 ≤ 3995473172082 := by decide +kernel

theorem rows225C_937 : rowsJ 140 141 75 78 ≤ 1996957321130 := by decide +kernel

theorem rows225C_938 : rowsJ 140 141 78 82 ≤ 195074493414 := by decide +kernel

theorem rows225C_939 : rowsJ 140 141 82 86 ≤ 0 := by decide +kernel

theorem rows225C_940 : rowsJ 140 141 86 90 ≤ 0 := by decide +kernel

theorem rows225C_941 : rowsJ 140 141 90 95 ≤ 0 := by decide +kernel

theorem rows225C_942 : rowsJ 140 141 95 101 ≤ 5247528317580 := by decide +kernel

theorem rows225C_943 : rowsJ 140 141 101 400 ≤ 904158385935665 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_935
#print axioms SieveCert.rows225C_943
