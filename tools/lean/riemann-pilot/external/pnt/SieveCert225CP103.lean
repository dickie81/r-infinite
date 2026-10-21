/-
# Round 625: the certificate at `L = 9/4`, parts 834–841 of 1374

File 103 of 167: the parts `rows225C_834` … `rows225C_841` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 59781 depth-4 tests: row 131 columns 87–90, row 131 columns 91–94, row 131
columns 95–98, row 131 columns 99–103, row 131 columns 104–399, row 132 columns 0–39, row 132 columns 40–69, row 132
columns 70–74), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_834 : rowsJ 131 132 87 91 ≤ 0 := by decide +kernel

theorem rows225C_835 : rowsJ 131 132 91 95 ≤ 0 := by decide +kernel

theorem rows225C_836 : rowsJ 131 132 95 99 ≤ 1013026568407 := by decide +kernel

theorem rows225C_837 : rowsJ 131 132 99 104 ≤ 7441670428165 := by decide +kernel

theorem rows225C_838 : rowsJ 131 132 104 400 ≤ 1269306110541678 := by decide +kernel

theorem rows225C_839 : rowsJ 132 133 0 40 ≤ 212399192145547 := by decide +kernel

theorem rows225C_840 : rowsJ 132 133 40 70 ≤ 68736384552820 := by decide +kernel

theorem rows225C_841 : rowsJ 132 133 70 75 ≤ 139748844420 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_834
#print axioms SieveCert.rows225C_841
