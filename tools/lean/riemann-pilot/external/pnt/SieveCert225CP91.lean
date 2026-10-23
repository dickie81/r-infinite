/-
# Round 625: the certificate at `L = 9/4`, parts 734–742 of 1374

File 91 of 167: the parts `rows225C_734` … `rows225C_742` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59260 depth-4 tests: row 123 columns 107–111, row 123 columns 112–399, row 124
columns 0–34, row 124 columns 35–68, row 124 columns 69–74, row 124 columns 75–78, row 124 columns 79–81, row 124
columns 82–84, row 124 columns 85–87), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_734 : rowsJ 123 124 107 112 ≤ 19357524350107 := by decide +kernel

theorem rows225C_735 : rowsJ 123 124 112 400 ≤ 982276051567273 := by decide +kernel

theorem rows225C_736 : rowsJ 124 125 0 35 ≤ 126908673861981 := by decide +kernel

theorem rows225C_737 : rowsJ 124 125 35 69 ≤ 239474476285736 := by decide +kernel

theorem rows225C_738 : rowsJ 124 125 69 75 ≤ 0 := by decide +kernel

theorem rows225C_739 : rowsJ 124 125 75 79 ≤ 0 := by decide +kernel

theorem rows225C_740 : rowsJ 124 125 79 82 ≤ 0 := by decide +kernel

theorem rows225C_741 : rowsJ 124 125 82 85 ≤ 0 := by decide +kernel

theorem rows225C_742 : rowsJ 124 125 85 88 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_734
#print axioms SieveCert.rows225C_742
