/-
# Round 625: the certificate at `L = 9/4`, parts 743–751 of 1374

File 92 of 167: the parts `rows225C_743` … `rows225C_751` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59008 depth-4 tests: row 124 columns 88–90, row 124 columns 91–93, row 124
columns 94–97, row 124 columns 98–101, row 124 columns 102–105, row 124 columns 106–110, row 124 columns 111–399,
row 125 columns 0–34, row 125 columns 35–68), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_743 : rowsJ 124 125 88 91 ≤ 0 := by decide +kernel

theorem rows225C_744 : rowsJ 124 125 91 94 ≤ 0 := by decide +kernel

theorem rows225C_745 : rowsJ 124 125 94 98 ≤ 179176226788 := by decide +kernel

theorem rows225C_746 : rowsJ 124 125 98 102 ≤ 2072634660714 := by decide +kernel

theorem rows225C_747 : rowsJ 124 125 102 106 ≤ 6312131428828 := by decide +kernel

theorem rows225C_748 : rowsJ 124 125 106 111 ≤ 17714291698045 := by decide +kernel

theorem rows225C_749 : rowsJ 124 125 111 400 ≤ 1169704372719475 := by decide +kernel

theorem rows225C_750 : rowsJ 125 126 0 35 ≤ 132974170730986 := by decide +kernel

theorem rows225C_751 : rowsJ 125 126 35 69 ≤ 222032500283346 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_743
#print axioms SieveCert.rows225C_751
