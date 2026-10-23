/-
# Round 625: the certificate at `L = 9/4`, parts 760–768 of 1374

File 94 of 167: the parts `rows225C_760` … `rows225C_768` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59183 depth-4 tests: row 125 columns 98–101, row 125 columns 102–106, row 125
columns 107–111, row 125 columns 112–399, row 126 columns 0–35, row 126 columns 36–69, row 126 columns 70–74, row
126 columns 75–78, row 126 columns 79–81), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_760 : rowsJ 125 126 98 102 ≤ 2330231491833 := by decide +kernel

theorem rows225C_761 : rowsJ 125 126 102 107 ≤ 9533086467535 := by decide +kernel

theorem rows225C_762 : rowsJ 125 126 107 112 ≤ 21662240674533 := by decide +kernel

theorem rows225C_763 : rowsJ 125 126 112 400 ≤ 1248073677169097 := by decide +kernel

theorem rows225C_764 : rowsJ 126 127 0 36 ≤ 154611650040470 := by decide +kernel

theorem rows225C_765 : rowsJ 126 127 36 70 ≤ 188549214106528 := by decide +kernel

theorem rows225C_766 : rowsJ 126 127 70 75 ≤ 0 := by decide +kernel

theorem rows225C_767 : rowsJ 126 127 75 79 ≤ 0 := by decide +kernel

theorem rows225C_768 : rowsJ 126 127 79 82 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_760
#print axioms SieveCert.rows225C_768
