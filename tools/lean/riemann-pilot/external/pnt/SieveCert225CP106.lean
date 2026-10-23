/-
# Round 625: the certificate at `L = 9/4`, parts 859–866 of 1374

File 106 of 167: the parts `rows225C_859` … `rows225C_866` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56266 depth-4 tests: row 133 columns 90–93, row 133 columns 94–98, row 133
columns 99–103, row 133 columns 104–399, row 134 columns 0–47, row 134 columns 48–69, row 134 columns 70–73, row 134
columns 74–76), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_859 : rowsJ 133 134 90 94 ≤ 0 := by decide +kernel

theorem rows225C_860 : rowsJ 133 134 94 99 ≤ 1195468619299 := by decide +kernel

theorem rows225C_861 : rowsJ 133 134 99 104 ≤ 8456043415526 := by decide +kernel

theorem rows225C_862 : rowsJ 133 134 104 400 ≤ 1177202156348055 := by decide +kernel

theorem rows225C_863 : rowsJ 134 135 0 48 ≤ 249047472177256 := by decide +kernel

theorem rows225C_864 : rowsJ 134 135 48 70 ≤ 13818103084624 := by decide +kernel

theorem rows225C_865 : rowsJ 134 135 70 74 ≤ 960354231748 := by decide +kernel

theorem rows225C_866 : rowsJ 134 135 74 77 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_859
#print axioms SieveCert.rows225C_866
