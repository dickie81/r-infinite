/-
# Round 625: the certificate at `L = 9/4`, parts 984–991 of 1374

File 121 of 167: the parts `rows225C_984` … `rows225C_991` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 57942 depth-4 tests: row 144 columns 97–399, row 145 columns 0–60, row 145
columns 61–66, row 145 columns 67–70, row 145 columns 71–74, row 145 columns 75–78, row 145 columns 79–82, row 145
columns 83–87), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_984 : rowsJ 144 145 97 400 ≤ 716229216022490 := by decide +kernel

theorem rows225C_985 : rowsJ 145 146 0 61 ≤ 165922739206509 := by decide +kernel

theorem rows225C_986 : rowsJ 145 146 61 67 ≤ 10267345743989 := by decide +kernel

theorem rows225C_987 : rowsJ 145 146 67 71 ≤ 10279521838048 := by decide +kernel

theorem rows225C_988 : rowsJ 145 146 71 75 ≤ 9417103419538 := by decide +kernel

theorem rows225C_989 : rowsJ 145 146 75 79 ≤ 4975026828980 := by decide +kernel

theorem rows225C_990 : rowsJ 145 146 79 83 ≤ 1770702846292 := by decide +kernel

theorem rows225C_991 : rowsJ 145 146 83 88 ≤ 100462344894 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_984
#print axioms SieveCert.rows225C_991
