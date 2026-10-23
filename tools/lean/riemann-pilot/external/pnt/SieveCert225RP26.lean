/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 111–113 of 117

File 26 of 27: the parts `rows225R_111` … `rows225R_113` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (3 parts, 22270 tests: rows 124–132, rows 133–140, rows 141–147), each a sum of refined
costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_111 : rows2 124 133 ≤ 103629657377542447 := by decide +kernel

theorem rows225R_112 : rows2 133 141 ≤ 109465805747412663 := by decide +kernel

theorem rows225R_113 : rows2 141 148 ≤ 107976611754889793 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_111
#print axioms SieveCert.rows225R_113
