/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 93–96 of 117

File 22 of 27: the parts `rows225R_93` … `rows225R_96` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 24794 tests: rows 83–83, rows 84–84, rows 85–85, rows 86–86), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_93 : rows2 83 84 ≤ 2250785783202011 := by decide +kernel

theorem rows225R_94 : rows2 84 85 ≤ 2603972738149286 := by decide +kernel

theorem rows225R_95 : rows2 85 86 ≤ 2941926267115184 := by decide +kernel

theorem rows225R_96 : rows2 86 87 ≤ 3284801468944252 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_93
#print axioms SieveCert.rows225R_96
