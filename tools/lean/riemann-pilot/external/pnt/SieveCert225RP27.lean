/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 114–116 of 117

File 27 of 27: the parts `rows225R_114` … `rows225R_116` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (3 parts, 16952 tests: rows 148–156, rows 157–196, rows 197–199), each a sum of refined
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

theorem rows225R_114 : rows2 148 157 ≤ 143504583674496024 := by decide +kernel

theorem rows225R_115 : rows2 157 197 ≤ 168127093980058703 := by decide +kernel

theorem rows225R_116 : rows2 197 200 ≤ 67747903085194760 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_114
#print axioms SieveCert.rows225R_116
