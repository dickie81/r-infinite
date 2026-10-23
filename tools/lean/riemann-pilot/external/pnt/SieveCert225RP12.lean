/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 47–50 of 117

File 12 of 27: the parts `rows225R_47` … `rows225R_50` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 28579 tests: row 58 columns 0–45, row 58 columns 46–199, row 59 columns 0–45, row
59 columns 46–199), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_47 : rowsJ2 58 59 0 46 ≤ 1290379867075088 := by decide +kernel

theorem rows225R_48 : rowsJ2 58 59 46 200 ≤ 528910566934427 := by decide +kernel

theorem rows225R_49 : rowsJ2 59 60 0 46 ≤ 1207927951181024 := by decide +kernel

theorem rows225R_50 : rowsJ2 59 60 46 200 ≤ 833794424458815 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_47
#print axioms SieveCert.rows225R_50
