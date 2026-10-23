/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 31–34 of 117

File 8 of 27: the parts `rows225R_31` … `rows225R_34` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 23038 tests: row 50 columns 0–45, row 50 columns 46–199, row 51 columns 0–45, row
51 columns 46–199), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
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

theorem rows225R_31 : rowsJ2 50 51 0 46 ≤ 2121181025976917 := by decide +kernel

theorem rows225R_32 : rowsJ2 50 51 46 200 ≤ 46155337532392 := by decide +kernel

theorem rows225R_33 : rowsJ2 51 52 0 46 ≤ 1990224239033889 := by decide +kernel

theorem rows225R_34 : rowsJ2 51 52 46 200 ≤ 43093062138730 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_31
#print axioms SieveCert.rows225R_34
