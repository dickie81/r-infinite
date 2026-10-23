/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 17–20 of 117

File 5 of 27: the parts `rows225R_17` … `rows225R_20` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 27906 tests: rows 40–40, rows 41–41, rows 42–42, rows 43–43), each a sum of
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

theorem rows225R_17 : rows2 40 41 ≤ 3383844546147500 := by decide +kernel

theorem rows225R_18 : rows2 41 42 ≤ 3299955682258033 := by decide +kernel

theorem rows225R_19 : rows2 42 43 ≤ 3208248352096264 := by decide +kernel

theorem rows225R_20 : rows2 43 44 ≤ 3096736358257280 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_17
#print axioms SieveCert.rows225R_20
