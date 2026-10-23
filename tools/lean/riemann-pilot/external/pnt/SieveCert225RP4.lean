/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 13–16 of 117

File 4 of 27: the parts `rows225R_13` … `rows225R_16` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 29600 tests: rows 36–36, rows 37–37, rows 38–38, rows 39–39), each a sum of
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

theorem rows225R_13 : rows2 36 37 ≤ 3549294749344004 := by decide +kernel

theorem rows225R_14 : rows2 37 38 ≤ 3527071929028784 := by decide +kernel

theorem rows225R_15 : rows2 38 39 ≤ 3497452180910227 := by decide +kernel

theorem rows225R_16 : rows2 39 40 ≤ 3444642433529128 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_13
#print axioms SieveCert.rows225R_16
