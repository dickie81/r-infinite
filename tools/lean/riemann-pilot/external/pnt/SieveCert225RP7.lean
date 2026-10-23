/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 25–30 of 117

File 7 of 27: the parts `rows225R_25` … `rows225R_30` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (6 parts, 28784 tests: row 47 columns 0–45, row 47 columns 46–199, row 48 columns 0–45, row
48 columns 46–199, row 49 columns 0–45, row 49 columns 46–199), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_25 : rowsJ2 47 48 0 46 ≤ 2539366449781935 := by decide +kernel

theorem rows225R_26 : rowsJ2 47 48 46 200 ≤ 25912602420768 := by decide +kernel

theorem rows225R_27 : rowsJ2 48 49 0 46 ≤ 2396020037920895 := by decide +kernel

theorem rows225R_28 : rowsJ2 48 49 46 200 ≤ 36023865004384 := by decide +kernel

theorem rows225R_29 : rowsJ2 49 50 0 46 ≤ 2251781186769424 := by decide +kernel

theorem rows225R_30 : rowsJ2 49 50 46 200 ≤ 42981412156667 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_25
#print axioms SieveCert.rows225R_30
