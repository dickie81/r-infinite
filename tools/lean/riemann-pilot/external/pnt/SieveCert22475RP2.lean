/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 4–8 of 534

File 2 of 135: the parts `rows22475R_4` … `rows22475R_8` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (5 parts, 24955 tests: rows 27–27, rows 28–28, rows 29–29, rows 30–30, rows 31–31),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_4 : rows2 27 28 ≤ 2327337219238475 := by decide +kernel

theorem rows22475R_5 : rows2 28 29 ≤ 2466231843252617 := by decide +kernel

theorem rows22475R_6 : rows2 29 30 ≤ 2597692526901394 := by decide +kernel

theorem rows22475R_7 : rows2 30 31 ≤ 2718705232390573 := by decide +kernel

theorem rows22475R_8 : rows2 31 32 ≤ 2826127654434830 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_4
#print axioms SieveCert.rows22475R_8
