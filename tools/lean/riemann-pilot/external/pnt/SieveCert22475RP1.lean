/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 0–3 of 534

File 1 of 135: the parts `rows22475R_0` … `rows22475R_3` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27405 tests: rows 0–18, rows 19–22, rows 23–24, rows 25–26), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_0 : rows2 0 19 ≤ 7252912142694264 := by decide +kernel

theorem rows22475R_1 : rows2 19 23 ≤ 5671324892676432 := by decide +kernel

theorem rows22475R_2 : rows2 23 25 ≤ 3645873301656217 := by decide +kernel

theorem rows22475R_3 : rows2 25 27 ≤ 4221866110537697 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_0
#print axioms SieveCert.rows22475R_3
