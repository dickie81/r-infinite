/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 97–102 of 117

File 23 of 27: the parts `rows225R_97` … `rows225R_102` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (6 parts, 29369 tests: rows 87–87, rows 88–88, rows 89–89, rows 90–90, rows 91–91, rows
92–92), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_97 : rows2 87 88 ≤ 3592902072638277 := by decide +kernel

theorem rows225R_98 : rows2 88 89 ≤ 3930744142869655 := by decide +kernel

theorem rows225R_99 : rows2 89 90 ≤ 3923966895558975 := by decide +kernel

theorem rows225R_100 : rows2 90 91 ≤ 3911721878027483 := by decide +kernel

theorem rows225R_101 : rows2 91 92 ≤ 3914425132161558 := by decide +kernel

theorem rows225R_102 : rows2 92 93 ≤ 3929205869928500 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_97
#print axioms SieveCert.rows225R_102
