/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 4–8 of 117

File 2 of 27: the parts `rows225R_4` … `rows225R_8` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (5 parts, 24955 tests: rows 27–27, rows 28–28, rows 29–29, rows 30–30, rows 31–31), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_4 : rows2 27 28 ≤ 3644940783370340 := by decide +kernel

theorem rows225R_5 : rows2 28 29 ≤ 3554659412818889 := by decide +kernel

theorem rows225R_6 : rows2 29 30 ≤ 3487215012815202 := by decide +kernel

theorem rows225R_7 : rows2 30 31 ≤ 3456415704335813 := by decide +kernel

theorem rows225R_8 : rows2 31 32 ≤ 3472902705231406 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_4
#print axioms SieveCert.rows225R_8
