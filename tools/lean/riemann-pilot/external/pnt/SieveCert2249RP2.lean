/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 4–8 of 503

File 2 of 127: the parts `rows2249R_4` … `rows2249R_8` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (5 parts, 24955 tests: rows 27–27, rows 28–28, rows 29–29, rows 30–30, rows 31–31), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_4 : rows2 27 28 ≤ 2139590986273868 := by decide +kernel

theorem rows2249R_5 : rows2 28 29 ≤ 2261027541869592 := by decide +kernel

theorem rows2249R_6 : rows2 29 30 ≤ 2373080572257734 := by decide +kernel

theorem rows2249R_7 : rows2 30 31 ≤ 2472690993567279 := by decide +kernel

theorem rows2249R_8 : rows2 31 32 ≤ 2556639088105023 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_4
#print axioms SieveCert.rows2249R_8
