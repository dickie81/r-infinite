/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 369–372 of 503

File 97 of 127: the parts `rows2249R_369` … `rows2249R_372` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 25771 tests: row 117 columns 0–48, row 117 columns 49–56, row 117 columns
57–67, row 117 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_369 : rowsJ2 117 118 0 49 ≤ 203787065844761 := by decide +kernel

theorem rows2249R_370 : rowsJ2 117 118 49 57 ≤ 52179127713755 := by decide +kernel

theorem rows2249R_371 : rowsJ2 117 118 57 68 ≤ 8703051265867 := by decide +kernel

theorem rows2249R_372 : rowsJ2 117 118 68 300 ≤ 220687880255994 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_369
#print axioms SieveCert.rows2249R_372
