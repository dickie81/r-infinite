/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 216–219 of 503

File 57 of 127: the parts `rows2249R_216` … `rows2249R_219` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24923 tests: row 87 columns 78–84, row 87 columns 85–299, row 88 columns 0–47,
row 88 columns 48–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_216 : rowsJ2 87 88 78 85 ≤ 29395969793034 := by decide +kernel

theorem rows2249R_217 : rowsJ2 87 88 85 300 ≤ 31099319398812 := by decide +kernel

theorem rows2249R_218 : rowsJ2 88 89 0 48 ≤ 722168697937910 := by decide +kernel

theorem rows2249R_219 : rowsJ2 88 89 48 62 ≤ 29231315596450 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_216
#print axioms SieveCert.rows2249R_219
