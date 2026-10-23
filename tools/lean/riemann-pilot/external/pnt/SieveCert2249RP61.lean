/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 231–234 of 503

File 61 of 127: the parts `rows2249R_231` … `rows2249R_234` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29919 tests: row 90 columns 0–52, row 90 columns 53–61, row 90 columns 62–66,
row 90 columns 67–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_231 : rowsJ2 90 91 0 53 ≤ 688717154358308 := by decide +kernel

theorem rows2249R_232 : rowsJ2 90 91 53 62 ≤ 303294947005 := by decide +kernel

theorem rows2249R_233 : rowsJ2 90 91 62 67 ≤ 88389583768 := by decide +kernel

theorem rows2249R_234 : rowsJ2 90 91 67 73 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_231
#print axioms SieveCert.rows2249R_234
