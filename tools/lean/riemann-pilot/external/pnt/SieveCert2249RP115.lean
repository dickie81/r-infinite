/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 442–445 of 503

File 115 of 127: the parts `rows2249R_442` … `rows2249R_445` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 23594 tests: row 142 columns 0–41, row 142 columns 42–299, row 143 columns
0–41, row 143 columns 42–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_442 : rowsJ2 142 143 0 42 ≤ 133146044079290 := by decide +kernel

theorem rows2249R_443 : rowsJ2 142 143 42 300 ≤ 2376631746972497 := by decide +kernel

theorem rows2249R_444 : rowsJ2 143 144 0 42 ≤ 140366944913716 := by decide +kernel

theorem rows2249R_445 : rowsJ2 143 144 42 300 ≤ 2380186666281093 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_442
#print axioms SieveCert.rows2249R_445
