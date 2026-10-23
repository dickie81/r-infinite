/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 204–207 of 503

File 54 of 127: the parts `rows2249R_204` … `rows2249R_207` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28628 tests: row 86 columns 0–39, row 86 columns 40–61, row 86 columns 62–66,
row 86 columns 67–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_204 : rowsJ2 86 87 0 40 ≤ 625862653960109 := by decide +kernel

theorem rows2249R_205 : rowsJ2 86 87 40 62 ≤ 194145351944368 := by decide +kernel

theorem rows2249R_206 : rowsJ2 86 87 62 67 ≤ 965160971448 := by decide +kernel

theorem rows2249R_207 : rowsJ2 86 87 67 72 ≤ 1079446977542 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_204
#print axioms SieveCert.rows2249R_207
