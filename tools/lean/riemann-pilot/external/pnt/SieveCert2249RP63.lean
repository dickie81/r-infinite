/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 239–242 of 503

File 63 of 127: the parts `rows2249R_239` … `rows2249R_242` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27724 tests: row 91 columns 62–66, row 91 columns 67–72, row 91 columns 73–79,
row 91 columns 80–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_239 : rowsJ2 91 92 62 67 ≤ 21885456794 := by decide +kernel

theorem rows2249R_240 : rowsJ2 91 92 67 73 ≤ 68619394427 := by decide +kernel

theorem rows2249R_241 : rowsJ2 91 92 73 80 ≤ 12113890159077 := by decide +kernel

theorem rows2249R_242 : rowsJ2 91 92 80 300 ≤ 870910925548995 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_239
#print axioms SieveCert.rows2249R_242
