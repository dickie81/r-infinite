/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 87–90 of 503

File 22 of 127: the parts `rows2249R_87` … `rows2249R_90` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24188 tests: row 60 columns 0–34, row 60 columns 35–43, row 60 columns 44–56,
row 60 columns 57–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_87 : rowsJ2 60 61 0 35 ≤ 882257901157997 := by decide +kernel

theorem rows2249R_88 : rowsJ2 60 61 35 44 ≤ 442552620694259 := by decide +kernel

theorem rows2249R_89 : rowsJ2 60 61 44 57 ≤ 691052956040408 := by decide +kernel

theorem rows2249R_90 : rowsJ2 60 61 57 300 ≤ 148797704767203 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_87
#print axioms SieveCert.rows2249R_90
