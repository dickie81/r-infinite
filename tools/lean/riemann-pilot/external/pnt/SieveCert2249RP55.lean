/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 208–211 of 503

File 55 of 127: the parts `rows2249R_208` … `rows2249R_211` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24960 tests: row 86 columns 72–77, row 86 columns 78–84, row 86 columns 85–299,
row 87 columns 0–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_208 : rowsJ2 86 87 72 78 ≤ 1363739669157 := by decide +kernel

theorem rows2249R_209 : rowsJ2 86 87 78 85 ≤ 26163913531944 := by decide +kernel

theorem rows2249R_210 : rowsJ2 86 87 85 300 ≤ 17622667909187 := by decide +kernel

theorem rows2249R_211 : rowsJ2 87 88 0 43 ≤ 678057561807673 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_208
#print axioms SieveCert.rows2249R_211
