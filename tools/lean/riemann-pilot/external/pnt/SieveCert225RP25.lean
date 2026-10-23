/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 107–110 of 117

File 25 of 27: the parts `rows225R_107` … `rows225R_110` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 29942 tests: rows 101–103, rows 104–107, rows 108–113, rows 114–123), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_107 : rows2 101 104 ≤ 12481500476192790 := by decide +kernel

theorem rows225R_108 : rows2 104 108 ≤ 20292321680518464 := by decide +kernel

theorem rows225R_109 : rows2 108 114 ≤ 39836179397407859 := by decide +kernel

theorem rows225R_110 : rows2 114 124 ≤ 91557533083357510 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_107
#print axioms SieveCert.rows225R_110
