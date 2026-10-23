/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 103–106 of 117

File 24 of 27: the parts `rows225R_103` … `rows225R_106` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 27093 tests: rows 93–94, rows 95–96, rows 97–98, rows 99–100), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_103 : rows2 93 95 ≤ 7862234391735718 := by decide +kernel

theorem rows225R_104 : rows2 95 97 ≤ 7935038792728883 := by decide +kernel

theorem rows225R_105 : rows2 97 99 ≤ 8038357235312078 := by decide +kernel

theorem rows225R_106 : rows2 99 101 ≤ 8140446425714657 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_103
#print axioms SieveCert.rows225R_106
