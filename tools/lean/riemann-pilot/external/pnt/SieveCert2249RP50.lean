/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 189–192 of 503

File 50 of 127: the parts `rows2249R_189` … `rows2249R_192` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29008 tests: row 83 columns 68–72, row 83 columns 73–78, row 83 columns 79–299,
row 84 columns 0–37), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_189 : rowsJ2 83 84 68 73 ≤ 3563796964055 := by decide +kernel

theorem rows2249R_190 : rowsJ2 83 84 73 79 ≤ 2048950173085 := by decide +kernel

theorem rows2249R_191 : rowsJ2 83 84 79 300 ≤ 11949028256469 := by decide +kernel

theorem rows2249R_192 : rowsJ2 84 85 0 38 ≤ 586010943202239 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_189
#print axioms SieveCert.rows2249R_192
