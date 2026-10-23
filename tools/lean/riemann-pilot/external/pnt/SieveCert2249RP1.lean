/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 0–3 of 503

File 1 of 127: the parts `rows2249R_0` … `rows2249R_3` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27405 tests: rows 0–18, rows 19–22, rows 23–24, rows 25–26), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_0 : rows2 0 19 ≤ 6645266975185482 := by decide +kernel

theorem rows2249R_1 : rows2 19 23 ≤ 5220621028698829 := by decide +kernel

theorem rows2249R_2 : rows2 23 25 ≤ 3361896494924522 := by decide +kernel

theorem rows2249R_3 : rows2 25 27 ≤ 3891014381692228 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_0
#print axioms SieveCert.rows2249R_3
