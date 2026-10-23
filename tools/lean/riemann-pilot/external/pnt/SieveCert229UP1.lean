/-
# Round 623: the certificate at `L = 229/100`, parts 0–3 of 21 (rows 0 to 24)

File 1 of 5: the parts `rows229U_0` … `rows229U_3` of `SieveCert229U.lean`'s certificate on
`SieveGrid229U.grid229U` (4 parts, 25 rows, 8545 cells of depth 4 and candidate cells), each the sum of
the costs of its rows (`rows`, `SieveCertDefs.lean`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid229U.lean`.
-/
import SieveGrid229U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid229U

theorem rows229U_0 : rows 0 14 ≤ 15026459309741714 := by decide +kernel

theorem rows229U_1 : rows 14 20 ≤ 11031574565539238 := by decide +kernel

theorem rows229U_2 : rows 20 23 ≤ 6327160485386492 := by decide +kernel

theorem rows229U_3 : rows 23 25 ≤ 4995172175031701 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows229U_0
#print axioms SieveCert.rows229U_3
