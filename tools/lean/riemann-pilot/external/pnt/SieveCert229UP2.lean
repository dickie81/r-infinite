/-
# Round 623: the certificate at `L = 229/100`, parts 4–8 of 21 (rows 25 to 34)

File 2 of 5: the parts `rows229U_4` … `rows229U_8` of `SieveCert229U.lean`'s certificate on
`SieveGrid229U.grid229U` (5 parts, 10 rows, 9494 cells of depth 4 and candidate cells), each the sum of
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

theorem rows229U_4 : rows 25 27 ≤ 5193167923341586 := by decide +kernel

theorem rows229U_5 : rows 27 29 ≤ 5050271711197417 := by decide +kernel

theorem rows229U_6 : rows 29 31 ≤ 4609787955373855 := by decide +kernel

theorem rows229U_7 : rows 31 33 ≤ 4038443214186510 := by decide +kernel

theorem rows229U_8 : rows 33 35 ≤ 3583737472663864 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows229U_4
#print axioms SieveCert.rows229U_8
