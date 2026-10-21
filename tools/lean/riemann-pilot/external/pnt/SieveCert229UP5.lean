/-
# Round 623: the certificate at `L = 229/100`, parts 17–20 of 21 (rows 64 to 149)

File 5 of 5: the parts `rows229U_17` … `rows229U_20` of `SieveCert229U.lean`'s certificate on
`SieveGrid229U.grid229U` (4 parts, 86 rows, 6928 cells of depth 4 and candidate cells), each the sum of
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

theorem rows229U_17 : rows 64 67 ≤ 21161984720060148 := by decide +kernel

theorem rows229U_18 : rows 67 73 ≤ 46297274741570480 := by decide +kernel

theorem rows229U_19 : rows 73 145 ≤ 791083449266844160 := by decide +kernel

theorem rows229U_20 : rows 145 150 ≤ 119751883107505664 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows229U_17
#print axioms SieveCert.rows229U_20
