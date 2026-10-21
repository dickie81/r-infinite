/-
# Round 623: the certificate at `L = 229/100`, parts 9–12 of 21 (rows 35 to 48)

File 3 of 5: the parts `rows229U_9` … `rows229U_12` of `SieveCert229U.lean`'s certificate on
`SieveGrid229U.grid229U` (4 parts, 14 rows, 8023 cells of depth 4 and candidate cells), each the sum of
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

theorem rows229U_9 : rows 35 37 ≤ 3253448909898381 := by decide +kernel

theorem rows229U_10 : rows 37 39 ≤ 2863733763366406 := by decide +kernel

theorem rows229U_11 : rows 39 42 ≤ 3432977182177876 := by decide +kernel

theorem rows229U_12 : rows 42 49 ≤ 6736717874268414 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows229U_9
#print axioms SieveCert.rows229U_12
