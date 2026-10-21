/-
# Round 623: the certificate at `L = 229/100`, parts 13–16 of 21 (rows 49 to 63)

File 4 of 5: the parts `rows229U_13` … `rows229U_16` of `SieveCert229U.lean`'s certificate on
`SieveGrid229U.grid229U` (4 parts, 15 rows, 8658 cells of depth 4 and candidate cells), each the sum of
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

theorem rows229U_13 : rows 49 55 ≤ 2583447644131167 := by decide +kernel

theorem rows229U_14 : rows 55 58 ≤ 2467115541345301 := by decide +kernel

theorem rows229U_15 : rows 58 61 ≤ 8879629653393456 := by decide +kernel

theorem rows229U_16 : rows 61 64 ≤ 15471438590305548 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows229U_13
#print axioms SieveCert.rows229U_16
