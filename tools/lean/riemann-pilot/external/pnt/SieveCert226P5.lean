/-
# Round 614: the certificate at `L = 226/100`, parts 40–48 of 49 (rows 82 to 199)

File 5 of 5: the parts `rows226_40` … `rows226_48` of `SieveCert226.lean`'s certificate on `SieveGrid226.grid226`
(9 parts, 118 rows, 18756 cells of depth 4 and candidate cells), each the sum of the costs of its rows
(`rows`, in `SieveCertDefs.lean` since round 618) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid226.lean`.
-/
import SieveGrid226

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid226

theorem rows226_40 : rows 82 85 ≤ 7738434492368668 := by decide +kernel

theorem rows226_41 : rows 85 88 ≤ 10409612259189026 := by decide +kernel

theorem rows226_42 : rows 88 91 ≤ 10998480726351280 := by decide +kernel

theorem rows226_43 : rows 91 94 ≤ 11470796405456018 := by decide +kernel

theorem rows226_44 : rows 94 97 ≤ 11912659504398184 := by decide +kernel

theorem rows226_45 : rows 97 101 ≤ 16516014093535422 := by decide +kernel

theorem rows226_46 : rows 101 108 ≤ 34136467041313808 := by decide +kernel

theorem rows226_47 : rows 108 147 ≤ 466745278747737984 := by decide +kernel

theorem rows226_48 : rows 147 200 ≤ 314340118065623424 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows226_40
#print axioms SieveCert.rows226_48
