/-
# Round 614: the certificate at `L = 226/100`, parts 11–19 of 49 (rows 32 to 40)

File 2 of 5: the parts `rows226_11` … `rows226_19` of `SieveCert226.lean`'s certificate on `SieveGrid226.grid226`
(9 parts, 9 rows, 20034 cells of depth 4 and candidate cells), each the sum of the costs of its rows
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

theorem rows226_11 : rows 32 33 ≤ 1616611958447808 := by decide +kernel

theorem rows226_12 : rows 33 34 ≤ 1655361389976004 := by decide +kernel

theorem rows226_13 : rows 34 35 ≤ 1684342531840116 := by decide +kernel

theorem rows226_14 : rows 35 36 ≤ 1692431074721515 := by decide +kernel

theorem rows226_15 : rows 36 37 ≤ 1690794303084396 := by decide +kernel

theorem rows226_16 : rows 37 38 ≤ 1667812148299010 := by decide +kernel

theorem rows226_17 : rows 38 39 ≤ 1636637693185937 := by decide +kernel

theorem rows226_18 : rows 39 40 ≤ 1586934696261992 := by decide +kernel

theorem rows226_19 : rows 40 41 ≤ 1530521885202004 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows226_11
#print axioms SieveCert.rows226_19
