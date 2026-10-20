/-
# Round 614: the certificate at `L = 226/100`, parts 20–30 of 49 (rows 41 to 52)

File 3 of 5: the parts `rows226_20` … `rows226_30` of `SieveCert226.lean`'s certificate on `SieveGrid226.grid226`
(11 parts, 12 rows, 19479 cells of depth 4 and candidate cells), each the sum of the costs of its rows
(`SieveCert232.rows`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid226.lean`.
-/
import SieveGrid226

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid226

theorem rows226_20 : rows 41 42 ≤ 1459370738768087 := by decide +kernel

theorem rows226_21 : rows 42 43 ≤ 1388572076622054 := by decide +kernel

theorem rows226_22 : rows 43 44 ≤ 1313541583867575 := by decide +kernel

theorem rows226_23 : rows 44 45 ≤ 1251648258243193 := by decide +kernel

theorem rows226_24 : rows 45 46 ≤ 1191257375779868 := by decide +kernel

theorem rows226_25 : rows 46 47 ≤ 1138421699003557 := by decide +kernel

theorem rows226_26 : rows 47 48 ≤ 1076912458288148 := by decide +kernel

theorem rows226_27 : rows 48 49 ≤ 1021440988597632 := by decide +kernel

theorem rows226_28 : rows 49 50 ≤ 957798384819106 := by decide +kernel

theorem rows226_29 : rows 50 51 ≤ 902140571728823 := by decide +kernel

theorem rows226_30 : rows 51 53 ≤ 1635576218293912 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows226_20
#print axioms SieveCert.rows226_30
