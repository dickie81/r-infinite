/-
# Round 614: the certificate at `L = 226/100`, parts 0–10 of 49 (rows 0 to 31)

File 1 of 5: the parts `rows226_0` … `rows226_10` of `SieveCert226.lean`'s certificate on `SieveGrid226.grid226`
(11 parts, 32 rows, 21105 cells of depth 4 and candidate cells), each the sum of the costs of its rows
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

theorem rows226_0 : rows 0 13 ≤ 5021472774744892 := by decide +kernel

theorem rows226_1 : rows 13 16 ≤ 4151819246414472 := by decide +kernel

theorem rows226_2 : rows 16 18 ≤ 3270975673645792 := by decide +kernel

theorem rows226_3 : rows 18 20 ≤ 3275654964694850 := by decide +kernel

theorem rows226_4 : rows 20 23 ≤ 4392311959989472 := by decide +kernel

theorem rows226_5 : rows 23 26 ≤ 3680148386702704 := by decide +kernel

theorem rows226_6 : rows 26 28 ≤ 2415501076969146 := by decide +kernel

theorem rows226_7 : rows 28 29 ≤ 1325023193683227 := by decide +kernel

theorem rows226_8 : rows 29 30 ≤ 1412625082590074 := by decide +kernel

theorem rows226_9 : rows 30 31 ≤ 1494901429958792 := by decide +kernel

theorem rows226_10 : rows 31 32 ≤ 1559129071124296 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows226_0
#print axioms SieveCert.rows226_10
