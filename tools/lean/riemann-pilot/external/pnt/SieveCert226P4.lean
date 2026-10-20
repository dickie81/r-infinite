/-
# Round 614: the certificate at `L = 226/100`, parts 31–39 of 49 (rows 53 to 81)

File 4 of 5: the parts `rows226_31` … `rows226_39` of `SieveCert226.lean`'s certificate on `SieveGrid226.grid226`
(9 parts, 29 rows, 18642 cells of depth 4 and candidate cells), each the sum of the costs of its rows
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

theorem rows226_31 : rows 53 55 ≤ 1454924343663296 := by decide +kernel

theorem rows226_32 : rows 55 57 ≤ 1342158660848329 := by decide +kernel

theorem rows226_33 : rows 57 60 ≤ 5516129235103841 := by decide +kernel

theorem rows226_34 : rows 60 64 ≤ 9948038581540766 := by decide +kernel

theorem rows226_35 : rows 64 69 ≤ 7588977206375305 := by decide +kernel

theorem rows226_36 : rows 69 73 ≤ 2455340857252499 := by decide +kernel

theorem rows226_37 : rows 73 76 ≤ 605929020614214 := by decide +kernel

theorem rows226_38 : rows 76 79 ≤ 990635694135351 := by decide +kernel

theorem rows226_39 : rows 79 82 ≤ 4258264962750197 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows226_31
#print axioms SieveCert.rows226_39
