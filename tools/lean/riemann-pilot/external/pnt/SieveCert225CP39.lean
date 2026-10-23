/-
# Round 625: the certificate at `L = 9/4`, parts 317–323 of 1374

File 39 of 167: the parts `rows225C_317` … `rows225C_323` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (7 parts, 53000 depth-4 tests: row 90 columns 35–43, row 90 columns 44–49, row 90 columns
50–56, row 90 columns 57–66, row 90 columns 67–84, row 90 columns 85–399, row 91 columns 0–34), each a sum of costs
(`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_317 : rowsJ 90 91 35 44 ≤ 58761238620471 := by decide +kernel

theorem rows225C_318 : rowsJ 90 91 44 50 ≤ 137244321200823 := by decide +kernel

theorem rows225C_319 : rowsJ 90 91 50 57 ≤ 201398028637210 := by decide +kernel

theorem rows225C_320 : rowsJ 90 91 57 67 ≤ 224382995878461 := by decide +kernel

theorem rows225C_321 : rowsJ 90 91 67 85 ≤ 218360593982963 := by decide +kernel

theorem rows225C_322 : rowsJ 90 91 85 400 ≤ 30168215432961 := by decide +kernel

theorem rows225C_323 : rowsJ 91 92 0 35 ≤ 211413332874450 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_317
#print axioms SieveCert.rows225C_323
