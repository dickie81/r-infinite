/-
# Round 625: the certificate at `L = 9/4`, parts 309–316 of 1374

File 38 of 167: the parts `rows225C_309` … `rows225C_316` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 59652 depth-4 tests: row 89 columns 0–34, row 89 columns 35–43, row 89 columns
44–49, row 89 columns 50–55, row 89 columns 56–64, row 89 columns 65–82, row 89 columns 83–399, row 90 columns
0–34), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_309 : rowsJ 89 90 0 35 ≤ 245067829967384 := by decide +kernel

theorem rows225C_310 : rowsJ 89 90 35 44 ≤ 54046349275411 := by decide +kernel

theorem rows225C_311 : rowsJ 89 90 44 50 ≤ 130795444289890 := by decide +kernel

theorem rows225C_312 : rowsJ 89 90 50 56 ≤ 178791765705439 := by decide +kernel

theorem rows225C_313 : rowsJ 89 90 56 65 ≤ 218653990110016 := by decide +kernel

theorem rows225C_314 : rowsJ 89 90 65 83 ≤ 255977995078126 := by decide +kernel

theorem rows225C_315 : rowsJ 89 90 83 400 ≤ 43594452639303 := by decide +kernel

theorem rows225C_316 : rowsJ 90 91 0 35 ≤ 227884491921328 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_309
#print axioms SieveCert.rows225C_316
