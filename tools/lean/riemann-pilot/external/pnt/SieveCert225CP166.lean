/-
# Round 625: the certificate at `L = 9/4`, parts 1360–1369 of 1374

File 166 of 167: the parts `rows225C_1360` … `rows225C_1369` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (10 parts, 52989 depth-4 tests: rows 220–220, rows 221–221, rows 222–222, rows 223–223,
rows 224–225, rows 226–227, rows 228–230, rows 231–235, rows 236–256, rows 257–276), each a sum of costs (`rows` or
`rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_1360 : rows 220 221 ≤ 3422491585567955 := by decide +kernel

theorem rows225C_1361 : rows 221 222 ≤ 3508128390127568 := by decide +kernel

theorem rows225C_1362 : rows 222 223 ≤ 3594717928040009 := by decide +kernel

theorem rows225C_1363 : rows 223 224 ≤ 3682276092940491 := by decide +kernel

theorem rows225C_1364 : rows 224 226 ≤ 7631095519524383 := by decide +kernel

theorem rows225C_1365 : rows 226 228 ≤ 7992750804119341 := by decide +kernel

theorem rows225C_1366 : rows 228 231 ≤ 12683088799983654 := by decide +kernel

theorem rows225C_1367 : rows 231 236 ≤ 23045169157913356 := by decide +kernel

theorem rows225C_1368 : rows 236 257 ≤ 120886422955495178 := by decide +kernel

theorem rows225C_1369 : rows 257 277 ≤ 141629151565403405 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1360
#print axioms SieveCert.rows225C_1369
