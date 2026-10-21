/-
# Round 625: the certificate at `L = 9/4`, parts 293–300 of 1374

File 36 of 167: the parts `rows225C_293` … `rows225C_300` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 58347 depth-4 tests: row 86 columns 63–74, row 86 columns 75–399, row 87 columns
0–34, row 87 columns 35–43, row 87 columns 44–49, row 87 columns 50–55, row 87 columns 56–63, row 87 columns 64–77),
each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_293 : rowsJ 86 87 63 75 ≤ 240623368316747 := by decide +kernel

theorem rows225C_294 : rowsJ 86 87 75 400 ≤ 136426614686513 := by decide +kernel

theorem rows225C_295 : rowsJ 87 88 0 35 ≤ 281779185910198 := by decide +kernel

theorem rows225C_296 : rowsJ 87 88 35 44 ≤ 45981396979054 := by decide +kernel

theorem rows225C_297 : rowsJ 87 88 44 50 ≤ 118214607083214 := by decide +kernel

theorem rows225C_298 : rowsJ 87 88 50 56 ≤ 183213622495268 := by decide +kernel

theorem rows225C_299 : rowsJ 87 88 56 64 ≤ 208568142526091 := by decide +kernel

theorem rows225C_300 : rowsJ 87 88 64 78 ≤ 249439263834738 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_293
#print axioms SieveCert.rows225C_300
