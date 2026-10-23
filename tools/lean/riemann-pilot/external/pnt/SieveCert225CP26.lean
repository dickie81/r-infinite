/-
# Round 625: the certificate at `L = 9/4`, parts 213–220 of 1374

File 26 of 167: the parts `rows225C_213` … `rows225C_220` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55879 depth-4 tests: row 76 columns 35–43, row 76 columns 44–49, row 76 columns
50–54, row 76 columns 55–58, row 76 columns 59–63, row 76 columns 64–70, row 76 columns 71–399, row 77 columns
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

theorem rows225C_213 : rowsJ 76 77 35 44 ≤ 52931434757867 := by decide +kernel

theorem rows225C_214 : rowsJ 76 77 44 50 ≤ 64757682866845 := by decide +kernel

theorem rows225C_215 : rowsJ 76 77 50 55 ≤ 114679488753776 := by decide +kernel

theorem rows225C_216 : rowsJ 76 77 55 59 ≤ 134616400372059 := by decide +kernel

theorem rows225C_217 : rowsJ 76 77 59 64 ≤ 161728634677962 := by decide +kernel

theorem rows225C_218 : rowsJ 76 77 64 71 ≤ 197860486333093 := by decide +kernel

theorem rows225C_219 : rowsJ 76 77 71 400 ≤ 142080944714526 := by decide +kernel

theorem rows225C_220 : rowsJ 77 78 0 35 ≤ 494747332593989 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_213
#print axioms SieveCert.rows225C_220
