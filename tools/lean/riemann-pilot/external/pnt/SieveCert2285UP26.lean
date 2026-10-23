/-
# Round 631: the certificate at `L = 2285/1000`, parts 222–231 of 252

File 26 of 28: the parts `rows2285U_222` … `rows2285U_231` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (10 parts, 50122 depth-4 tests: row 106 columns 0–39, row 106 columns 40–249, row 107
columns 0–39, row 107 columns 40–249, row 108 columns 0–39, row 108 columns 40–249, row 109 columns 0–39, row 109
columns 40–249, row 110 columns 0–38, row 110 columns 39–249), each a sum of costs (`rows` or `rowsJ`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2285U.lean`.
-/
import SieveGrid2285U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2285U

theorem rows2285U_222 : rowsJ 106 107 0 40 ≤ 255862973071410 := by decide +kernel

theorem rows2285U_223 : rowsJ 106 107 40 250 ≤ 2939363159427629 := by decide +kernel

theorem rows2285U_224 : rowsJ 107 108 0 40 ≤ 271511668784666 := by decide +kernel

theorem rows2285U_225 : rowsJ 107 108 40 250 ≤ 3174156955367984 := by decide +kernel

theorem rows2285U_226 : rowsJ 108 109 0 40 ≤ 283936082733173 := by decide +kernel

theorem rows2285U_227 : rowsJ 108 109 40 250 ≤ 3395119907265669 := by decide +kernel

theorem rows2285U_228 : rowsJ 109 110 0 40 ≤ 300008424543067 := by decide +kernel

theorem rows2285U_229 : rowsJ 109 110 40 250 ≤ 3628739825683039 := by decide +kernel

theorem rows2285U_230 : rowsJ 110 111 0 39 ≤ 290614169865779 := by decide +kernel

theorem rows2285U_231 : rowsJ 110 111 39 250 ≤ 3883587570406596 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_222
#print axioms SieveCert.rows2285U_231
