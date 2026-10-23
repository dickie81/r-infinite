/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 40–43 of 534

File 10 of 135: the parts `rows22475R_40` … `rows22475R_43` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27010 tests: row 47 columns 35–43, row 47 columns 44–299, row 48 columns
0–34, row 48 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_40 : rowsJ2 47 48 35 44 ≤ 396868365533353 := by decide +kernel

theorem rows22475R_41 : rowsJ2 47 48 44 300 ≤ 249289460066596 := by decide +kernel

theorem rows22475R_42 : rowsJ2 48 49 0 35 ≤ 1938343718736433 := by decide +kernel

theorem rows22475R_43 : rowsJ2 48 49 35 44 ≤ 382473660965923 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_40
#print axioms SieveCert.rows22475R_43
