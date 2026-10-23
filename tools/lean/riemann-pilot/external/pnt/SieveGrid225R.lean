/-
# Round 705: the grid of the refined certificate at `L = 9/4` with `n = 200`

The grid of `SieveTypeIIU225C.typeII_225c`'s window: `U1 = ⌈(41191/100000)DEN⌉`, `U2 = ⌊(48127/100000)DEN⌋`, `n = 200`
(`grid225R`, `gridOK225R`), round 625's window with half its cells a side. Its refined certificate
(`SieveCert2Defs.total2`) is checked by the kernel in 117 parts, 27 files (`SieveCert225RP1.lean` …
`SieveCert225RP27.lean`, one `lean` process each): ranges of consecutive rows, and the 33 heavy rows in column
pieces (`SieveCert2Defs.rowsJ2`); assembled in `SieveCert225R.lean`.

The file imports `SieveCert2Defs.lean`, which imports `SieveCertDefs.lean` only, so neither it nor the part files load
`Mathlib` (round 618).
-/
import SieveCert2Defs

namespace SieveCert

/-- **The grid at `L = 9/4` with `n = 200`**: `U1 = ⌈(41191/100000)DEN⌉`, `U2 = ⌊(48127/100000)DEN⌋`. -/
@[instance_reducible] def grid225R : Grid := ⟨(41191 * DEN + 99999) / 100000, 48127 * DEN / 100000, 200⟩

theorem gridOK225R : @GridOK grid225R :=
  @GridOK.mk grid225R (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK225R
