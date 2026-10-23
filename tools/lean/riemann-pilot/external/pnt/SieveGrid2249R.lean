/-
# Round 710: the grid of the refined certificate at `L = 2249/1000` with `n = 300`

The grid of `SieveTypeIIU2249C.typeII_2249c`'s window: `U1 = ⌈(41249/100000)DEN⌉`, `U2 = ⌊(48104/100000)DEN⌋`, `n = 300`
(`grid2249R`, `gridOK2249R`), the window of `frontier/linnik/route_limits.jsonl`'s rows for `g7c` at `2249/1000`.
Its refined certificate (`SieveCert2Defs.total2`) is checked by the kernel in 503 parts, 127 files
(`SieveCert2249RP1.lean` … `SieveCert2249RP127.lean`, one `lean` process each): ranges of consecutive rows, and the
118 heavy rows in column pieces (`SieveCert2Defs.rowsJ2`); assembled in `SieveCert2249R.lean`.

The file imports `SieveCert2Defs.lean`, which imports `SieveCertDefs.lean` only, so neither it nor the part files load
`Mathlib` (round 618).
-/
import SieveCert2Defs

namespace SieveCert

/-- **The grid at `L = 2249/1000` with `n = 300`**: `U1 = ⌈(41249/100000)DEN⌉`, `U2 = ⌊(48104/100000)DEN⌋`. -/
@[instance_reducible] def grid2249R : Grid := ⟨(41249 * DEN + 99999) / 100000, 48104 * DEN / 100000, 300⟩

theorem gridOK2249R : @GridOK grid2249R :=
  @GridOK.mk grid2249R (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK2249R
