/-
# Round 710: the grid of the refined certificate at `L = 899/400` with `n = 300`

The grid of `SieveTypeIIU22475C.typeII_22475c`'s window: `U1 = ⌈(41335/100000)DEN⌉`, `U2 = ⌊(48069/100000)DEN⌋`,
`n = 300` (`grid22475R`, `gridOK22475R`), the window of `frontier/linnik/route_limits.jsonl`'s rows for `g7c` at
`899/400`. Its refined certificate (`SieveCert2Defs.total2`) is checked by the kernel in 534 parts, 135 files
(`SieveCert22475RP1.lean` … `SieveCert22475RP135.lean`, one `lean` process each): ranges of consecutive rows, and the
120 heavy rows in column pieces (`SieveCert2Defs.rowsJ2`); assembled in `SieveCert22475R.lean`.

The file imports `SieveCert2Defs.lean`, which imports `SieveCertDefs.lean` only, so neither it nor the part files load
`Mathlib` (round 618).
-/
import SieveCert2Defs

namespace SieveCert

/-- **The grid at `L = 899/400` with `n = 300`**: `U1 = ⌈(41335/100000)DEN⌉`, `U2 = ⌊(48069/100000)DEN⌋`. -/
@[instance_reducible] def grid22475R : Grid := ⟨(41335 * DEN + 99999) / 100000, 48069 * DEN / 100000, 300⟩

theorem gridOK22475R : @GridOK grid22475R :=
  @GridOK.mk grid22475R (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK22475R
