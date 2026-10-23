/-
# Round 612: the certificate of the sieve route's loss at `L = 227/100` (the Weyl-conditional exponent)

The grid of `SieveTypeIIU227.typeII_227`'s window: `U1 = ⌈(4048/10000)DEN⌉`, `U2 = ⌊(4858/10000)DEN⌋`, `n = 100`. On it
`SieveCert.total` is at most `0.88K`, checked by the kernel.

The file imports `SieveCert.lean`.
-/
import SieveCert

namespace SieveCert

/-- **The grid at `L = 227/100`**: `U1 = ⌈(4048/10000)DEN⌉`, `U2 = ⌊(4858/10000)DEN⌋`, `n = 100`. -/
@[instance_reducible] def grid227 : Grid := ⟨(4048 * DEN + 9999) / 10000, 4858 * DEN / 10000, 100⟩

theorem gridOK227 : @GridOK grid227 :=
  @GridOK.mk grid227 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **The certificate on `grid227`**: the loss's bound is at most `0.88`, checked by the kernel. -/
theorem total_le_227 : @total grid227 ≤ 88 * K / 100 := by decide +kernel

end SieveCert

#print axioms SieveCert.gridOK227
#print axioms SieveCert.total_le_227
