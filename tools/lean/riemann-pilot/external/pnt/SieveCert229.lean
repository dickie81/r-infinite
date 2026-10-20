/-
# Round 607: the certificate of the sieve route's loss at `L = 229/100` (the second goal, N4)

The grid of `SieveTypeII73.typeII_73`'s window: `U1 = ⌈(4123/10000)DEN⌉`, `U2 = ⌊(4902/10000)DEN⌋`, `n = 100`. On it
`SieveCert.total` is at most `0.88K`, checked by the kernel.

The file imports `SieveCert.lean`.
-/
import SieveCert

namespace SieveCert

/-- **The grid at `L = 229/100`**: `U1 = ⌈(4123/10000)DEN⌉`, `U2 = ⌊(4902/10000)DEN⌋`, `n = 100`. -/
@[instance_reducible] def grid229 : Grid := ⟨(4123 * DEN + 9999) / 10000, 4902 * DEN / 10000, 100⟩

theorem gridOK229 : @GridOK grid229 :=
  @GridOK.mk grid229 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **The certificate on `grid229`**: the loss's bound is at most `0.88`, checked by the kernel. -/
theorem total_le_229 : @total grid229 ≤ 88 * K / 100 := by decide +kernel

end SieveCert

#print axioms SieveCert.gridOK229
#print axioms SieveCert.total_le_229
