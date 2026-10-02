# χ₄ control: pre-registration (round 224)

Written before any run. DH's Weil form fails at `a₁ = 1.713` (round 165) and `−λ₁^{DH}` grows past it
(round 222). The control is the same code on `L(s, χ₄)`, whose zeros are on the line as far as
computed (`validate.py` finds 122 by sign changes below height 200; GRH for `χ₄` is verified far
beyond by others). Everything else (the Gram, `z0 = 3/4`, no pole) is shared with the DH runs.

**Predictions.**
1. `λ₁^{χ₄}(a) > 0` at every `a ∈ {1.0, 1.5, 1.715, 2.0, 2.25, 2.5}`, the last three past DH's
   first failure. A negative value that is stable in `K` and precision falsifies either GRH for `χ₄`
   below the horizon (not credible) or the Gram code.
2. Decay law: `−log λ₁ / e^{2a} ∈ [0.8π, 1.2π]` for `a ≥ 1.5` (the prolate rate `4π` divided by the
   conductor `4`, as DH gave `4π/5`).

Parameters: `scan.py chi4 K PREC δ`, `δ = 2a`, `K ∈ {80, 120}`, `PREC` at least `3.5·π·e^{2a}·log₂e`
bits so the smallest eigenvalue is resolved.
