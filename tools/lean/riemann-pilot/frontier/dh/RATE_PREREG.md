# DH rate test: pre-registration (round 222)

Written before any run past `a = 2.0`.

`WeilRate.lam_rate` (Lean, clean axioms) proves for ζ: a zero with `|2 Re ρ − 1| > σ` forces
`λ₁(a) < −C e^{σa}` at arbitrarily large `a`. The proof only uses the explicit formula, so the same
mechanism is expected for the Davenport–Heilbronn function, whose Weil form is built by the same code
(`dh_gram.py`). The Lean theorem is not about DH; this is a numerical transfer test.

Lowest off-line DH zero (`anal.py` seeds): `ρ₀ = 0.808517 + 85.699348 i`, so `2β₀ − 1 = 0.617034`.

Heuristic: the optimal probe concentrates on `ρ₀`, giving `−λ₁(a) ≍ |ĝ_a(τ₀)|² ∝ e^{(2β₀−1)a}` times
slowly varying factors (powers of `a`).

**Prediction.** Over `a ∈ [2.5, 3.5]` the least-squares slope of `log(−λ₁^{DH}(a))` against `a` lies in
`[0.55, 0.70]`, target `0.617`.

**Falsifiers.**
* A slope outside `[0.55, 0.70]` that is stable in `K` (120 vs 160) falsifies the heuristic.
* A slope above 0.70 would point to another off-line zero dominating. That would require a
  zero with `2β − 1 > 0.70`, i.e. `β > 0.85`, visible below height `≈ 5e^{2a}/(2πe)`. The next
  known seeds have `β = 0.724, 0.651, 0.574`, so this is not expected.

Parameters: `scan.py dh K 300 δ`, `δ = 2a ∈ {4.0, 4.5, …, 7.0}`, `K ∈ {120, 160}`.
