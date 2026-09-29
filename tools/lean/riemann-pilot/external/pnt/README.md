# External: rungs 1 and 2 of the wander ladder

`WanderLadderPNT.lean` imports the PrimeNumberTheoremAnd project (Kontorovich, Tao et al.) and restates two of its results in the pilot's terms (`Chebyshev.psi` from Mathlib):
- rung 1, the prime number theorem;
- rung 2, de la Vallée Poussin's error term.

It uses a different toolchain from the rest of the pilot, so it is built separately.

```
git clone https://github.com/AlexKontorovich/PrimeNumberTheoremAnd pntplus
cd pntplus && git checkout 650d31264be65f4cd6e70c45d8b25d86d482a761   # toolchain v4.33.1
lake exe cache get
lake build PrimeNumberTheoremAnd.StrongPNT PrimeNumberTheoremAnd.Consequences
cp <pilot>/external/pnt/WanderLadderPNT.lean . && lake env lean WanderLadderPNT.lean
```

Checked in round 191: all three theorems print only `propext`, `Classical.choice`, `Quot.sound`. The two `sorry` lemmas in the project's `Wiener.lean` are not in the dependency cone.

## Rung3.lean (round 192)

Build as above, then `lake env lean Rung3.lean`.

`rung3_of_region` reduces rung 3 to one analytic input, `KVInput n₁ n₂`: a zero-free region of width `(log t)^{−n₁}` plus a log-derivative bound. Its axioms are clean.

## Landau.lean (round 193)

Build as above, then `lake env lean Landau.lean` (about 10 minutes; three proofs raise `maxHeartbeats`).

This is layer III of rung 3, Landau's lemma in general form. `rung3_of_growth` runs from `PolylogGrowth a K` (`|ζ| ≤ K(log|t|)^K` on `σ ≥ 1 − (log|t|)^{−a}`, `0 < a ≤ 1`) to `ψ(x) − x = O(x·exp(−c(log x)^{1/(1+n₁)}))`, for every `n₁ > a`. The intermediate outputs are `zeroFree_of_growth` (the zero-free region) and `logDerivBnd_of_growth` (`|ζ'/ζ| ≤ C(log|t|)³`). All axioms are clean.


## KVBridge.lean and kv_port.sh (round 212): rung 3, unconditional

`PNT=<pntplus checkout> ./kv_port.sh` builds the whole chain on PNT+'s toolchain (v4.33.1), in about 6 minutes after PNT+ itself is built:
- the pilot's layer I–II files (`Vinogradov` … `ExpSum7`), copied with three lemma renames that the older Mathlib needs;
- `Landau.lean`;
- `KVBridge.lean`.

The script then prints the axioms of the final theorems. All three print only `propext`, `Classical.choice`, `Quot.sound`.

- `polylogGrowth_kv`: `PolylogGrowth a K` holds for every `6/7 ≤ a ≤ 1`.
- `zeroFree_kv`: `ZetaZeroFreeGenProp n₁` holds for every `n₁ > 6/7`, i.e. ζ has no zeros in `σ ≥ 1 − A/(log|t|)^{n₁}`.
- `rung3_kv`: `ψ(x) − x = O(x·exp(−c(log x)^{1/(1+n₁)}))` for every `n₁ > 6/7`.
