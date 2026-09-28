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
