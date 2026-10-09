# External: the Davenport–Heilbronn layer (rounds 253–273; split from `src/` in round 275)

The Davenport–Heilbronn function `dh = (1 + ε′)L(s, χ₅) + (1 + ε)L(s, χ₅⁻¹)` run through the pilot's Weil machinery: its explicit formula (`DHExplicit`), the kernel-checked off-line zero (`DHCertificate.dh_offline_zero`), four located zeros (`DHLocateNum.dh_zero_located_box`, `DHLocateFour`), the ground-state stack (`DHGround`, an instance of `src/GroundChain.lean`), the negative index (`DHNegIndex`, an instance of `src/WeilIndexInfinite.lean`'s `NegData`) and the dh column of the substitution matrix (`DHColumn`, `DHColumnRest`, `DHTwin`, `DHOddPacket`, …). `DHJoins` (round 328) adds the conjugation symmetry `dh(s̄) = conj dh(s)`, the parity split of `Q_dh` and a Weil index of at least `5` on probes of either parity; for `L(s, χ)` it adds the ground energy `λ_χ`, and GRH(χ) iff `λ_χ ≥ 0` at every support (round 329). `ChiGround` (round 330) ports the ground-state stack to `L(s, χ)`: DHGround's proofs, stated once for every u-space form with no pole term, give ground states, Theorem D and the top-of-chain ground state for Weil's form of every Dirichlet character, and the chain from the convergence hypothesis `HypConvC χ` to GRH(χ). `ChiFirstFailure` (round 331) adds, for every such form, continuity of the ground energy, positivity at small support and the first-failure structure theorem: under `¬GRH(χ)` for `χ`, and unconditionally for `dh`, whose first failure lies at some `a₁ ≤ 12/5`. About 85% of the lines are generated interval arithmetic *(corrected in round 328; it read 60%)*; the generators are in `frontier/dh/lean_gen/` and reproduce the files byte for byte.

## Building

```
../../build.sh    # the pilot's own files (src/)
./build.sh        # this directory, into the same ../../build
```

`./build.sh` is the pilot's `build.sh` with `SRC` set to this directory: parallel, incremental, and a file is rebuilt when it or any pilot module it imports changed. Recompiling 35 of its 50 files took about 5,200 CPU-seconds (round 275), so a clean build of this layer costs well over an hour of CPU on top of the pilot's.

Every file ends with `#print axioms`; all 454 checked theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. See the main README, rounds 253–275. Since round 327 `./build.sh` checks this: a compiled file fails if Lean reports a use of `sorry` in it or it prints an axiom outside those three.
