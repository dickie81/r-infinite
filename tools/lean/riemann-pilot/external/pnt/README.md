# External: rungs 1–3 of the wander ladder

These files build on the PrimeNumberTheoremAnd project (PNT+; Kontorovich, Tao et al.).

| file | round | content |
|---|---|---|
| `WanderLadderPNT.lean` | 191 | rungs 1 and 2 in the pilot's terms |
| `Rung3.lean` | 192 | rung 3 from a zero-free region and a `ζ'/ζ` bound |
| `Landau.lean` | 193, 219 | Landau's lemma: a growth bound on ζ gives rung 3; since round 219, for any admissible width function |
| `KVBridge.lean` | 212 | the pilot's layers I–II give the growth bound: rung 3, unconditional |
| `LandauKV.lean` | 215 | the Korobov–Vinogradov zero-free region |
| `LogDerivKV.lean`, `MediumPNTW.lean`, `PNTKV.lean` | 216 | the prime number theorem with the Korobov–Vinogradov error term |
| `KaiserKV.lean` | 234 | the Korobov–Vinogradov region in the Kaiser prefactor: `λ₁(a) ≤ K(a+1)exp(10a − c·a^{1/3}/(log a)^{1/3} − 4πe^{2a})` |
| `HalfPlanePNT.lean` | 337 | a zero-free half-plane `Re s > θ` gives `ψ(x) − x = O(x^{(1+θ)/2+ε})` |

## Building (round 217)

Everything builds on the pilot's toolchain (`../../lean-toolchain`, Mathlib at `../../MATHLIB_REV`):

```
../../build.sh    # the pilot's own files
./build.sh        # PNT+ and this directory
```

`build.sh` does four things:
- It takes the 19 PNT+ files that this directory imports, at commit `650d312` (Lean v4.33.1), into `upstream/`. Set `PNT` to a PNT+ clone to use it; otherwise that one commit is fetched.
- It applies `pnt_port.patch`, which ports those files to the pilot's toolchain. There are five small changes, all forced by Mathlib API drift; the top of the patch lists them.
- It compiles `Architect.lean`, the PNT+ files and this directory's files into `../../build`, next to the pilot's oleans.
  - `Architect.lean` is a no-op stand-in for LeanArchitect, the package behind PNT+'s `@[blueprint]` tags. The tags only feed PNT+'s blueprint document.
  - The PNT+ files are compiled with PNT+'s own lakefile options, `autoImplicit = false` and `relaxedAutoImplicit = false`.
- It prints the axioms of the final theorems. It fails if Lean reports a use of `sorry` in one of this directory's files, or if those files or the final check print an axiom outside `propext`, `Classical.choice` and `Quot.sound`. The final check also needs one clean line per `#print axioms` (round 327).

The pilot's layer I–II files (`Vinogradov` … `VinoKV`) are no longer copied and renamed: `KVBridge.lean` and `LandauKV.lean` import the pilot's own oleans. `kv_port.sh` is gone.

The two `sorry` lemmas in PNT+'s `Wiener.lean` are not in the dependency cone of any theorem here. So the build does not check the PNT+ files (`StrongPNT.lean`, which prints its axioms under `open Classical` as `[propext, choice, Quot.sound]`, would also fail the check). A checked theorem here that used one of the two lemmas would print `sorryAx` in its axiom line and fail the build.

## WanderLadderPNT.lean (round 191)

`WanderLadderPNT.lean` restates two PNT+ results in the pilot's terms (`Chebyshev.psi` from Mathlib):
- rung 1, the prime number theorem;
- rung 2, de la Vallée Poussin's error term.

All three theorems print only `propext`, `Classical.choice`, `Quot.sound`.

## Rung3.lean (round 192)

`rung3_of_region` reduces rung 3 to one analytic input, `KVInput n₁ n₂`: a zero-free region of width `(log t)^{−n₁}` plus a log-derivative bound. Its axioms are clean.

## Landau.lean (round 193)

This is layer III of rung 3, Landau's lemma in general form. Three of its proofs raise `maxHeartbeats`.

`rung3_of_growth` runs from `PolylogGrowth a K` (`|ζ| ≤ K(log|t|)^K` on `σ ≥ 1 − (log|t|)^{−a}`, `0 < a ≤ 1`) to `ψ(x) − x = O(x·exp(−c(log x)^{1/(1+n₁)}))`, for every `n₁ > a`. The intermediate outputs are `zeroFree_of_growth` (the zero-free region) and `logDerivBnd_of_growth` (`|ζ'/ζ| ≤ C(log|t|)³`). All axioms are clean.

The local steps are proved once, for any admissible width `w` (`WidthOK`: positive, at most 1, non-increasing, `log(1/w(L)) = O(1 + log L)`): `apply_localW`, `zero_gapW`, `disc_factsW`, `near_boundW`. The power width `wpow a L = L^(−a)` gives the statements above, and `LandauKV`/`LogDerivKV` use the Korobov–Vinogradov width. Round 215's `LandauW.lean` is merged in (round 219).

## KVBridge.lean (round 212): rung 3, unconditional

- `polylogGrowth_kv`: `PolylogGrowth a K` holds for every `4/5 ≤ a ≤ 1`; `polylogGrowth_sharp` extends this to every `2/3 < a ≤ 1`.
- `zeroFree_kv`: `ZetaZeroFreeGenProp n₁` holds for every `n₁ > 2/3`, i.e. ζ has no zeros in `σ ≥ 1 − A/(log|t|)^{n₁}`.
- `rung3_kv`: `ψ(x) − x = O(x·exp(−c(log x)^{1/(1+n₁)}))` for every `n₁ > 2/3`.

## Rounds 215–216: the Korobov–Vinogradov prime number theorem

- `LandauKV.zeroFree_KV`: ζ has no zeros in `σ ≥ 1 − A/((log|t|)^{2/3}(log log|t|)^{1/3})`, for `|t| ≥ e³`.
- `LogDerivKV.logDerivBnd_KV`: `|ζ'/ζ| ≤ C(log|t|)³` for `|t| > 3` and `σ ≥ 1 − A·u(|t|)`, where `u(T) = 1/((log T)^{2/3}(log(log T + 3))^{1/3})`.
- `MediumPNTW.GenPNTW`: PNT+'s contour argument, restated for any depth function `D` with `DepthOK D`.
- `PNTKV.PNT_KV`: `ψ(x) − x = O(x·exp(−c(log x)^{3/5}/(log log x)^{1/5}))`.

All axioms are clean. See the main README, rounds 191–217, for the details.

## KaiserKV.lean (round 234)

- `region`: with PNT+'s `ZetaNoZerosInBox` below `e³` and `zeroFree_KV` above, every zero `β + iγ` with `|γ| ≤ T` has `β < 1 − A/((log T)^{2/3}(log log T)^{1/3})`, for every `T ≥ e³`.
- `abs_im_tau_le`: the zeros of the pilot's `Ξ` with `|Re τ| ≤ T` have `|Im τ| ≤ ½ − A/f(T)`.
- `lam_prefactor_KV`: `λ₁(a) ≤ K(a + 1)·exp(10a − c·a^{1/3}/(log a)^{1/3} − 4πe^{2a})` for `a ≥ 4`, through the pilot's `Kaiser.lam_le_split` (`src/KaiserSplit.lean`).

All axioms are clean. See the main README, round 234.

## ShortKV.lean, DetectEM.lean (round 235)

- `ShortKV.zeroFreeXi_KV`: the Korobov–Vinogradov region in the pilot's form, `ZeroFreeXi (3/4)`.
- `DetectEM.detectHyp`: PNT+'s Euler–Maclaurin formula at a zero, together with the mollifier identity (`src/MollId.lean`), gives `|D(ρ)| ≥ ½`.
- `DetectEM.density_unconditional`: `N(σ, T) ≪ T^{4(1+δ)(1−σ)}(log T)^{11}` for every `0 < δ ≤ 1/4`.
- `DetectEM.short_primes`: for every `θ > 3/4`, every large `y` has a prime in `(y, y + y^θ]`.

All axioms are clean. See the main README, round 235.

## HalfPlanePNT.lean (round 337)

- `riemannZeta_linear_growth`: `|ζ(s)| ≤ (5/2 + 1/δ)|Im s|` for `Re s ≥ δ > 0`, `|Im s| ≥ 1`, from PNT+'s Euler–Maclaurin formula. The proof is that of zeta23's `RvM.norm_riemannZeta_le_of_re_pos`, run against PNT+.
- `logDeriv_le_of_zeroFree`: if `ζ(s) ≠ 0` on `Re s > θ ≥ 0`, then `|ζ'/ζ(σ + it)| ≤ C log|t|` for `σ ≥ θ' > θ` and `|t| > 3`, through PNT+'s `FinalBound` on a disc that holds no zero.
- `MediumPNTW.GenPNTW'`: `GenPNTW` with the abscissa `σ₂` of the small-height box as a parameter, and `σ₂ < 1 − D(T(x))` eventually in place of `D(T(x)) → 0`, so a constant depth is allowed. `GenPNTW` is its case with PNT+'s `σ₂`.
- `psi_isBigO_of_zeroFree`: if `ζ(s) ≠ 0` on `Re s > θ` with `θ < 1`, then `ψ(x) − x = O(x^{(1+θ)/2+ε})` for every `ε > 0`. Its instances are `psi_isBigO_of_smoothBound` (round 278's `SmoothBound θ`) and `psi_isBigO_of_completed` (`O(x^{23/24+ε})` under round 326's completed mean square). The exponent is `(1+θ)/2`, not the classical `θ`; see the main README, round 337.

For the instances, the file imports `src/HalfPlaneS0.lean` and `src/EisensteinTransferEstimate.lean`. All axioms are clean.
