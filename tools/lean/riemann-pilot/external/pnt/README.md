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
| `HalfPlanePNT.lean` | 337, 338 | a zero-free half-plane `Re s > θ` gives `ψ(x) − x = O(x^{θ+ε})` |
| `BohrKV.lean` | 399 | the Korobov–Vinogradov region as a shell around round 391's Bohr sphere at each height |
| `HalfPlaneFinal.lean` | 467 | `ψ(x) − x = O(x^{11/12+ε})` with no hypothesis, from the pilot's half-plane `Re s > 11/12` (round 466) |
| `PsiExponent.lean` | 469 | the exponent of the error: `limsup log\|ψ(x) − x\| / log x = Θ`, the supremum of the real parts of the zeros, with `½ ≤ Θ ≤ 11/12` |
| `HalfPlaneLindelof.lean` | 470 | a zero-free half-plane `Re s > θ` gives `ζ(s)^{±1} = O(\|t\|^ε)` on `Re s ≥ σ₀ > θ`; with no hypothesis at `θ = 11/12`, and at `Θ` |
| `SmoothPerron.lean` | 472, 473 | the smoothed Perron formula for a general Dirichlet series, the shift of the line of integration, and the unsmoothing |
| `MertensExponent.lean` | 472 | `M(x) = O(x^{θ+η})` from a zero-free half-plane; `limsup log\|M(x)\| / log x = Θ`; `RH ⟺ Θ = ½`; Littlewood's criterion; the abscissa of convergence of `Σ μ(n)n^{−s}` is `Θ` |
| `DivisorExponent.lean` | 473 | the divisor problems: `Σ_{n≤x} d_k(n) = xP_k(log x) + O(x^{θ+η})` from a zero-free half-plane `Re s > θ`, with `P_k` of degree `k − 1`; with no hypothesis at `θ = 11/12`, and at `Θ` |
| `ChiPNT.lean` | 478 | `ψ(x, χ) = Σ_{n≤x} χ(n)Λ(n) = O(x^{θ+η})` for a real `χ ≠ 1` with `L(s, χ) ≠ 0` on `Re s > θ`; with no hypothesis at `θ = 11/12`; the log-derivative of an entire function in a zero-free half-plane, `\|F′/F(σ + it)\| ≤ C log\|t\|` |

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
- Round 400: the detection argument moved to `src/DetectCore.lean`, with its one PNT+ input displayed as `DetectCore.EMBound`, the Euler–Maclaurin bound at a zero. `DetectEM.emBound` proves that input from `norm_partial_zeta_le`. `detectHyp`, `density_unconditional` and `short_primes` keep their names and statements; the helper lemmas `zeta_βsγs`, `aux_Z`, `aux_exp1` and `aux_exp2` are now in `DetectCore`. The zeta23 layer proves the same input from its own copy of PNT+'s `ZetaBounds` (`external/zeta23/ShellDensity.lean`).

All axioms are clean. See the main README, rounds 235 and 400.

## HalfPlanePNT.lean (rounds 337, 338)

- `riemannZeta_linear_growth`: `|ζ(s)| ≤ (5/2 + 1/δ)|Im s|` for `Re s ≥ δ > 0`, `|Im s| ≥ 1`, from PNT+'s Euler–Maclaurin formula. The proof is that of zeta23's `RvM.norm_riemannZeta_le_of_re_pos`, run against PNT+.
- `logDeriv_le_of_zeroFree`: if `ζ(s) ≠ 0` on `Re s > θ ≥ 0`, then `|ζ'/ζ(σ + it)| ≤ C log|t|` for `σ ≥ θ' > θ` and `|t| > 3`, through PNT+'s `FinalBound` on a disc that holds no zero.
- `MediumPNTW.GenPNTW'`: `GenPNTW` with the abscissa `σ₂` of the small-height box as a parameter, and `σ₂ < 1 − D(T(x))` eventually in place of `D(T(x)) → 0`, so a constant depth is allowed. `GenPNTW` is its case with PNT+'s `σ₂`.
- `MediumPNTW.MellinOfSmooth1d` (round 338): `|M(Smooth1 ν ε)(s)| ≤ B/|s|` for `0 < Re s ≤ 2` and `0 < ε < 1`, with `B` independent of `ε`, from PNT+'s `MellinOfSmooth1a`. With it the five segments left of `Re s = 1` are bounded without the factor `1/ε` (`I3NoEpsBoundW` to `I7NoEpsBoundW`, `I5NoEpsBound`). `GenPNTWOfLeft` is the contour argument with the bound on those five segments as a hypothesis. `GenPNTW'` is its case with PNT+'s bounds, and `GenPNTWNoEps` its case with these.
- `psi_isBigO_of_zeroFree`: if `ζ(s) ≠ 0` on `Re s > θ` with `θ < 1`, then `ψ(x) − x = O(x^{θ+ε})` for every `ε > 0`, through `GenPNTWNoEps`. Its instances are `psi_isBigO_of_smoothBound` (round 278's `SmoothBound θ`) and `psi_isBigO_of_completed` (`O(x^{11/12+ε})` under round 326's completed mean square). *(Round 467: the completed mean square is proved, the pilot's round 466 `Eis.completedMeanSquare`; `HalfPlaneFinal.lean` states the bound with no hypothesis.)* Round 337 had the exponent `(1+θ)/2 + ε`, through `GenPNTW'`; see the main README, rounds 337 and 338.

For the instances, the file imports `src/HalfPlaneS0.lean` and `src/EisensteinTransferEstimate.lean`. All axioms are clean.

## BohrKV.lean (round 399)

`shell_of_KV`: a nontrivial zero `ρ` with `|Im ρ| ≥ e³` has `‖v_F(1 − δ)‖ < ‖v_F(ρ)‖ < ‖v_F(δ)‖` for every nonempty finite set `F` of primes, where `δ = A/((log|Im ρ|)^{2/3}(log log|Im ρ|)^{1/3})` comes from `LandauKV.zeroFree_KV` and `v_F` is round 391's normalised Bohr vector (`src/BohrSphere.lean`). The bound `Re ρ > δ` uses the reflection `ρ ↦ 1 − ρ` (`PsiOmega.IsNontrivialZero.one_sub`). The file imports `src/BohrJoins.lean`; see the main README, round 399. All axioms are clean.

## HalfPlaneFinal.lean (round 467)

`HalfPlanePNT.psi_isBigO_eleven_twelfths`: `ψ(x) − x = O(x^{11/12+ε})` for every `ε > 0`, with no hypothesis. It is `psi_isBigO_of_zeroFree` at `θ = 11/12`, with the half-plane from the pilot's `Eis.ne_zero_of_re_gt_eleven_twelfths` (`src/KubotaThetaProof.lean`, round 466). The file imports `HalfPlanePNT.lean` and `src/KubotaThetaProof.lean`; see the main README, round 467. All axioms are clean.

## PsiExponent.lean (round 469)

`PsiExponent.Theta` is the supremum of the real parts of the nontrivial zeros of `ζ`. `half_le_Theta` and `Theta_le` give `½ ≤ Θ ≤ 11/12`, the upper bound from the pilot's `Eis.ne_zero_of_re_gt_eleven_twelfths` (round 466). `psi_isBigO_Theta` is `ψ(x) − x = O(x^{Θ+ε})`, `psi_isBigO_of_zeroFree` at `Θ`; `psi_omega_Theta` is `ψ(x) − x = Ω±(x^{Θ−ε})`, the pilot's `PsiOmega.psi_omega` (round 220) at a zero with `Re ρ > Θ − ε`; `limsup_expo` joins them: `limsup log|ψ(x) − x| / log x = Θ`. See the main README, round 469. All axioms are clean.

## HalfPlaneLindelof.lean (round 470)

`HalfPlaneLindelof.zeta_bound_of_zeroFree`: if `ζ(s) ≠ 0` on `Re s > θ`, `0 ≤ θ < 1`, then for every `σ₀ > θ` and `ε > 0` there are `T` and `C` with `|ζ(σ + it)| ≤ C|t|^ε` and `1/|ζ(σ + it)| ≤ C|t|^ε` for `σ ≥ σ₀` and `|t| ≥ T`. The proof interpolates round 337's `logDeriv_le_of_zeroFree` against PNT+'s `LogDerivZetaBdd_of_Re_ge_three_halves` by the maximum modulus principle on a rectangle (`norm_le_interp`, `logDeriv_le_interp`), and bounds `log|ζ|` by the mean value inequality, its derivative in `σ` being `Re ζ′/ζ` (`hasDerivAt_log_norm`). `zeta_bound_eleven_twelfths` is the case `θ = 11/12`, from the pilot's `Eis.ne_zero_of_re_gt_eleven_twelfths` (round 466); `zeta_bound_Theta` is the case `θ = Θ` (round 469). See the main README, round 470. All axioms are clean.

## SmoothPerron.lean (rounds 472, 473)

`SmoothPerron.verticalIntegral_eq_smoothedSum` is PNT+'s `SmoothedChebyshevDirichlet` for any `f` with `f(0) = 0` and `L(f, σ)` absolutely convergent, `1 < σ ≤ 2`: `(1/2πi) ∫_{(σ)} L(f, s)𝓜(Smooth1)(s)X^s ds = Σ_n f(n)Smooth1(n/X)`. `verticalIntegral_shift` moves a vertical integral across a strip on which the integrand is complex-differentiable and tends to `0` uniformly as `|Im s| → ∞` (PNT+'s `DiffVertRect_eq_UpperLowerUs` and `HolomorphicOn.vanishesOnRectangle`). `smoothedSum_eq_verticalIntegral_left` combines the two for a function `L` equal to `L(f, s)` on `Re s > 1`, complex-differentiable on `Re s ≥ σ′` with at most linear growth there. `mellin_le_geom` bounds `𝓜(Smooth1)` on `Re s = σ ∈ (0, 1]` by `Kε^{−κ}(1 + |t|)^{−1−κ}`, the geometric mean of round 338's `MediumPNTW.MellinOfSmooth1d` and PNT+'s `MellinOfSmooth1b`, and `norm_smoothedSum_sub_le` bounds the cost of the smoothing by `B(3 log 2 · εX + 1)` when `|f(n)| ≤ B` for `n ≤ 3X`. Round 473 split the shift out of `smoothedSum_eq_verticalIntegral_left` as `verticalIntegral_integrand_shift`: the line moves from `Re s = 2` to `Re s = σ′` for any `L` complex-differentiable on `Re s ≥ σ′`, bounded on `Re s = 2`, with at most linear growth there. `DivisorExponent.lean` applies it to `g_k`, the entire part of `ζ(s)^k`.

## MertensExponent.lean (round 472)

`MertensExponent.mertens_isBigO_of_zeroFree`: if `ζ(s) ≠ 0` on `Re s > θ`, `0 ≤ θ < 1`, then `M(x) = Σ_{n≤x} μ(n) = O(x^{θ+η})` for every `η > 0`. The proof moves the smoothed Perron integral of `1/ζ` to `Re s = θ + η₀/4`, with `1/ζ = (s − 1)/Z(s)` through the pilot's entire `PsiOmega.Zr` and the bounds of `HalfPlaneLindelof.zeta_bound_of_zeroFree`. At `θ = 11/12` and at `θ = Θ` it needs no hypothesis. With the pilot's `MertensOmega.mertens_omega`: `limsup log|M(x)| / log x = Θ` (`limsup_mexpo`), `RH ⟺ Θ = ½` (`rh_iff_Theta_eq_half`), `RH ⟺ M(x) = O(x^{½+η})` for every `η > 0` (`rh_iff_mertens`), and the partial sums of `Σ μ(n)n^{−s}` converge for `Re s > Θ` and diverge for `Re s < Θ` (`moebius_tendsto_of_Theta_lt`, `moebius_not_tendsto_of_lt_Theta`), so the abscissa of convergence is `Θ` (`moebiusAbscissa_eq_Theta`). The convergence is Abel summation as in Mathlib's `LSeries_eq_mul_integral`, without its hypothesis of absolute convergence (`tendsto_partialSum_of_isBigO`).

## DivisorExponent.lean (round 473)

`DivisorExponent.divisor_isBigO_of_zeroFree`: if `ζ(s) ≠ 0` on `Re s > θ`, `0 ≤ θ < 1`, then for every `k ≥ 1` and `η > 0`, `Σ_{n≤x} d_k(n) = xP_k(log x) + O(x^{θ+η})`. Here `d_k` is the `k`-th Dirichlet power of `ArithmeticFunction.zeta` (`dk k`), and `P_k` (`Pk k`) is a real polynomial of degree `k − 1` with leading coefficient `1/(k − 1)!` (`natDegree_Pk_eq`, `coeff_Pk`). The proof writes `ζ(s)^k` as its principal part at `1` plus an entire `g_k` (`zeta_pow_eq`, by iterated `dslope` of `Z(s)^k` with the pilot's `PsiOmega.Zr`). It integrates the principal part exactly (`verticalIntegral_inv_sub_one_pow`, through `(s − 1)^{−m} = ∫_0^∞ u^{m−1}e^{−(s−1)u} du/(m − 1)!`, Fubini and Mathlib's Mellin inversion), moves the line for `g_k` to `Re s = θ + η₀/4` with `HalfPlaneLindelof.zeta_bound_of_zeroFree` (`norm_remainder_le`), and unsmooths by comparing two smoothed sums, since `d_k ≥ 0` (`tsum_smooth_le`, `le_tsum_smooth`). At `θ = 11/12` and at `θ = Θ` it needs no hypothesis (`divisor_isBigO_eleven_twelfths`, `divisor_isBigO_Theta`). See the main README, round 473. All axioms are clean.

## ChiPNT.lean (round 478)

`ChiPNT.logDeriv_le_of_zeroFree` is round 337's `HalfPlanePNT.logDeriv_le_of_zeroFree` for an entire `F` in place of `ζ`: if `F` has no zero in `Re s > θ ≥ 0`, `|F(s)| ≤ c_δ|Im s|` on `δ ≤ Re s ≤ 3`, `|Im s| ≥ 1`, for every `δ > 0`, `1/|F(3/2 + it)| ≤ A` and `|F′/F| ≤ C₀` on `Re s ≥ 3/2`, then `|F′/F(σ + it)| ≤ C log|t|` for `σ ≥ θ′ > θ` and `|t| > 3`, through PNT+'s `FinalBound` on the disc of radius `3/2 − θ` around `3/2 + it` (`disc_point`). `ChiPNT.sum_isBigO_of_zeroFree`: for `θ < 1` and coefficients with `f(0) = 0`, `|f(n)| ≤ Λ(n)` and `L(f, s) = −F′/F(s)` on `Re s > 1`, `Σ_{n≤x} f(n) = O(x^{θ+η})` for every `η > 0`; the proof is `MertensExponent.mertens_isBigO_of_zeroFree`'s, with `−F′/F` in place of `1/ζ` and the unsmoothing at `B = log 3X`. `ChiPNT.psiChi_isBigO_of_zeroFree` applies the two to `F = L(·, χ)` for a quadratic `χ ≠ 1`, with the pilot's `PsiOmega.norm_LFunction_le` for the growth; with the pilot's half-plane for the real characters (`Eis.RealChar.LFunction_ne_zero_of_isQuadratic`, round 477), `psiChi_isBigO_eleven_twelfths` needs no hypothesis. See the main README, round 478. All axioms are clean.
