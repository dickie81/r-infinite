# External: zeta23 (round 228)

These files build on zeta23, the Lean formalisation that accompanies Alpöge–Furman (arXiv 2608.13637). zeta23 lives in `anthropics/formal-math`, folder `zeta23`. It is Copyright 2026 Anthropic, PBC and released under the Apache License 2.0; its `Zeta23/FromPNTPlus/` files derive from PrimeNumberTheoremAnd, also Apache 2.0. `build.sh` copies zeta23's `LICENSE` and `NOTICE` next to the files it fetches.

| file | round | content |
|---|---|---|
| `SlogZeta.lean` | 228 | von Mangoldt's bound `|S(t)| ≤ C log t` for Mathlib's `riemannZeta`, in the pilot's terms; the 1ca wall law without `hSlog` |

## What is used from zeta23

`build.sh` compiles 50 zeta23 files at commit `fbdc36b`: the import closures of three results.

| result | zeta23 name | content |
|---|---|---|
| Montgomery–Vaughan | `Zeta23.MV.mv_hilbert` | the weighted Hilbert inequality `∃ C > 0, MVHilbert C` (C = 26) |
| Riemann–von Mangoldt | `Zeta23.RvM.riemannVonMangoldt` | `N(T, 2T) = (T/2π)ℓ₁(T) + O(log T)` and the local count `N(t, t+1] ≤ A₀ log(|t| + 3)`, given the Γ facts |
| the Γ facts | `Zeta23.gammaFacts` | Stirling for `μ(τ) = (1/2π)Re ψ(¼ + iτ/2) − log π/2π` and its integrals |

`SlogZeta.lean` uses the second and third, through their parts: the argument principle for `Λ = completedRiemannZeta` folded onto the right half-contour (`N_eq_halfContour_completedZeta`), the split `Λ'/Λ = ζ'/ζ + Γ_ℝ'/Γ_ℝ`, Backlund's bound on the horizontals (`backlund_horizontal`), the vertical side at `σ = 2` (`vertical_two`), the Γ side (`gamma_side`) and Stirling (`gammaFacts.stirling`). Montgomery–Vaughan is compiled but not yet used here.

## Building

```
../../build.sh    # the pilot's own files
./build.sh        # zeta23 and this directory
```

`build.sh` does three things:
- It fetches the 50 files at commit `fbdc36b` (Lean v4.33.0-rc2) into `upstream/`. Set `ZETA23` to a clone of `anthropics/formal-math` to use it; otherwise that one commit is fetched.
- It applies `zeta23_port.patch`, which ports those files to the pilot's toolchain. Four files change, all by Mathlib API drift; the top of the patch lists them. Each changed file carries a note saying so.
- It compiles the zeta23 files (with zeta23's own `relaxedAutoImplicit = false`) and this directory's files into `../../build`, then prints the axioms of the final theorems.

The zeta23 files print their own upstream warnings (deprecations, unused variables); they are compiled unedited apart from the patch. `SlogZeta.lean` prints none.

## SlogZeta.lean (round 228)

- `Ncnt_good`: at a height `T` that is not the ordinate of a zero, the pilot's count `Ncnt zetaOrd T` (zeros with `0 < γ < T`, with multiplicity) equals zeta23's `Ncount 0 T` (zeros with `0 < γ ≤ T`). Both use the multiplicity `(analyticOrderAt ζ ρ).toNat`.
- `Ncount_contour`: for good heights `T₁ < T₂` above Backlund's threshold, `|N(T₁, T₂) − ∫_{T₁}^{T₂} μ| ≤ (|C_B| log T₁ + π + |C_B| log T₂)/π`.
- `int_mu_near`: `|∫_a^b μ − (N₀(b) − N₀(a))| ≤ |C_S|` for `1 ≤ a ≤ b`, from Stirling's `μ(τ) = (1/2π)log(τ/2π) + O(τ⁻²)` and `N₀′(r) = (1/2π)log(r/2π)`.
- `Slog_eventually`, then **`Slog_zeta`**: `∃ C ≥ 0, ∀ t ≥ 14, |S(t)| ≤ C log t`, where `S = N − N₀ − 7/8` is the pilot's `Sz zetaOrd`. For large `t`, sandwich `t` between good heights `T₃ ∈ [t−1, t]` and `T₂ ∈ [t, t+1]`. Below that, `S` is bounded by monotonicity of `N` and `N₀`.
- **`wall_law_zeta_S`**: `wall_law_zeta` (round 5) without the hypothesis `hSlog`. Littlewood's `S₁(T) = O(log T)` (`hS1log`) and the first-zero height stay named inputs.

All axioms are clean.
