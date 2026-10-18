# Ideas register: an exponent below 7/3 for prime moduli

README round 546 opens this register. The owner's instruction (2026-10-18) was: "Keep searching, do not give up until every idea is exhausted".

The goal is a density exponent below `7/3` near `σ = 5/7` for the characters mod a prime `q`, with `T = q^{o(1)}`. Through the stack's half-plane and round 520's `Linnik.linnik_of_charDensity`, that is a Linnik exponent below `7/3`.

Each idea carries one status:

- **CORE**: open, and tied to a named open problem; listed under "The cores".
- **OPEN**: no closing argument yet; more work is owed.
- **REDUCED**: shown to come down to a core.
- **CLOSED**: a recorded argument shows the idea cannot reach the goal alone, in the scope stated.
- **SURVEYED**: the literature was checked and nothing usable was found.

A closure is a statement about the idea as described, in the scope stated. It is not a claim that no variant can work. `idea_register.py` checks every quantitative closure marked [R*] in exact arithmetic.

## The cores

Each core gives an exponent below `7/3` in round 528's model, or kernel-checked where stated. None is known at the needed strength. The list is what this strand has found; it is not shown to be exhaustive.

1. **The `S₃` step.** Chen–Gupta–Li's first term `(qT)²|W|^{3/2}` at `q^{3−κ}`. This is joint cancellation in the line sums on the `q^{2/3}` lines of small height (SEVEN-THIRDS §§5–15, rounds 528–540). The sharpened target (round 535) is `S₃ ≤ q^{3−δ}` for sets of size `q^{2/3}` with minimal energy.
2. **`SIX(δ)`** for the critical blocks (rounds 541–542). Equivalent forms recorded so far:
   - the off-diagonal count of `x₁x₂x₃ ≡ y₁y₂y₃ (mod q)` over three intervals of length `q^{7/18}`;
   - a ternary additive divisor problem with shifts in `qℤ`;
   - through Mellin, a fourth moment of `L` twisted by a smooth sum of length `q^{7/18}`, with loss below `q^{1/6}` [R7].
3. **A fixed-modulus sixth moment** `Σ_χ |L(½ + it, χ)|⁶ ≪ q^{1+θ}` with `θ < 1/6` (round 544). Known: `θ = 1/3`. For `ζ` the analogue would be `M(1/2, 6) < 7/6`. The bound the exponent database's chapter 9 gives, by interpolating the fourth and twelfth moments, is `5/4` [R12].
4. **Large central values at `q^{1/12}`** (round 545). A power saving in the fourth moment's count of `|L(½ + it, χ)| ≥ q^{a}` for `a` near `1/12` suffices with Proposition 3.1. Core 3 and the uniform bound `c < 1/12` each give it. For `ζ`, the count of `1`-spaced `t ∈ [T, 2T]` with `|ζ(½ + it)| ≥ T^{1/12}` is `T^{2/3+o(1)}` by the fourth moment. None of the bounds evaluated from the database's chapters 8–9 improves it [R12].

**The common target, H\*** (README round 550; `sixth_moment.py` check (W)). Let `ν_c(σ) = 1/(2(2 − σ))`, the critical block's exponent (`7/18` at `σ = 5/7`). H\*(δ, w) says: among the detector's blocks of length `Q^ν` with `|ν − ν_c(σ)| ≤ w`, those large at `N^σ` number at most `Q^{6ν(1−σ)−δ}`.

- This is `SIX(δ)`'s large-values consequence, near the critical block only. In round 528's model with all four families, `δ = 1/100` and `w = 1/1000` give a maximum of `2.33010 < 7/3` over the grid.
- Each core gives it, near `σ = 5/7`, where it is needed:
  - core 2 by Chebyshev;
  - core 4 because at `ν = ν_c(σ)` the band's count `1 − 4a` equals `6ν_c(σ)(1 − σ)`, where `a = ν_c(σ)(σ − ½)` (`1/12` at `σ = 5/7`);
  - core 3 and the uniform bound `c < 1/12` through core 4;
  - core 1 through the squares of these blocks, which sit at the window's left end, where Chen–Gupta–Li's third term acts (round 528's socket (S)).
- H\* needs no piece longer than `Q^{ν_c+w}`. Core 4 gives it, but not conversely, and C9's hard range is not on its path.
- Its simplest instance: the number of `χ mod q` with `|Σ_{n∼N} χ(n)| ≥ N^{5/7}` at `N = q^{7/18}` is below `q^{2/3−δ}`. The fourth moment and the cube's mean value each give exactly `q^{2/3}` there, up to logarithms.

The kernel-checked conditional route is round 521's `LinnikDensity.linnik_of_critBound`. A uniform `|L(½ + it, χ)| ≪ (q(|t| + 2))^c` with `c < 1/12` gives `2 + 4c + η`. Known: `c = 1/6` (Petrow–Young), not in the stack; the stack proves `5/24 + ε`.

## A. Zero detection

- **A1. Littlewood's lemma with a mollified second moment (Selberg's method).** CLOSED [R1, R15c]. In the form `N(σ) ≪ q^{1−(2σ−1)θ}`, with a mollifier of length `q^θ`, the exponent at `σ = 5/7` is below `7/3` only for `θ > 7/9`. At `θ = 1/2` it is `11/4`. The explicit formula with test functions of Fourier support `s` would give the same exponent at `θ = s/2`, and `2` at `s = 2` for every `σ`, if every zero off the line contributed positively. They need not: for the Fejér kernel `φ(x) = (sin πsx/πx)²`, the weight `2 Re φ(x + iy)` of an off-line zero changes sign as `x`, its scaled ordinate, varies, once `|y|` is large. Even at `θ = 51/101`, the twist length up to which Bui–Pratt–Robles–Zaharescu obtain the twisted second moment at the central point (C14), the formula gives `277/101 ≈ 2.743` [R17a].
- **A2. Turán's power sums and the Halász–Turán method.** CLOSED at `σ = 5/7` for the bounds recorded with a range [R11]. The exponent database (§11.2) records Turán's `A(1 − η) ≤ 2 + η^{0.14}` for `η` small enough, and Halász–Turán bounds `A(1 − η) ≤ Cη^{1/2}` for sufficiently small `η`. Its Table 11.2 gives three with a range. Ford's `58.05(1 − σ)^{1/2}`, stated for `1/2 ≤ σ ≤ 1`, gives more than `31` at `σ = 5/7`. Heath-Brown's `6.42(1 − σ)^{1/2}` and Pintz's `3√2(1 − σ)^{1/2} + 18(1 − σ)` are stated for `σ ≥ 9/10` and `σ ≥ 17/18`. These are bounds for `ζ`. This round did not reconstruct the method for the characters mod `q` at `σ = 5/7`.
- **A3. Detectors from `L′/L` with Heath-Brown's identity.** CLOSED as a route around the critical length. The smooth factors of the identity have arbitrary lengths, so smooth sums of length near `q^{7/18}` reappear. Detection through the explicit formula needs Turán's lemma (A2).
- **A4. A heavier mollifier, splitting each block into `d·m` pieces.** CLOSED. The piece `d ≍ 1` is the smooth sum of length `N` itself, which cannot be factored. A large value of the block can sit on that piece.
- **A5. Products of the critical block with other blocks.** CLOSED. A product is counted only when each factor is large. A zero detected by the critical block alone gives only the powers of that block, of lengths `7/9` and `7/6`, at the two ends of the window.

## B. Large values of the class-I polynomials

- **B1. The `S₃` step.** CORE 1.
- **B2. The fourth moment of the Gram matrix, `Tr(E⁴)`.** REDUCED. With the outer sum extended to all characters, `Tr(E⁴) ≤ (q − 1)·S₃′` for a sum of the `S₃` type. Without the extension it needs the same Jacobi-phase cancellation. In the trivial bound the shortfall is `q^{2/3}`.
- **B3. Bourgain-type energy dichotomy, with Halász–Montgomery and the energy.** CLOSED at `σ = 5/7`. With minimal energy, the inequality `|W|²V² ≤ |W|N² + |W|²N^{3/2}` needs `V > N^{3/4}`.
- **B4. Large values from a twelfth moment.** CLOSED for this height. Even a `q`-aspect twelfth moment `≪ q^{2+ε}` counts `|L| ≥ q^{1/12}` by `q`.
- **B5. Huxley's estimate, and a form of it with the half-plane's Gram entries.** CLOSED at `σ = 5/7` [R9].
  - In `seven_thirds.py`'s model, Huxley's good set (`HUX`) is the single point `7/6` at Ingham's level `t = 2/3`, and empty below it. Its second line has slope `4 − 6σ = −2/7`, above the mean value theorem's `−3/7`. So at `σ = 5/7` its good set lies inside the mean value theorem's at every `t`.
  - Put the half-plane's Gram entries `|M(η)| ≤ N^{1/12}q^{5/12+ε}` in place of `√q`. At `T = q^{o(1)}`, Huxley's argument by subdivision in `t` then reduces to Halász–Montgomery with those entries, which needs `l ≥ 35/29 > 7/6` (B8). A half-plane form of the stack's reflection route (round 526) was not derived.
  - Jutila's estimate and the other published shapes: B14.
- **B6. Burgess's method summed over the characters (a large-values Burgess bound).** CLOSED [R3, R5].
  - In the form derived this round, `|W| ≲ N^{2r−1}q^{1+1/r}V^{−2r−1}`, the exponent at `N = q^{7/18}`, `V = N^{5/7}` is `(2r − 6)/9 + 1 + 1/r`. It exceeds `1` for every `r ≥ 1`: checked for `r ≤ 10`, and for `r ≥ 3` the term `(2r − 6)/9` is nonnegative. The derivation's choice `A = Vq^{−1/r}` is at least `1` only for `r ≥ 18/5`.
  - Pointwise, Pólya–Vinogradov rules out large character sums only for `N > q^{7/10}`, Burgess with `r = 2` only for `N > q^{7/8}`, and Burgess with `r = 3` only for `N > q^{7/3}`.
- **B7. `SIX(δ)`.** CORE 2.
- **B8. Halász–Montgomery with Pólya–Vinogradov or the half-plane's line `1/12`.** CLOSED (SEVEN-THIRDS §3: it needs `N > Q^{35/29}`).
- **B9. The half-plane's pointwise bound in the dual sums.** CLOSED (SEVEN-THIRDS §6: `q^{31/9}`).
- **B10. Concentration (an uncertainty principle on `X(q)` and `F_q^*`).** REDUCED to B1. The critical configuration needs a function on `W` whose multiplicative Fourier transform is concentrated on `[N, 2N]`. The trace of the concentration operator, `|W|N/q`, does not forbid an eigenvalue near the top.
- **B11. Point–line incidences.** CLOSED (round 543: Stevens–de Zeeuw is out of range).
- **B12. An inverse theorem: a large `S₃` forces energy above the minimum.** CORE 1, in contrapositive form (rounds 534–535). Round 535's sharpened target is `S₃ ≤ q^{3−δ}` for the sets of size `q^{2/3}` with minimal energy. An inverse theorem with Proposition 10.2's minimal energy is that statement read backwards.
- **B13. The Frobenius norm of the off-diagonal Gram matrix, with minimal (flat) energy.** CLOSED as a route, recorded for its arithmetic [R6, R16]. A large set of size `K` needs a top eigenvalue `KN^{2σ−1}`. If `‖E‖²_F ≈ K²N`, at most `N^{3−4σ}` eigenvalues can have that size: `q^{1/9}` at length `q^{7/9}` and `q^{1/18}` at length `q^{7/18}`. That alone is no contradiction.
  - The premise, read as the upper bound `‖E‖²_F ≤ K²N·q^{o(1)}`, is a theorem when `K ≥ q^{2/3}` and `K ≥ N`. Darbar–Kerr–Munsch–Shparlinski (arXiv:2604.02960, Lemma 3.1) record a simplified version of Heath-Brown's 1979 Theorem 1 as `Σ_{r,s=1}^{R} |Σ_{n=1}^{N} α_n χ_r(n)χ̄_s(n)|² ≤ (N²R + NR² + NR^{5/4}q^{1/2})q^{o(1)}`, for `R` distinct characters, `N ≤ q` and `|α_n| ≤ 1`. Its last two terms are equal exactly at `R = q^{2/3}`, the critical count. Its first term, the diagonal's, is at most `NR²` when `R ≥ N`. So the premise holds at length `q^{7/18}`. At length `q^{7/9}` the first term `N²K` exceeds `K²N`, and the bound does not give it.
  - Where the premise holds, `‖E‖_op ≤ ‖E‖_F` and Halász–Montgomery give `RV² ≤ N² + N^{3/2}R`, hence `R ≤ 2N²/V²` only when `V > N^{3/4}`, i.e. `σ > 3/4` (as in B3). At `σ = 5/7` it gives nothing.
- **B14. The other large-values theorems of the exponent database (chapters 7 and 10), with `T` replaced by the conductor.** CLOSED at `σ = 5/7`, except for one theorem, which comes down to core 1 [R10].
  - These give `F ≥ 2/3` at every block length of the barrier `B`, wherever they apply: Heath-Brown's two forms (7.13, 7.14), Jutila's (7.16), the exponent-pair bound (7.11), Bourgain's (10.30, 10.31), Kerr's Theorem 5 (10.32) and Guth–Maynard's (10.28). Kerr's is used only where its condition forces `α > 0`. As transcribed, it admits `α < 0` for `τ < 8σ − 5`, where its bound would fall below the database's lower bound `min(2 − 2σ, τ)`.
  - Heath-Brown's second theorem (7.15) and Kerr's Theorems 2–4 need `σ > 3/4` or `σ > 25/32`.
  - Guth–Maynard's Theorem 1.1 (10.27) gives `29/45 < 2/3` at `7/9`. Its proof subdivides to `τ = 6/5`, and for prime `q` there is no subdivision (C5, E5).
  - The unsubdivided bound (10.28) gives exactly `2/3` at `7/9`, from its term `2 − 4σ + (4/3)τ`. In the model that term is Chen–Gupta–Li's `(qT)^{4/3}N^{2−4σ}`, the contribution of the `S₃` step. The other seven terms are below `2/3` there for `k ≤ 5`.
- **B15. `SIX(δ)` from the fourth moment and a pointwise bound.** CLOSED [R14a]. `Σ|D_N|⁶ ≤ max|D_N|²·(q + N²)N²` is below `q^{−δ}N⁶` at `N = q^{7/18}` only if `max_{χ≠χ₀}|D_N(χ)| < q^{5/18−δ/2}`. Burgess's best exponent there, at `r = 4`, is `71/192 ≈ 0.370`. Pólya–Vinogradov gives `1/2` and the trivial bound `7/18`. A Lindelöf-type bound `q^{7/36}` would suffice.

## C. The integral class and central values

- **C1. A fixed-modulus sixth moment.** CORE 3. Literature: no single-modulus bound better than `θ = 1/3` was found. Under GRH, Soundararajan's method gives `θ = 0`. Gao–Zhao (arXiv:2504.17905) reach `k ≤ 2` for a fixed modulus.
- **C2. Large central values at `q^{1/12}`.** CORE 4.
- **C3. Amplifying a set of characters.** CLOSED [R4]. With an amplifier of length `L` built from `R` characters, the off-diagonal is of random size `√(RL)` against the diagonal `L`. So it needs `L > R = q^{2/3}`, beyond the twist lengths of the twisted fourth moments surveyed (C7).
- **C4. One-sided distribution of `log|L|` (Radziwiłł–Soundararajan style).** CLOSED at this height. The deviation `log V = (log q)/12` is proportional to `log q`. With `P(χ) = Σ_{p≤x} χ(p)/√p`, moments of order `k < (log q)/(log x)` give savings of a power of `log q`, not of `q`.
- **C5. Fourth moments along cosets (Petrow–Young).** CLOSED for prime `q`: no coset of the characters mod `q` lowers the conductor.
- **C6. The half-plane together with subharmonicity of `log|L|`.** CLOSED. A zero at `β ≥ 5/7`, a large value at `½` and `|L| ≤ q^ε` on `Re s ≥ 11/12 + ε` are mutually compatible.
- **C7. Twisted fourth moments.** SURVEYED [R7, R13]. Core 2's Mellin form needs a twist of length `q^{7/18}`, with loss below `q^{1/6}`.
  - Blomer–Humphries–Khan–Milinovich (arXiv:1902.07042): "As an application, we obtain sharp upper bounds for the fourth moment twisted by the square of a Dirichlet polynomial of length q^{1/4}." In round 528's model, a bound of this shape at the detector's points gives the class-II line `1 − 4y(σ − ½)` for mollifiers up to `q^{1/8}`, without `FMx`'s `2x`. At `σ = 5/7` it still needs `y ≥ 7/18`, so the blocks contain `7/18`, a point of the barrier [R13a].
  - Zacharias (arXiv:1611.09582), prime `q`: error `(ℓ₁ℓ₂)^{3/2}L⁵q^{−η}` with `η = 1/14 − 3θ/7 = 11/448` at `θ = 7/64`.
  - Gao–Wu–Zhao (arXiv:2509.24690): an asymptotic for the fourth moment "mollified by a Dirichlet polynomial of length q^{1/22−ε}", for all moduli `q ≢ 2 (mod 4)`.
  - The `t`-aspect: Hughes–Young (arXiv:0709.2345), twists of length `T^{1/11−ε}`; Bettin–Bui–Li–Radziwiłł (arXiv:1609.02539), `T^{1/4−ε}`.
  - Gao–Zhao (arXiv:2507.18186): prime-power moduli.
- **C9. Core 4 through the approximate functional equation.** REDUCED to core 4 [R13]. It locates core 4's hard range.
  - A large `|L(½ + it, χ)| ≥ q^{1/12}` makes one dyadic piece `Σ_{n∼M} χ(n)n^{−1/2−it}`, `M ≤ q^{1/2}`, large.
  - Pieces with `M < q^{7/18}` are counted below `q^{2/3}` by the mean value of their cubes. The twisted bound of C7 reaches only `M ≤ q^{1/4}`.
  - At `M = q^{1/2}` the square has length `q` and value `q^{2/3}`, where the density term is exactly `2/3`. So powers of the piece cannot help there, and an unsquared count needs `LV(2/3, 2) < 4/3`. The mean value theorem gives `5/3`, Huxley `2` and Guth–Maynard's Theorem 1.1 `26/15`. For `ζ`, R12(d) records the database's exponent-pair bound above `2/3` in the count.
- **C10. `SIX(δ)` from equidistribution of `d₃` in every class.** CLOSED [R14b]. A saving `q^{−δ′}` in every class mod `q` gives `SIX(2δ′)`. At `X = N³ = q^{7/6}` that is level of distribution `6/7`. Fouvry–Kowalski–Michel (arXiv:1304.3199): "the exponent of distribution of the ternary divisor function d_3 in arithmetic progressions to prime moduli is at least 1/2+1/46"; and "when averaging over a fixed residue class", `1/2 + 1/34`.
- **C11. Upper bounds for product congruences in short intervals.** CLOSED [R15a]. Bourgain–Garaev–Konyagin–Shparlinski (arXiv:1203.0017, Theorem 19) bound the number `K_ν(p, h, s)` of solutions of `(x₁ + s)⋯(x_ν + s) ≡ (y₁ + s)⋯(y_ν + s) ≢ 0 (mod p)`, `1 ≤ x_i, y_i ≤ h`, by `(h^ν/p^{ν/e_ν} + 1)h^ν exp(c(ν) log h/log log h)`, with `e_ν = max{ν² − 2ν − 2, ν² − 3ν + 4}`. For `ν = 3`, `e₃ = 4`, and at `h = q^{7/18}` the bound is `q^{19/12+o(1)}`, above the expected `q^{4/3}`. `SIX(δ)` needs more than an upper bound. `χ₀` removes `N⁶/(q − 1)`, so a bound `C·N⁶/q` with `C > 1` leaves `(C − 1)N⁶`. What is needed is an asymptotic with a power-saving error.
- **C12. Moments averaged over the moduli.** CLOSED [R15b]. Chandee–Li–Matomäki–Radziwiłł (arXiv:2409.01457) recall that "In 1970, Huxley obtained a sharp upper bound for the sixth moment of Dirichlet L-functions at the central point, averaged over primitive characters χ modulo q and all moduli q ≤ Q". For one modulus, an average bound `Q^{2+o(1)}` gives at most `q^{2+o(1)}`: loss `1`, against the Weyl bound's `1/3` and core 3's `1/6`.
- **C13. Halász's mean-value theorem (pretentious distance) for the critical sums.** CLOSED. Halász bounds `Σ_{n≤N} f(n)` by `N(1 + M)e^{−M}` plus a small term, where `M` is the pretentious distance `D(f, n^{it}; N)²` minimized over `t`. Since `D² ≤ Σ_{p≤N} 2/p = 2 log log N + O(1)`, the bound saves at most a power of `log N`. `|Σ_{n∼N} χ(n)| ≥ N^{5/7}` needs a saving `N^{2/7}`.
- **C8. Variance of `d₃` in progressions to a single modulus.** SURVEYED [R8]. Nguyen (arXiv:2205.02354, Corollary 1) treats `X = d^c` with `c ∈ (k − 1, k)`. For `k = 3` that is `X ∈ (d², d³)`. It records Kowalski–Ricotta's prime-modulus range as `c ∈ (k − ½, k)`. `SIX(δ)` sits at `X = q^{7/6}`.
- **C14. A twisted second moment with a long twist (round 552).** REDUCED to core 2 [R17b]. Let `S_χ(N)` be the smooth sum of length `N = q^{7/18}`. If `|S_χ(N)| ≥ N^{5/7}`, then `|L(½ + it, χ)| ≥ q^{1/12−ε}` for some `|t| ≤ q^ε`. So H\*'s simplest instance follows from `Σ_χ |L(½ + it, χ)|²|S_χ(N)|⁴ ≪ q^{1+η+ε}N²`, averaged over `|t| ≤ q^ε`, with `η < 1/6`: the count is then at most `q^{1/2+η+ε}`. The twist `S_χ(N)²` has length `q^{7/9}`.
  - The large sieve gives `η = 5/18`. The route needs a saving of `q^{1/9}` over it.
  - Bui–Pratt–Robles–Zaharescu (arXiv:1808.10803) study the second moment "twisted by the square of an arbitrary Dirichlet polynomial", and "obtain an asymptotic formula provided that the length of the Dirichlet polynomial is less than q^{51/101} = q^{1/2 +1/202}".
  - Through Mellin, the same bound gives `Σ_χ |S_χ(N)|⁶ ≪ q^{1+η+ε}N³`, which is `SIX(1/6 − η)`. So the route is at least as strong as core 2.

## D. Restructuring the argument

- **D1. Another Linnik deduction.** CLOSED within the density framework. Zeros at `σ` contribute `q^{(A(σ)−L)(1−σ)}`, so the deduction needs `L > A(5/7)`.
- **D2. An auxiliary composite modulus `qr` (`r` prime to `q`), to borrow Chen–Gupta–Li's subdivision.** CLOSED [R2].
  - The characters mod `q` form the subgroup `X(q)` of `X(qr)`, and each coset of `X(r)` holds one of them. For `χ ≠ ψ` mod `q`, `χψ̄` has conductor `q` in any lift. So no subdivision of `X(qr)` into cosets lowers the conductor of the off-diagonal.
  - For the subdivided case, SEVEN-THIRDS §2 quotes "|W| ⪅ (qT)^ϵ q q₁^{1/3} T N^{2−4σ}". With modulus `qr = q^{1+η}` and `q₁ = q` that term is `q^{4/3+η}N^{2−4σ}`, or `q^{2/3+η}` at the critical point. `W` lies in one of the `r` cosets of `X(q)`, and there the term is `q^{4/3}N^{2−4σ}`, as it is mod `q` directly.
- **D3. A larger `T` for subdivision in `t`.** CLOSED [R2]. A `t`-interval of length `T₁ ≥ 1` has conductor `qT₁ ≥ q`. In the same term the factor `qT` grows with `T`, and so the term never drops below its value at `T = q^{o(1)}`.

## E. Structure particular to prime moduli

- **E1. Additive combinatorics in `X(q) ≅ ℤ/(q − 1)` (Freiman-type inverse theorems).** CLOSED at the critical point. Proposition 10.2 gives `W` minimal energy, so there is no additive structure to exploit. Darbar–Kerr–Munsch–Shparlinski (arXiv:2604.02960) prove "new zero-density estimates on average over sets of characters with a small product set". A set with a small product set has large energy, the opposite of the critical `W`.
- **E2. The arithmetic of Gauss and Jacobi sums (Stickelberger, Gross–Koblitz, Katz's equidistribution).** REDUCED to B12. These results concern sums over all characters, or over algebraic families. `W` is an arbitrary set of `q^{2/3}` characters, so they reach `W` only through a structure theorem for the sets on which `S₃` is large, which is B12. For scale, at the critical point [R17c]: discarding the Jacobi phases gives `N^{3/2}q² = q^{19/6}` (`seven_thirds.py` check (P)), and Chen–Gupta–Li's bound is `q³`. If the normalized phases `J(ψ₁, ψ₂)/√q` on the `q²` pairs behaved like independent random signs, `S₃` would be about `N^{3/2}q = q^{13/6}`. That is a heuristic, not a bound. *(Round 553: the survey behind this entry missed results over arbitrary sets. Lu–Zheng (arXiv:2005.14358) prove equidistribution of normalized Jacobi sums when the characters "run through arbitrary sets of nontrivial multiplicative characters", under `#A₁ ≥ q^{1/2+ε}` and `#A₂ ≥ (log q)^{1/δ−1}`, or `#A₁#A₂/q → ∞`. Lu–Zheng–Zheng (arXiv:1305.3405) and Xi (arXiv:1809.04286) prove earlier forms. These reach `W` directly. For fixed `χ₂` and `m`, the Jacobi sums in `S₃` form a weighted bilinear sum over the product set `(Wχ̄₂) × (χ₂W̄)`, and Parseval already saves `q^{1/6}` there. Summed over `χ₂ ∈ W` and the dual variable `m`, that bound gives `Nq|W|² = q^{28/9} > q³` [R18]. The shortfall is in the outer sums, which is core 1, so the reduction to B12 stands.)*
- **E3. Large smooth sums from aligned values `χ(p)` on small primes.** REDUCED to core 4: through Mellin, a large smooth sum is a large `L(½ + it, χ)`.
- **E4. Poisson summation on the critical smooth sums.** CLOSED: the dual has length `q^{11/18}`, at height `q^{7/18}`, and the fourth moment then gives `q^{8/9}`. *(Round 552: that is the mean value theorem's bound for the dual's fourth power, whose term `M⁴` is the principal character's. Poisson summation is an isometry here, `|S_χ(N)| = (N/√q)|D(χ̄)|` with `D` the dual sum, so the dual's exact fourth moment gives back `q^{2/3}` [R17d]. Either way there is no gain.)*
- **E5. Subgroups of `X(q)` (the order structure of `q − 1`).** CLOSED: Gram entries on a coset `χ · H_d` are `M(η)` with `η` still of conductor `q`.
- **E6. The `q`-analogue of van der Corput and the Postnikov–Korobov method (round 552).** CLOSED for prime `q`: these methods factor the modulus. Irving (arXiv:1503.07156): "We use the q-analogue of van der Corput's method to estimate short character sums to smooth moduli". Banks–Shparlinski (arXiv:1605.07553) derive "new bounds on short character sums when the modulus q has a small core", the core being the product of the primes dividing `q`. Chang (arXiv:1201.0299): "We establish new estimates on short character sums for arbitrary composite moduli with small prime factors". A prime `q` is its own core and is not `q^δ`-smooth.
- **E7. Base change to an imaginary quadratic field `K` (round 552).** CLOSED. The Hecke characters of `K` have an angular aspect, where subdivision is available. But for `q` unramified in `K`, the base change `χ ∘ N_{K/ℚ}` of `χ mod q` has conductor of norm `q²`, and `L(s, χ ∘ N) = L(s, χ)L(s, χχ_K)`. For `χ ≠ χ′` the Gram entry of the base-change family is a smooth sum of `(χχ̄′)(n)r_K(n)`, `r_K = 1 ∗ χ_K`, with dual length about `q²/N`, against `q/N` mod `q`. The base changes all have angular type `0`, so subdividing in that aspect does not split them.

## F. The half-plane `Re s > 11/12`

- **F1–F4.** CLOSED in SEVEN-THIRDS §3 and §6: class-II elimination, the off-diagonal on `Re s = 1/12`, higher moments with `μ(a)`, and the dual sums. In this register: C6, and B5 with the Gram entries `|M(η)| ≤ N^{1/12}q^{5/12+ε}`.

## G. Literature and horizon

- **G1.** The Analytic Number Theory Exponent Database (Tao–Trudgian–Yang): its blueprint lists zero density for `L`-functions as a topic in progress, so no `q`-aspect bound was found there. SURVEYED.
- **G2.** Chen–Gupta–Li's front matter: "After the preprint [2] by the first author was released, the other authors informed BC that they had independently obtained the exponent 7/3 in the zero density estimate." The two efforts are one paper; there is no separate method. SURVEYED.
- **G3.** Horizon scans of rounds 541–545 and 547: no improvement for prime moduli. SURVEYED.
- **G4. Large values of short character sums (round 551).** SURVEYED. The three arXiv searches of round 551 (listed in README round 551) returned 37 abstracts. They include lower bounds for maximal sums (Munsch, arXiv:1805.07163, by the resonance method, and several Omega results for sums with multiplicative coefficients), the distribution of short sums as the interval moves (Lamzouri, arXiv:1106.6072, for `log H = o(log q)`), equivalences among conjectures (Granville–Mangerel, arXiv:2112.12339), and Darbar–Kerr–Munsch–Shparlinski (B13, E1). No abstract among them describes a count, for one prime modulus, of the characters with `|Σ_{n∼N} χ(n)| ≥ N^{σ}` at `N` a power of `q` below the fourth moment's bound, which is what H\* asks.
- **G5. Horizon scan of round 552.** SURVEYED. Six arXiv queries sorted by submission date (listed in README round 552) returned five abstracts not on file. Ye (arXiv:2610.15989) treats zero density in short vertical strips; Iggidr (arXiv:2603.12159) complete mixed character sums; Matomäki–Teräväinen (arXiv:2605.27833) a multiplicative-function analogue of Linnik's problem; Pliego–Wang (arXiv:2610.11487) and Matomäki–Pandey–Pliego–Teräväinen–Wang (arXiv:2610.09567) short intervals. None of these abstracts describes a large-values bound for one prime modulus. Pliego–Wang would use one: "any improvement in large value estimates for character-twisted Dirichlet polynomials would lead to a corresponding improvement in the lower bound for H".
