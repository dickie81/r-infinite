# Lower order, higher rank: the residue-symbol order and the theta function's rank in the half-plane route

Side-branch note, 2026-10-22, on branch `claude/latest-commit-branch-ik1pj3` from round 637 (`34b94504`). It is not a README round, and it adds no Lean. Every number below comes from the three gate scripts in this directory (section 7).

**The question.** The owner's instruction: "Keep exploring your higher rank combined with lower order idea - take a branch if needed". The idea was stated in chat on 2026-10-19 and is not recorded elsewhere in the repo:
- With residue symbols of order `m`, the companion paper's extraction gives the boundary `1 − 1/(2m)`. Higher order therefore widens the boundary.
- The companion's dual step uses a theta function whose Fourier coefficients are the dual's Gauss sums. On GL₂ such coefficients are known for orders 2 and 3 only (Friedberg–Ginzburg, quoted in section 3).
- The opening proposed: a lower order, carried by a theta function of higher rank. Examples were the 4-fold cover of GL₃ for a quartic family (boundary `7/8`), and a cubic family (`5/6`) if Patterson's bias could be handled.

**Summary.**
1. Through this extraction only orders 2 and 3 can go below `7/8` (section 1). Order 2 is circular, so among these families the cubic one is the only candidate on this route. The quartic family is capped at `7/8` whatever its dual step.
2. Poisson summation turns the Möbius function into a Gauss sum: `μ(n)G(χ_n)` equals `G(χ_nρ_n)` (with `ρ = χ^{N/2}` the quadratic character) up to Hecke and residue-class factors. This is verified exactly for orders 2, 3, 4 and 6, the paired form included (section 2). The dual is then:
   - a cubic Gauss sum for the sextic family (the companion paper);
   - a quartic Gauss sum for the quartic family;
   - for the cubic family, `α(n)·conj(G₃(n))²`, equivalently one sextic Gauss sum;
   - the Möbius function itself for the quadratic family.
3. Of the dual Gauss sums, the cubic one has a carrier on GL₂ and the quartic one has a carrier on GL₃ (Friedberg–Ginzburg, quoted in section 3). No carrier of degree below 4 was found for the cubic family's dual (section 3).
4. In a model of the dual step (section 4), a carrier of degree `d` needs `σ ≥ 1 − 2/d`. The sextic family then gets `11/12`, the companion's value. The quartic family (`d = 3`) and the cubic family (`d = 4`) both land exactly on the trivial boundary `1`. Any saving in the dual step makes them nontrivial. The quartic family reaches `7/8` at a saving `η = 1/2` (the dual's `L²` term cut to `L^{3/2}`) and never goes below it. The cubic family goes below `7/8` only with a saving `η > 3/5`.
5. Numerically, the Möbius weight removes the Patterson bias from the order-3, -4 and -6 Gauss sums (section 5). The cubic and quartic duals are at the random size: within `0.74`–`0.89` of the baseline. What blocks these routes is the degree of the carriers, not a main term.

## 1. The extraction exponent for order `N`

The family is round 288's family with the sextic symbol replaced by the order-`N` symbol, over a field containing the `N`-th roots of unity (`ℚ(ω)` for `N = 3, 6`; `ℚ(i)` for `N = 4`): `A_Z(u) = Σ_𝔞 μ(𝔞)(u/𝔞)_N W(N𝔞/Z)`. `MeanSquare σ` is round 288's display with `N`-th powers.

Round 288's argument at `N`-th powers runs as follows. Average over `u = b^N` with `N(b) ≤ Y = Z^{(1+σ)/N}`, then apply Cauchy–Schwarz against `MeanSquare σ`. This gives a zero-free half-plane `Re s > θ_N(σ)`, where

`θ_N(σ) = (2N − 1 + (N − 1)σ)/(2N)`.

At `N = 6` this is round 288's `(11 + 5σ)/12` (gate O1). The bound from the inclusion–exclusion error, `Z^{1−(1+σ)/(2N)+ε}`, is below the main term for every `σ ≥ 0`, as at `N = 6`.

| `N` | `θ_N(0)` | `σ` with `θ_N(σ) < 7/8` | `σ` with `θ_N(σ) < 0.8748867` (Sang) |
|---|---|---|---|
| 2 | `3/4` | `σ < 1/2` | `σ < 0.499547` |
| 3 | `5/6` | `σ < 1/8` | `σ < 0.124660` |
| 4 | `7/8` | none (equality at `σ = 0`) | none |
| 5, 6, 8, 10, 12 | `9/10` … `23/24` | none | none |

So only `N = 2` and `N = 3` can go below `7/8` through this extraction (gate O2). `N = 4` reaches `7/8` only in the limit `σ → 0`. The cap holds whatever the dual step is, because it comes from the extraction alone.

**`N = 2` is circular on this route** (CLAUDE.md Check 9(c)). The quadratic Gauss sum `G₂(n)` is fixed by `n mod 4`, while `μ(n)` is not (gate A5). The Poisson dual of the quadratic family therefore carries the Möbius function again, twisted by quadratic characters. The family is self-dual and has no independent second representation.

## 2. Möbius absorption: the dual coefficient at each order

Poisson summation in `u` leaves, for each column `n`, the factor `μ(n)` times the normalized Gauss sum of `χ_n = (·/n)_N`. The companion's paired identity is the case `N = 6` (round 304's `paired_gauss`).

At a prime, two facts combine:
- Hasse–Davenport's product formula.
- The sign in Weil's Jacobi-sum character: `J(χ^a, χ^b) = −χ^{a+b}(−1)·J_W(a, b)`, with `J_W` a Grössencharacter.

So every quotient `G(χ^a)G(χ^b)/G(χ^{a+b})` is `−1` times a Hecke character at each prime: a factor `μ`. (Weil's normalization is recalled, not re-read here; its consequences at orders 3 and 4 are gates A1 and A6.) Modulo Hecke characters, `h_a := μ·G(χ^a)` then satisfies `h_a h_b = h_{a+b}`. With the quadratic Gauss sum fixed by residue classes, this gives

`μ(n)G(χ_n) = (Hecke character)·(unit fixed by n mod 4 or 8)·G(χ_nρ_n)`, with `ρ_n` the quadratic symbol (`χ_n^{N/2}` when `N` is even).

For squarefree moduli, `identities.py` checks the following exactly. It covers every squarefree primary modulus of norm `≤ 2500`: 338 over `ℤ[ω]` (49 primes, 7 inert) and 441 over `ℤ[i]` (50 primes, 8 inert). Conjugate pairs `π·π̄` are included. Notation: `α(n) = n/|n|` for the primary generator, and `G_d` is the normalized order-`d` Gauss sum with the companion's additive character.

| Gate | Field | Identity | Reading |
|---|---|---|---|
| A1 | `ℤ[ω]` | `G₃(n)³ = μ(n)α(n)` | the Möbius sign is the cube of the cubic Gauss sum |
| A2 | `ℤ[ω]` | `μ(n)G₃(n) = α(n)·conj(G₃(n))²` | cubic family: the dual is a product of two cubic Gauss sums |
| A3 | `ℤ[ω]` | `μ(n)G₆(n) = c(n)α(n)·conj(G₃(n))·G₂(n)`, `c` a cube root of unity fixed by `n mod 4` | sextic family: one cubic Gauss sum, the companion's absorption |
| A4 | `ℤ[ω]` | `μ(n)G₃(n) = c(n)α(n)·conj(G₆(n))·conj(G₂(n))`, `c` fixed by `n mod 4` | cubic family: equivalently one sextic Gauss sum |
| A5 | `ℤ[ω]` | `G₂(n)` fixed by `n mod 4`; `μ(n)` not | quadratic family: the Möbius function stays |
| A6 | `ℤ[i]` | `G₄(n)² = c(n)μ(n)α(n)G₂(n)`, `c = ±1` fixed by `n mod 8`; `G₂(n) = 1` | the Möbius sign is the square of the quartic Gauss sum |
| A7 | `ℤ[i]` | `μ(n)G₄(n) = c(n)α(n)·conj(G₄(n))·conj(G₂(n))`, `c = ±1` | quartic family: one conjugate quartic Gauss sum |
| A8 | `ℤ[ω]` | `μ(z₁)μ(z₂)G(χ_{z₁}χ̄_{z₂}) = a(z₁)·conj(a(z₂))`, `a(n) = α(n)·conj(G₃(n))²`, exactly | the cubic family's paired coefficient; cubic reciprocity removes the cross term |
| A9 | `ℤ[i]` | the same with `b(n) = α(n)·conj(G₄(n))·conj(G₂(n))` and a sign fixed by `(z₁, z₂) mod 8` | the quartic family's paired coefficient |

- A0 checks the composite Gauss sums against brute-force sums over `O/n` on 584 moduli (error `≤ 6·10⁻¹²`).
- A8 and A9 use brute force over `O/(z₁z₂)`: 464 and 648 coprime pairs, with one or two split primes in each column and `N(z₁z₂) ≤ 3000`.

The order of the dual Gauss sum is `N' = N/2` for `N ≡ 2 (mod 4)`, `N` for `4 ∣ N`, and `2N` for `N` odd. For `N = 2` it is the Möbius function. A cubic dual (`N' = 3`) occurs only at `N = 6` among the orders listed (gate O3). So, among families twisted by one power-residue symbol, the sextic family is the one whose absorbed dual is a single cubic Gauss sum.

## 3. The carriers

The companion's dual step uses an automorphic object whose Fourier coefficients are the dual's Gauss sums, together with a summation formula.

- **Kazhdan–Patterson, as stated in Y. Cai's slides** ("Fourier Coefficients for Theta Representations on Metaplectic Groups", BIRS, 2016-07-26): "When n = r or n = r + 1 (in this case, only for certain covers), uniqueness of Whittaker models holds for Θr." Also: "When n = r, the Whittaker coefficients are expressed in terms of nth order Gauss sum."
- **Order 3 (the sextic family).** Kubota's cubic theta on GL₂ (`n = 3 = r + 1`), with Patterson's coefficient formula. This is the companion's carrier, proved in the stack as `Eis.kubotaTheta` (round 466). Degree 2.
- **Order 4 (the quartic family).** S. Friedberg and D. Ginzburg, "Metaplectic theta functions and global integrals" (arXiv:1403.3929). Their Section 2 reads: "the representations Θ v have a unique Whittaker model for n = 3 or n = 4 (for n = 4 this requires that c be odd; see [10] Corollary I.3.6). However, for n> 4 the model is no longer unique." This is on the `n`-fold cover of GL₃. Their Section 5 reads: "the only coefficients τ (m, 1) of the theta function on the 4-fold cover of GL3(FS) that are not zero are those that occur when each prime dividing m occurs to a power congruent to 0 or 1 modulo 4. Moreover, at prime powers we have τ (p4k, 1) = |p|k τ (p4k+1, 1) = |p|k−1/2¯g(p)." The text extraction flattens the exponents: `τ(p^{4k}, 1) = |p|^k` and `τ(p^{4k+1}, 1) = |p|^{k−1/2}·ḡ(p)`. So at primes the first-row coefficients are conjugate normalized quartic Gauss sums, the coefficients that A7 leaves in the quartic family's dual. Degree 3.
- **Order 6 (the cubic family).** No theta function with sextic Gauss-sum coefficients was found. Friedberg–Ginzburg, Section 5: "It is a difficult problem to determine the Whittaker coefficients τ (r1,r 2) of functions in the space of Θ for n> 4; even on GL2 the analogous coefficients are not determined (there for n> 3)." The 3-fold cover of GL₃ does not carry the cubic dual in its first row. Same section: "τ (m, 1) = 0 unless m is a unit times a perfect cube" (Proskurin; Bump–Hoffstein). The carrier found is the Rankin–Selberg product of two cubic theta functions, since `μG₃ = α·conj(G₃)²` (A2). Degree 4. De Faveri's paper (arXiv:2610.04045, as quoted in round 311) says the lower bounds for the cubic and quartic large sieves "are obtained from biases coming from higher order Gauss sums, which are detected via Rankin–Selberg theory [32] applied to metaplectic forms [9, Section 5]".
- **Order 2.** None needed and none useful: the dual is `μ` (A5).

## 4. A model of the dual step

Take the companion's `DualMeanSquare` at the block `B = F = 1` (round 305): rows `k` with `N(k) ≤ H = X^{1−σ}`, columns `n ~ X`, target `X²`.
- A summation formula of degree `d` at modulus `k` turns a column sum into `X/H^{d/2}` times a dual sum of length `L = H^d/X`.
- The large sieve over the `H` rows bounds the dual sums' mean square by `HL + L^{2−η}`. At `η = 0` this is the generic `(H + L)L`, sharp for general coefficients; `η > 0` is a saving on its `L²` term.
- The rows' total is `XH + X²H^{−d}L^{2−η}`, within `X²` iff `σ ≥ σ_min(d, η) = 1 − (2 − η)/(d(1 − η))`.

| Family | Carrier degree `d` | `σ_min` at `η = 0` | `θ_N(σ_min)` | Saving `η` needed to go below `7/8` |
|---|---|---|---|---|
| sextic (`N = 6`) | 2 (cubic theta, GL₂) | `0` | `11/12` | none possible (`θ₆ ≥ 11/12`) |
| quartic (`N = 4`) | 3 (theta on the 4-fold cover of GL₃) | `1/3` | `1` | none possible: `7/8` at `η = 1/2`, never below |
| cubic (`N = 3`) | 4 (Rankin–Selberg of two cubic thetas) | `1/2` | `1` | `η > 3/5`; `5/6` as `η → 1` |
| cubic (`N = 3`) | 5 (sextic theta, GL₅) | `3/5` | `31/30` | `η > 19/27` |
| `N = 5, 8, 10, 12` | 9, 7, 4, 11 | | `> 1` | |

Gates O4 and O5 check the table in exact arithmetic.
- The sextic row reproduces the companion's `11/12`, which is the model's consistency check.
- The two lower-order families sit exactly on the trivial boundary.
- A degree-`d` carrier's dual is longer than the family of rows (`L > H`) as soon as `H > X^{1/(d−1)}`. That is the regime where the generic sieve pays `L²`.

**Scope (CLAUDE.md Check 9(a)).** This is a model of one step, not a statement about the route. It leaves out:
- the companion's induction on row lengths, its cube reduction and its transfer estimates (Propositions 5.1 and 5.4; rounds 314–326), which might shorten the duals;
- any structure of the dual coefficients beyond the generic sieve. Section 5 suggests there is some: they are bias-free;
- carriers not listed here;
- families not twisted by a single power-residue symbol.

For the last item, the multi-variable families computed in chat (the `r`-variable product family with `r` Poisson variables) have dual mean squares of size at least `Z^{r+1}` against the target `Z²` in the same model. The computation is not gated here.

## 5. Numerics: the Möbius weight removes the Patterson bias

`bias.py` computes `T_w(k; Z) = Σ_{N(n)≤Z} w(n)·Gtilde_d(k; n)` with sharp cutoffs. Here `Gtilde_d(k; n)` is the twisted normalized Gauss sum, `0` unless `(k, n) = 1`. The scope:
- all squarefree primary moduli to `X = 3·10⁵`: 84676 over `ℤ[ω]` (coprime to 6), 104263 over `ℤ[i]`;
- the weights `1`, the indicator of primes, and `μ`;
- 9 to 10 frequencies `k` for single sums, and every `k` with `0 < N(k) ≤ 300` for the mean squares (1074 over `ℤ[ω]`, 948 over `ℤ[i]`).

`bias_gates.py` checks the following.
- **B1.** Without weights the sums grow at Patterson's exponents `1/2 + 1/d`. At the 16 frequencies with `|T| ≥ 4√X`, the log-log slopes over `[X/64, X]` are `0.817`–`0.841` for `d = 3` (exponent `5/6`) and `0.723`–`0.769` for `d = 4` (exponent `3/4`).
- **B2.** With `μ` there is no growth beyond the random size. All 29 Möbius sums have `|T_μ| ≤ 461`, below `2√(#moduli)`. At `k = 1` the cubic sums give `|T_μ| = 184` against `|T_one| = 7166`.
- **B3.** The bias follows the weight's mass, with the same phase. At the untwisted frequencies, `T_prime/T_one` is `0.308` (argument `0.0°`) against the mass ratio `0.3069` over `ℤ[ω]`, and `0.235` (`−3.3°`) against `0.2495` over `ℤ[i]`. The Möbius masses are `−172` and `−37`.
- **B4.** The duals' mean squares with `μ` are at the random size: `0.85`–`0.89` of the baseline (number of `k` × number of moduli) for the cubic dual, `0.74`–`0.84` for the quartic, `0.76`–`0.93` for the sextic, at `Z = X/8 … X`.
- **B5.** Without `μ` the excess grows by `2^{2/d}` per doubling: `1.575`–`1.590` against `1.587` for `d = 3`, `1.405`–`1.426` against `1.414` for `d = 4`, `1.169`–`1.252` against `1.260` for `d = 6`. That is the square of the bias `Z^{1/2+1/d}`.

**Reading.**
- B3 says the theta function's residue weights the moduli by a mean field, of size about `N(n)^{−1/6}` at order 3. A weight's bias is then its own mean against that field.
- With `μ`, that mean is a Möbius sum: the sum the family is built to bound. The family's `N`-th-power members and its dual's theta residues carry the same quantity. Compare Hamdar's first moment of the cubic family, quoted in the register (STRUCTURAL-REVIEW §6, round 506's bullet): "a main term of the principal sum which comes from cubes, and the contribution from infinitely many residues of Dirichlet series of cubic Gauss sums to the dual sum".
- So at the sizes computed, the cubic and quartic families' duals have no main term in the way. The absorbed coefficients also avoid the biased configurations behind de Faveri–Dunn–Hoffstein's lower bounds for the cubic and quartic large sieves (round 311). What these routes lack is a carrier of low degree, or a saving on a high-degree one.
- This is numerical evidence at `X = 3·10⁵`, not a proof that the dual mean squares hold.

## 6. Outcome, register entry and signals

**Outcome, scoped.** On the companion's route, with the carriers of section 3 and the model of section 4, higher rank combined with lower order does not narrow the strip below `7/8`.
- The quartic family is capped at `7/8` by its extraction (section 1). With the carrier on the 4-fold cover of GL₃ it gives exactly the trivial boundary in the model. It would reach `7/8`, an independent route to the release's boundary, with a square-root saving in its GL₃ dual step.
- The cubic family is the one family that could go below `7/8`. Its dual is `α(n)·conj(G₃(n))²` (A2, A8). In the model of section 4 it needs either a carrier of degree below 4 for that product, or a saving `η > 3/5` on the degree-4 dual.

**Register entry** (CLAUDE.md Check 9(b)). This note adds a sub-entry under "The zero-free strip below `7/8`" in STRUCTURAL-REVIEW §6:
- **Missing Prop:** the cubic family's dual mean square at some `σ < 1/8`. At the block `B = F = 1` it reads: `Σ_{0<N(k)≤X^{1−σ}} |Σ_n a(n)χ_n(k)W(N(n)/X)|² ≪ X^{2+ε}`, with `a(n) = α(n)·conj(G₃(n))²` and `χ_n` the cubic symbol. The full display would mirror round 305's `DualMeanSquare` with cubic symbols.
- **Sockets:** none at order 3. The order-6 chain is the template: round 288's `Eis.ne_zero_of_meanSquare` (extraction) and round 310's `Eis.meanSquare_of_dualMeanSquare` (Poisson reduction). The order-3 versions would take cubes in place of sixth powers (`θ₃(σ) = (5 + 2σ)/6`), with the paired identity A8.
- **Attack notes:**
  1. A summation formula for `α·conj(G₃)²` of degree below 4. None was found; the 3-fold cover of GL₃ is ruled out for the first row.
  2. A saving `η > 3/5` on the Rankin–Selberg dual. Section 5's bias-free structure is the evidence that the truth has room.
  3. An induction on row lengths with transfer estimates at order 3, after the companion's Sections 5–7.

**Signals** (CLAUDE.md Check 9(c)).
- The order-`N` family's mean square is an auxiliary signal for `N = 3, 4, 6`. Its Poisson dual has a Möbius-free second representation (A2/A8, A7/A9, A3).
- For `N = 2` it is circular (A5).

## 7. Reproduce

From this directory:

```
python3 identities.py      # gates A0-A9, about 6 s (compiles periods.c with gcc into a temporary directory)
python3 orders.py          # gates O1-O5, exact arithmetic
python3 bias_gates.py      # gates B1-B5 on the committed bias_w_3e5.json and bias_i_3e5.json
```

To regenerate the two JSON files:

```
gcc -O2 -o periods periods.c -lm
./periods w 300000 > periods_w_3e5.txt     # about 4.5 min
./periods i 300000 > periods_i_3e5.txt     # about 4.5 min
python3 bias.py w periods_w_3e5.txt 300000 300 bias_w_3e5.json
python3 bias.py i periods_i_3e5.txt 300000 300 bias_i_3e5.json
```

The files:
- `gausslab.py`: brute-force power-residue symbols and Gauss sums over `O/n`, the reference for A0, A8 and A9.
- `periods.c`: Gauss periods at split primes.
- `composite.py`: inert primes, and composite moduli by twisted multiplicativity.
- `bias.py`: the weighted sums and the dual mean squares.

**Horizon scan, 2026-10-22.**
- `github.com/openai/math` is at `1581d4c` (`git ls-remote`), as recorded in rounds 471 and 496.
- Web searches for lower-order families, quartic and GL₃ theta functions, and zero-free half-planes from cubic families found no result that fills a socket of the register or contradicts it.
- One related remark: Hamdar (arXiv:2509.06152) notes that the link from Dirichlet series of Gauss sums to theta functions is known for cubic Gauss sums only. This was read in a search summary, not in the paper.

## Check 4 and bearing on RH

**Check 4.**
- Acknowledged:
  - the extraction at `N = 6` (round 288);
  - the companion's absorption and paired identity (round 304);
  - the sieve bounds and lower bounds of de Faveri, Dunn–Radziwiłł, de Faveri–Dunn–Hoffstein and Xu–Sang (rounds 311 and 496);
  - Hamdar's cube/residue cancellation (register, round 506);
  - the literature on the carriers (Kazhdan–Patterson, Patterson, Proskurin, Bump–Hoffstein, Friedberg–Ginzburg);
  - the exponents of Patterson-type biases [recalled: the first pole of the order-`d` Kubota series].
- New here:
  - the extraction exponent `θ_N(σ)` and its thresholds for every order;
  - the absorption rule `μG(χ) ≐ G(χρ)` and its exact verification at orders 2, 3, 4 and 6, the paired forms at orders 3 and 4 included;
  - the identification of the quartic family's dual with the first-row coefficients of the theta function on the 4-fold cover of GL₃;
  - the degree model with its savings table;
  - the numerics showing that the Möbius weight removes the Patterson bias, and that the bias follows the weight's mass.

**Bearing on RH: none.** The note maps a method and isolates a target. It gains or verifies no constraint on zeros.
