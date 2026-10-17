# Past 7/3: where the exponent sits for prime moduli, and what the stack's inputs do there

README round 528. This is a paper analysis with an exact-arithmetic check of a model (`seven_thirds.py`). Nothing in it is machine-checked in Lean, and it has not been refereed. It attacks the open step that round 527's next step names, at the owner's request "Push past 7/3", in the form the owner chose: "Try on paper to replace subdivision in the Guth–Maynard argument with a Huxley-style reflection." No proof emerged. Section 6 records how far the attempt got.

Notation as in `ARGUMENT.md`. `Q = qT`; for Linnik's exponent `T = O(log q)` (round 519's Lean route), so exponents are powers of `q` up to `q^{o(1)}`. A Dirichlet polynomial `Σ_{n∼N} b_n χ(n)` with `|b_n| ≤ 1`, `N = Q^ℓ`, is *large* at `χ` when its modulus is at least `V = N^σ`; a large-values estimate bounds the number `|W|` of such characters.

## 1. The question

The stack proves Linnik's exponent `12/5 + η` (round 527, `LinnikTwelve.linnik_twelve_fifths`). Chen, Gupta and Li (arXiv:2507.08296v2, a preprint) prove the density exponent `7/3`, and with the stack's half-plane their Corollary 1.4 gives `7/3 + ε` (`ARGUMENT.md` §6). Going below `7/3` needs a density exponent `A(σ) ≤ 7/3 − δ` on all of `1/2 ≤ σ ≤ 11/12` for every modulus, prime moduli included.

## 2. Where 7/3 comes from

Read from the PDF's text layer of v2 (spaces and exponents restored).

- Their Proposition 3.1 is the bound with no subdivision: "Let σ ∈ [7/10, 4/5] … If |S_N(t,χ)| ≥ N^σ/6 for all (t,χ) ∈ W and N ≥ (qT)^{2/3}/2, we have |W| ⪅_ϵ N^{2−2σ} + (qT)^{1/2}N^{3−4σ} + (qT)^{4/3}N^{2−4σ}." Their Theorem 1.1 improves it by splitting the characters into cosets of the characters mod a divisor `q₁ | q` (Lemma 3.3). For prime `q` the divisors are `1` and `q`. With `T` small, the case `q₁ = q > N^{6/5}` of their proof gives "|W| ⪅ (qT)^ϵ q q₁^{1/3} T N^{2−4σ}", which is Proposition 3.1's third term again.
- §2, p. 8: "It appears to be difficult to find an analogous argument to Huxley's in this setting to improve the estimate when there is no subdivision available."
- Remark 11.2: "The terms that set the limitations on our bounds are the first two terms, (qT)^2|W|^{3/2} and qT|W|N^{3−2σ}." These are terms of their (11.2), `S₃ ⪅ (qT)^2|W|^{3/2} + qTN|W|^{1/2}E(W)^{1/2}`.
- Remark 12.3: "Notably, this happens for prime moduli q. In this case, the critical situation is at σ = 5/7 with N = q^{7/9} and |W| = q^{2/3}. This is a case where our lack of subdivision causes us to do worse as the largest term is q^{4/3}N^{2−4σ} = q^{2/3}, which comes from our S3 bound, S3 ⪅ (qT)^2|W|^{3/2}. This term corresponds to square root cancellation in the R functions but no cancellation in the sums over m. To improve this term, we would need to find some joint cancellation in R and the m sums, which seems quite difficult."

**The triple point** (`seven_thirds.py`, check (T)). At `σ = 5/7` the target is `|W| ≤ Q^{2/3}`, and three constraints meet there.

- Ingham's count: the mean value theorem on blocks of length `Q^1` to `Q^{7/6}`, with Ingham's class-II count, gives `3/(2 − σ) = 7/3`.
- The mean value theorem's bound `Q·N^{1−2σ}` and Proposition 3.1's term `q^{4/3}N^{2−4σ}` both equal `Q^{2/3}` at `N = Q^{7/9}`. The density term `N^{2−2σ}` equals `Q^{2/3}` at `N = Q^{7/6}`. The good window `[7/9, 7/6]` has ratio exactly `3/2`.
- The fourth moment counts the integral class at `Q^{2/3}` with smoothing `Y = Q^{7/18}`. Here `7/9 = 2·7/18` and `7/6 = 3·7/18`.

## 3. The stack's inputs at σ = 5/7

None of them moves the triple point.

- **The half-plane as a class-II eliminator.** The pointwise bound `|L(a + it, χ)| ≪ Q^{μ(a)+ε}` from the half-plane, with `μ(1/12) = 5/12`, empties the integral class once `y(σ − a) > μ(a) + x(1 − a)`. At `σ = 5/7` that needs `y > 35/53` at best (line `1/12`, `x = 0`), and those blocks include `7/18`.
- **Round 525's Halász–Montgomery off-diagonal on `Re s = 1/12`.** It needs `N > Q^{35/29}` at `σ = 5/7`. Pólya–Vinogradov needs `N > Q^{7/6}`, and the mean value theorem works from `N = Q` on. So nothing new below `N = Q`.
- **Higher moments with the half-plane's `μ`.** `2k`-th moments by Hölder, `1 + (2k − 4)μ(a)` on `Re s = a ≥ 1/2`, give detectors whose block ranges still contain a point of section 4's set `B` (checked for `k ≤ 12` and `a` on a grid).
- **Round 526's Huxley estimate.** It gives `F(7/9) = 7/9 > 2/3`.

## 4. The barrier within the family

Let `B = {7/18, 7/9} ∪ [7/6, ∞)` (exponents of block lengths).

- **(B1)** Every finite sum of elements of `B` is `7/18`, `7/9` or at least `7/6`. At each such length, every large-values estimate in the family gives at least `Q^{2/3}`. The density term `2ℓ(1 − σ)` is in each, and the other terms were checked at `7/18` and `7/9`.
- **(B2)** Every zero detector in the family whose integral class is at most `Q^{2/3}` has a block range `[x, y]` that meets `B`. This was checked exactly over the affine pieces of each detector type, and on a rational grid for the moment type.

A zero whose blocks all lie in `B` is therefore counted at no less than `Q^{2/3}` by any power or product of its blocks, under any number of detectors. So **within this family no argument gives a density exponent below `7/3` at `σ = 5/7`.**

The family is the one listed in `seven_thirds.py`'s docstring:

- large-values estimates: the mean value theorem, Huxley, Halász–Montgomery with Pólya–Vinogradov or with the half-plane's line `1/12`, and Chen–Gupta–Li's Proposition 3.1;
- detectors with mollifier `X = Q^x` and smoothing `Y = Q^y`, whose integral class is counted by:
  - Hölder with the fourth moment and the mean square of `M_X^j`;
  - the pointwise bound `|M_X| ≤ X^{1/2}`;
  - the half-plane's pointwise bounds on any line `0 < a < σ`;
  - `2k`-th moments by Hölder.

It says nothing about arguments outside this family. Check (C) reproduces the stack's landed exponents inside the model: `36/13` (round 524), `87/35` (round 525) and `12/5` (round 527). With all four estimates, `7/3` is certified on a grid of `σ`.

## 5. The socket

Suppose Proposition 3.1's third term holds with exponent `c = 4/3 − κ` for prime `q` and `T = q^{o(1)}`. Its crossing with Ingham's `3/(2 − σ)` is at `σ₀ = (5 − 6κ)/(7 − 3κ)`, where both equal `7/3 − κ` (check (S)).

- For `0 < κ ≤ 1/39`, `σ₀` lies in Proposition 3.1's range `[7/10, 4/5]`, since `σ₀` decreases in `κ` from `5/7` to `7/10`. At `κ = 1/100`, `1/50` and `1/39`, one detector certifies `7/3 − κ` at `σ₀` and at every grid point of `[1/2, 11/12]`.
- For `κ > 1/39` the crossing leaves `[7/10, 4/5]`. Just below `σ = 7/10`, where Proposition 3.1 does not apply, Ingham's count gives `30/13`. At `κ = 1/20` the check finds no detector that certifies `7/3 − 1/20` at `σ = 11/16`.

So the socket is worth `7/3 − κ` for `κ ≤ 1/39`. Past that, the range `[7/10, 4/5]` of Proposition 3.1 is the limit. In Lean the socket is `Linnik.CharDensity (7/3 − κ + ε)`, fed to `Linnik.linnik_of_charDensity`. Reaching `7/3` itself in Lean means formalizing Proposition 3.1 (Chen–Gupta–Li §§4–11), which is not started.

## 6. The open step: the first term of S₃ for prime q

Take the model case of the `q` aspect: one point per character, at `t = 0`. Then `R(b) = Σ_{χ∈W} χ(b)` on `F_q^*`, and `C_q(x) = q·1_{x≡0} − 1` for prime `q`.

**Exactly.** The sum `I_m` of their Proposition 7.1 is `(N/q)³` times smooth weights in `m`, times

```
q·L(m) − φ(q)²|W|,   L(m) = Σ_{(b₁,b₂): b₁m₁ + b₂m₂ + m₃ ≡ 0} R(b₁) R(b₂/b₁) R̄(b₂).
```

The second term is exact by orthogonality, and summed over `m` it is `O(N³|W|/q)`, which is negligible. Their proof of Proposition 7.1 instead applies "the triangle inequality along with the fact that |C_q(m)| ≤ (m,q)". With absolute values, the off-line part (the `−1`) and the on-line part (`q·L(m)`) each reach the critical size `q²|W|^{3/2}`:

- Hölder along each line gives `Σ_line |RRR| ≤ q(|W|E(W))^{1/2}`.
- `E(W) ≥ |W|²`.
- There are `M³ = (q/N)³ = q^{2/3}` lines with `|m_i| ≤ M`.

For prime `q`, `S₃` is the weighted sum `(N³/q²) Σ_m L(m)` up to `O(N³|W|/q)`, so improving its first term is exactly a question about cancellation in the line sums `L(m)` on the `q^{2/3}` lines of small height.

**The Gauss-sum form.** By Poisson, `Σ_n w(n/N)²ψ(n) = (N/q)τ(ψ)F(ψ̄)` for `ψ ≠ 1`, with the dual sum `F(ψ) = Σ_{m≠0} ĥ(Nm/q)ψ(m)` of length `M = q/N`. With `τ(ψ₁)τ(ψ₂)τ(ψ₃) = qψ₃(−1)J(ψ₁, ψ₂)` for `ψ₁ψ₂ψ₃ = 1`, all nontrivial, the part of `S₃` with `χ₁, χ₂, χ₃` distinct is

```
(N³/q²) Σ_{χ₁,χ₂,χ₃ ∈ W distinct} ψ₃(−1) J(ψ₁, ψ₂) F(ψ̄₁) F(ψ̄₂) F(ψ̄₃),   ψ₁ = χ₁χ̄₂, ψ₂ = χ₂χ̄₃, ψ₃ = χ₃χ̄₁.
```

`|J| = q^{1/2}`. The Jacobi sums carry the "square root cancellation in the R functions", and the `F`'s carry the `m` sums.

**Three bounds at the critical case** (check (P); `|W| = q^{2/3}`, `N = q^{7/9}`, `M = q^{2/9}`; needed: `q^{3−κ}`):

- Keep the Jacobi phases and bound the `m` sums trivially, as Chen–Gupta–Li do: `q³`.
- Use the half-plane in the `m` sums. The stack's Lindelöf bound on `Re s > 11/12`, uniform in `q` (round 522), gives `|F(ψ)| ≪ M^{11/12+ε}q^ε` for every `ψ ≠ 1` by a contour shift. This is a pointwise saving `M^{1/12} = q^{1/54}` in the `m` sums. Used pointwise, it discards the Jacobi phases: `q^{31/9}`.
- Use the mean square of the `F`'s (`|F| ≈ M^{1/2}`), again discarding the phases: `q^{19/6}`.

Each route keeps one of the two cancellations. This round found no argument that keeps both.

**Plancherel over all lines.** Over all `q²` lines of `F_q²`, the line sums have square-root cancellation on average: `Σ|L|² ≈ q³|W|³` when `|R|² ≈ |W|`. The small-height lines are only `q^{2/3}` of them, and they may carry the critical mass `q^{8/3}|W|³ ≤ q³|W|³`. Plancherel and Cauchy–Schwarz alone lose `q^{1/6}`.

**Huxley's product trick.** Chen–Gupta–Li already use it in `S₂` (Remark 6.3: "we reintroduce our large Dirichlet polynomial here"). In `S₃` there are two places it could act, and neither helps.

- After the triangle inequality of Propositions 7.1 and 7.2, the sums over `b` are complete, and orthogonality evaluates them exactly. The critical term is the square of such an evaluated mean, `(φ(q)|W|)²`, in the first term of their Proposition 8.1. Weighting the characters by `|D(χ)|²/V² ≥ 1` can only raise it.
- Before the triangle inequality, the trick can act on `|F(ψ)|` in the Gauss-sum form, but only after the Jacobi phases are discarded. The large sieve it feeds gives at best the mean-square size of the `F`'s, which is the `q^{19/6}` route.

A Huxley-type step would need a positivity that keeps the Jacobi phases.

**Attack notes for the register.**

- (i) A restriction-type estimate for the line sums of `R ⊗ R ⊗ R̄` on lines of small height. Point–line incidence bounds over `F_p` (e.g. Stevens–de Zeeuw) are the nearest tool known here. They were not tried.
- (ii) A bilinear form in which the half-plane's `M^{11/12}` survives the Cauchy–Schwarz that keeps the Jacobi phases.
- (iii) The large-values property of `W` used inside `S₃` before Proposition 7.1.

## 7. Survey and horizon scan

**The machinery checklist** (CLAUDE.md, "Looking in the right places").

- Surveyed here:
  - the multiplicative large sieve (mean value theorem);
  - Huxley's reflection (round 526);
  - Halász–Montgomery with Pólya–Vinogradov and with the half-plane (round 525);
  - zero detectors with a mollifier and smoothing;
  - the fourth moment and `2k`-th moments by Hölder;
  - Guth–Maynard in Chen–Gupta–Li's form (§§2–12 read);
  - Heath-Brown's double zeta sum bound (their Theorem 10.1). As a large-values estimate through duality its term `|W|²N` needs `σ > 3/4`.
- Not surveyed:
  - additive, planar and higher-order large sieves;
  - metaplectic and cubic theta;
  - Hecke L-functions over imaginary quadratic fields;
  - Jutila's and Forti–Viola's methods beyond the exponents Chen–Gupta–Li quote (`2.460…`, `2.463…`);
  - Bourgain's large-values estimates;
  - sum-product methods for characters on short intervals.

**Horizon scan** (2026-10-17).

- arXiv, by web search: Chen–Gupta–Li v2 is the latest result for all characters mod `q` that the searches found. Darbar, Kerr, Munsch and Shparlinski (arXiv:2604.02960) prove zero-density estimates only "on average over sets of characters with a small product set". Runbo Li (arXiv:2610.18923) works in the `t` aspect. Cossaboom (arXiv:2609.27715) treats GL₂.
- `openai/math`: the local clone at `adc7f12` (2026-10-06), with a full grep of `CONTENTS.md`, and the first 100 000 characters of the served `CONTENTS.md`. Neither has a zero-density or Linnik entry beyond "003. The quasi-Riemann hypothesis".
- The Lean community: lean-lang.org lists a problem statement "Linnik's theorem (L = 5.5)". No zero-density formalization was found.

Nothing found improves `7/3` for prime moduli or contradicts section 4. The searches are not exhaustive.

## 8. How this was checked

- Chen–Gupta–Li v2 read directly from the PDF's text layer, §§1–12.
- `seven_thirds.py`: checks (T), (B), (S), (P) and (C) pass. Each of its six mutations fails at least one check:
  - `c` below `4/3`;
  - the mean value theorem without its density term;
  - a better half-plane (`μ` halved);
  - an integral-class count at `p = 4` with a free mollifier;
  - the socket at `κ = 1/20`;
  - the calibration at `12/5 − 1/100`.
- Section 3's claims about the stack's inputs are instances of the model's formulas, checked by (B). The Gauss-sum identity and the exact `C_q` split of section 6 are short computations written out in the round, not checked in code.

## 9. Round 529: a numerical probe of the line sums, and a conjecture

The owner asked to keep researching. `line_sums.py` computes the line sums `L(m)` of section 6 at `q = 10007` and `10009`. It uses `|W| = q^{2/3}`, `N = q^{7/9}` and `M = q/N = 8`, the critical case's proportions. It is a probe at one size of `q`, for families of `W` that are not large-values sets.

- **Lines through `(1, 1)`** (P1). The lines with `m₁ + m₂ + m₃ = 0` pass through `(b₁, b₂) = (1, 1)`, where `R(1)³ = |W|³`. That is `q|W|^{3/2}` exactly when `|W| = q^{2/3}`. About `M²` of the `M³` small lines are of this kind. In `S₃` they give `N|W|³`, which at the critical case is `q^{2/9}` below `q²|W|^{3/2}`.
- **Generic lines** (P2). Remove the points where `b₁`, `b₂` or `b₂/b₁` equals `1`, and the diagonal triple.
  - For random `W` the median `|L|` is `1.04·√q|W|^{3/2}`, the random-phase size. That is `√q` below the bound per line behind Chen–Gupta–Li's first term.
  - For an interval of exponents (consecutive powers of a generator), the largest line reaches `0.93·q|W|^{3/2}`.
  - For a progression of exponents with difference `⌊(q − 1)/|W|⌋`, the largest line reaches `1.21·q|W|^{3/2}`.
- **Energy** (P3). Take `W` a random subset of a subgroup of order `h`, with `h` from `556` to `q − 1`. Across this range `E(W)/|W|²` runs from `23` to `387`, and the mean `|L|` divided by `√q|W|^{1/2}E(W)^{1/2}` stays between `0.096` and `0.371`. At `|W| = q^{2/3}` even random `W` has `E(W) ≈ |W|⁴/q`.

**The conjecture.** For prime `q` and every `W`, the line sums on the small lines satisfy `|L(m)| ≲ q^ε√q|W|^{1/2}E(W)^{1/2}` on average. This is over the generic points; the lines through `(1, 1)` and the points where an argument is `1` are separate. Under the conjecture:

- the first term of `S₃` is at most `(N³/q²)M³√q|W|^{1/2}E^{1/2} = q^{3/2}|W|^{1/2}E^{1/2}`;
- that is below their energy term `qN|W|^{1/2}E^{1/2}`, since `N ≥ q^{1/2}`;
- their Proposition 3.1 loses the term `(qT)^{4/3}N^{2−4σ}` and keeps the other terms of their proof: `N^{2−2σ} + (qT)^{1/2}N^{3−4σ} + qTN^{9/2−7σ} + (qT)^{18/19}N^{(72−112σ)/19}`.

**The payoff** (check (E) of `seven_thirds.py`). In the model, one detector then certifies `30/13` on the whole grid, and about `2.2235` at `σ = 5/7`. The limit `30/13` is Ingham's count at `σ = 7/10`, the left end of Proposition 3.1's range.

**Why it is not proved here.**

- **Cauchy–Schwarz loses `q^{1/6}`.** Grouping by `(ψ₁, ψ₂)` gives, up to signs, `S₃ = (N³/q²)Σ_{ψ₁,ψ₂} J(ψ₁, ψ₂)τ_W(ψ₁, ψ₂)F(ψ̄₁)F(ψ̄₂)F(ψ₁ψ₂)`, where `τ_W(ψ₁, ψ₂) = #{χ ∈ W : χψ₁, χψ̄₂ ∈ W}`. Apply Cauchy–Schwarz over all of `X(q)²`, with
  - `Σ τ_W² = Σ_ψ r(ψ)³`, where `r(ψ) = #{χ ∈ W : χψ ∈ W}`;
  - `Σ |F(ψ̄₁)F(ψ̄₂)F(ψ₁ψ₂)|² ≈ q²M³`.

  The result is `qN^{3/2}(Σ_ψ r(ψ)³)^{1/2}`. Since `Σ r³ ≥ |W|³ = q²` at the critical case, this is at least `q²N^{3/2}`, a factor `q^{1/6}` above the critical `q³`.
- **The conjecture's cancellation is across the Jacobi sums.** For `W = H` a subgroup of order `h`, `L(m)` is `h³` times the number of points of the line in `(H^⊥)²`, which is `q/h² + O(√q)` by the Weil bound. Square-root cancellation among the `h²` Jacobi sums in that count gives `h²√q = √q|W|^{1/2}E(W)^{1/2}`. The Weil bound alone gives `h³√q`. For a general `W`, no route to the cancellation over triangles was found here.

## 10. Round 530: the conjecture fails as stated; large-values sets, and a major/minor split

- **A counterexample at this size** (P4 of `line_sums.py`). Take the interval polynomial (`b_n = 1` on `[N, 2N]`) and let `W` be its top `|W| = q^{2/3}` characters, a large-values set at `V ≈ N^{0.56}`. Its generic small lines have median `|L| ≈ 0.44` and `0.37` times `q|W|^{3/2}` at `q = 10007` and `100003`. A third, scratch-only run at `q = 400009` gave `0.27`. The ratio of round 529's conjecture is `6.7` and `10.2` at the two `q` in the gate, and `13.9` at `400009`, growing with `q`. So the conjecture of §9, stated for every `W`, fails for this set. The set consists of the characters whose dual sum `F(χ̄)` of length `M` is large, which is exactly Chen–Gupta–Li's "no cancellation in the sums over m". *(Round 531: that holds for P4's sharp cutoff, whose largest `|F|` is `0.80M` and `0.72M` at these two `q`. With the smooth weight `sin²` on `[N, 2N]` no character has `|F| > M^{0.7}` at `q ≤ 10⁶` (`gram_probe.py` G2). Chen–Gupta–Li's weight is smooth too. §11.)*
- **Concentrated pairs** (P5). Alternating projections between `b` on `[N, 2N]` and `W`, the top `|W|` characters of `D`, were run at `q = 10007`.
  - From `b = 1` they reach a concentration `Σ_W|D|²/((q − 1)‖b‖²) = 0.71` at `V ≈ N^{0.61}`. That set has `E(W) ≈ 111|W|²`, and a tenth of its generic small lines exceed `q|W|^{3/2}`.
  - From a random start they reach `0.43`, with line sums of random size.
  - The critical case needs concentration `1` at `V = N^{5/7}`; neither run is close.
- **Why size matters.** Coherent sums over `m` need the differences `ψ = χχ̄′` to have large dual sums `F(ψ)`. By the mean value theorem for `F⁴` (length `M⁴ = q^{8/9} ≤ q`), `#{ψ : |F(ψ)| ≥ M^{1−δ}} ≪ q^{1/9 + 16δ/9 + ε}` at the critical case. At `q ≈ 10⁴`, `M = 8`, and the condition involves only the primes `2, 3, 5, 7`, so small `q` favours these sets. *(Round 531: with the smooth weight of §11 no character meets the condition with `δ < 0.3` at `q ≤ 10⁶`, so these sets do not come from it. Their concentration falls between `q = 10⁴` and `10⁶`, then levels off near `0.31` up to `q ≈ 10⁷`. §11.)*
- **A major/minor split of the Gram matrix.** Let `E_maj` keep the off-diagonal entries `K(χχ̄′)` with `|F(χ̄χ′)| > M^{1−δ}`. Each row of `E_maj` then has at most `q^{1/9+16δ/9+ε}` entries, each at most `C√q` (Pólya–Vinogradov). Schur's test gives `‖E_maj‖ ≪ q^{1/9+16δ/9+1/2+ε}`, which is below `N = q^{7/9}` for `δ < 3/32`. So `s₁(M)² ≤ N + ‖E_maj‖ + ‖E_min‖`, and only the minor part `E_min` (entries with `|F| ≤ M^{1−δ}`) can carry the critical eigenvalue `≈ q`.
- **Open.** A third-moment bound for `E_min` that keeps the Jacobi phases. Used pointwise, the saving `M^{−δ}` with `δ < 3/32` gives `q^{7/2}M^{−3δ}`, far above `q³`. Chen–Gupta–Li's moment method needs the Poisson structure in `m`, which the filter by `|F|` breaks. The revised target is that bound, or a proof that sets of size `q^{2/3}` cannot keep their differences on major arcs once `π(M)` is large. *(Round 531: the second alternative adds nothing. For large `q` the major part is empty for `δ < 1/12`, by §6's half-plane bound, and Schur's test covers `1/12 ≤ δ < 3/32`. At the tested `q` it is empty for `δ < 0.3`. So the target is the third moment of `E` itself; §11 refines it to an energy form.)*

## 11. Round 531: a large-`q` probe of the Gram matrix, and a weaker conjecture

The owner asked to keep researching. `gram_probe.py` computes the Gram matrix of §10 with FFTs in exponent coordinates, at the critical case's proportions (`|W| = q^{2/3}`, `N = q^{7/9}`), with the smooth weight `sin²` on `[N, 2N]`. With one point per character at `t = 0`, `S₃` is `tr E³`, where `E` is the Gram matrix minus its diagonal. The gate runs `q = 10007`, `100003` and `1000003`. Scratch runs at `q = 3025261`, `10000223` and `10001881` are not in the gate. The sets come from alternating projections started at the bump, as in P5.

- **No major arcs** (G2). With the smooth weight no character has `|F| > M^{0.7}`. The smallest `δ` is `0.363`, `0.376` and `0.359`, and `0.355`, `0.334` and `0.344` in the scratch runs. So §10's major part (`δ < 3/32`) is empty at these `q`, and for large `q` it is empty for `δ < 1/12` by §6's half-plane bound. The split leaves the open step where §6 put it. The weight's shape and position matter. The same profile placed symmetrically about `0` gives smallest `δ` of `0.075`, `0.038` and `0.023`; P4's sharp cutoff gives `0.111`, `0.129` and `0.186`. The dual weights of a smooth weight on `[N, 2N]` carry the phase `e(3Nm/2q)`, while those of the symmetric weight are real.
- **The concentrated sets** (G1, G3). Their concentration is `0.625`, `0.449` and `0.330`, and `0.350`, `0.309` and `0.309` in the scratch runs. In this search it falls to about `1/3` by `q = 10⁶` and then levels off. The arithmetic of `q − 1` made no difference in the pairs run. The safe prime `10000223` and `10001881`, with `q − 1 = 2³3⁶5·7³`, give the same value, and so do `1000667` and `1008001` against `1000003`. Of the off-diagonal Rayleigh mass, `0.92` to `0.98` lies on differences with `|F| ≥ M^{1/4}`, and `0.29` to `0.58` on `|F| ≥ M^{1/2}`.
- **They carry critical energy** (G4). Their additive energy is `E(W) = (1.8 to 2.6)·|W|^{8/3}` at the gated `q` and at `3025261` and `10001881`, the `q` where it was measured. At the critical case Chen–Gupta–Li's energy term `qN|W|^{1/2}E(W)^{1/2}` is `q³` exactly when `E(W) = |W|^{8/3}`. Their `S₃` is `0.45q³`, `0.22q³` and `0.14q³` at the gated `q`, and `0.18q³` and `0.16q³` at `3025261` and `10001881`. The last three are means of 24 Rademacher probes. That is at most `0.31` of the energy term, so these sets do not test the first term `q²|W|^{3/2}`.
- **Sparse polynomials** (G6). The top singular vector `b` of each set has participation ratio `38`, `93` and `201`, against `q^{1/3} = 22`, `46` and `100`. Of the `q^{7/9}` points of `[N, 2N]` it is spread over about `2q^{1/3}`. A concentration `c` needs a support of at least `cq^{1/3}`, since `|supp b|·|W| ≥ cq`. As `1`-bounded polynomials these are far from large-values sets: no character has `|D| ≥ N^{0.6}·max|b_n|`.
- **Low energy** (G5). Confine `W` to a random pool of `2|W|` exponents, so that `E(W)` is near the random level `|W|⁴/q`. Then the search reaches only `c = 0.221`, `0.122` and `0.066` (`0.049` at `3025261`). `S₃` is `1.23`, `1.01` and `1.02` times its mean over random `W`. That mean is `(5/16)N|W|³` up to lower order, the lines through `(1, 1)` of §9.

**A weaker conjecture.** For prime `q` and `T = O(1)`, every `W` in the range of Chen–Gupta–Li's Proposition 11.1 satisfies

```
S₃ ≲ q^ε (N|W|³ + qN|W|^{1/2}E(W)^{1/2}).
```

Their Proposition 11.1 bounds `S₃` by `(qT)²|W|^{3/2}` plus three terms that carry `σ`, and their Remark 11.2 reads: "The terms that set the limitations on our bounds are the first two terms, (qT)²|W|^{3/2} and qT|W|N^{3−2σ}." In their sketch, (2.3) reads "s₁(M)⁶ ⪅ (qT)²|W|^{3/2} + qTN|W|^{1/2}E(W)^{1/2}", and inserting their bound for `E(W)` gives "|W| ⪅ (qT)^{1/2} + (qT)^{4/3}N^{−1}", their (2.4) (both from the PDF's text layer). The conjecture keeps the energy term, drops the first term, and adds the lines through `(1, 1)`.

- It is weaker than §9's conjecture by a factor `N/√q` per line. Round 530's counterexample meets it: §9's ratio divided by `N/√q` is `0.52`, `0.42` and `0.39` at `q = 10007`, `100003` and `400009`.
- The term `N|W|³` does not bind for `σ > 2/3`. So, as for §9's conjecture, their Proposition 3.1 loses `(qT)^{4/3}N^{2−4σ}`, and the payoff is §9's: `30/13` in the model (check (E)).
- In inverse form at the critical case, the conjecture says: if `S₃ ≥ q^{3−η}` with `η < 2/9`, then `E(W) ≥ |W|^{8/3}q^{−2η−ε}`. The concentrated sets above sit at that energy. The sets of random-level energy have `S₃` near `q^{3−2/9}`.

**What the probe cannot see.**

- At random-level energy the energy term is `q^{3−1/18}`, within a factor `q^{1/18} ≤ 2.45` of `q³` for `q ≤ 10⁷`.
- The socket's saving `κ ≤ 1/39` lowers `q^{−κ}` only to `0.66` there.
- So at these sizes the magnitude of `S₃` separates the first term from the energy term by at most that factor, and cannot show the saving. The findings are structural: which arcs, which energies, which supports. The conjecture is consistent with them and is not proved.
- Alternating projections find local maxima. The pool makes `W` random-like, so structured sets of low energy are untested.
