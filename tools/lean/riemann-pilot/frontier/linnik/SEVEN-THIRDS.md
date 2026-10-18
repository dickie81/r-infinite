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

  *(Round 569: §37 surveys two of these. Additive, planar and higher-order large sieves bear on this family only through base change (E7) or the two cubic characters mod `q`. The stack's own cubic-theta family gives no count at `β = 5/7`. Hecke L-functions over imaginary quadratic fields are the register's E7, Bourgain's estimates are in B14, and sum-product methods are B26. Jutila's and Forti–Viola's methods stay as B14 records them.)*

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

## 12. Round 532: concentration at bounded energy

The owner asked to keep researching. `energy_frontier.py` asks how much concentration and third moment a set of size `q^{2/3}` can carry when its additive energy is held near the minimum.

- **The minimum.** Every `W ⊂ Z/L` of size `R` has `E(W) ≥ R⁴/L`, by Cauchy–Schwarz over the sums `k₁ + k₂`. So Chen–Gupta–Li's energy term `qN|W|^{1/2}E(W)^{1/2}` is at least `qNR^{5/2}L^{−1/2}`. Their first term `q²|W|^{3/2}` exceeds that by the factor `q√L/(NR)`, which is `q^{1/18}` at the critical proportions up to `(L/q)^{1/2}`; numerically `1.67`, `1.90` and `2.15` at the three gated `q`. So for every `W` at the critical point, the weaker conjecture of §11 asks for a saving of at most `q^{1/18}` in `S₃` over their (2.3).
- **The dynamic.** Start from §11's concentrated set. At each step, score every character by `|Gv|²` minus a growing multiple of the energy it would add, and exchange at most 3% of `W`. For each energy level `κ = E(W)/(R⁴/L) ≥ 1`, keep the set with the largest concentration.
- **Results** (the gate, `q = 10007`, `100003` and `1000003`):
  - The dynamic reaches `κ = 1.10`, `1.08` and `1.05`.
  - The best concentration is `0.438`, `0.300` and `0.210` at `κ ≤ 1.25`, and `0.533`, `0.372` and `0.257` at `κ ≤ 2`. So low energy does not force small concentration at these `q`: §11's random pools reached only `0.221`, `0.122` and `0.066` at `κ ≈ 1.1`. At each fixed energy level, though, the concentration falls with `q`, by a factor of about `0.7` per decade. §11's unconstrained sets level off near `1/3` only as their energy grows, `E ≈ 2|W|^{8/3}`, that is `κ ≈ 2q^{1/9}`.
  - At `κ ≤ 1.25`, `S₃` is `0.095q³`, `0.048q³` and `0.024q³`, which is `3.0`, `2.3` and `1.8` times its mean over random `W`.
  - The ratio of `S₃` to the energy term is `0.143`, `0.082` and `0.047` at `κ ≤ 1.25`, and `0.236`, `0.129` and `0.066` at `κ ≤ 2`. It falls by a factor of `0.51` to `0.57` per decade. The weaker conjecture needs it to stay below `q^ε`.
- **Reading.** In this search a large third moment comes with energy near `|W|^{8/3}`. At bounded energy, both the concentration and the third moment fade with `q`. That is the inverse form of §11's conjecture, seen at three values of `q` for one search method; it is not a proof. §11's caveat stands: at these `q`, magnitudes cannot separate factors of `q^{1/18}`.

## 13. Round 533: what the concentrated sets are

The owner asked to keep researching. `structure_probe.py` looks inside §11's unconstrained concentrated sets at `q = 10007`, `100003` and `1000003`. Write `R(b) = Σ_{χ∈W} χ(b)` for `b ∈ F_q^*`, and call the height of `b` the least `max(|m|, |m′|)` with `b ≡ m/m′`.

- **They nearly annihilate a few small-height rationals** (S1, S5). The 24 values `b ≠ 1` with the largest `|R(b)|` have `|R(b)|` between `0.43|W|` and `0.89|W|`. They are real and positive, and their heights are at most `16`, `35` and `45`; a random `b` has height about `0.65√q`. At `q = 10⁶` the leading ones are `b = −5/9`, `−11/3`, `15`, `−13/15`, `33/5` and `−1/13`, and products of these recur further down the list. So the characters of `W` nearly satisfy `χ(β) = 1` for a small multiplicative set of rationals `β` of height up to about `2M`. A random `W` of the same size has `|R(b)| < 0.14|W|` for every `b ≠ 1`.
- **Most of them act through a wrap modulo q** (S2). At each `q`, at least 22 of the 24 are negative or lie outside `[1/2, 2]`. For such a `β = m/m′`, `βn ≡ n′` with `n, n′ ∈ [N, 2N]` needs `mn − m′n′ = kq` with `k ≠ 0`.
- **The polynomial lives on an approximate orbit** (S3, S4). Take the main support of the singular vector: its `37`, `92` and `200` heaviest points. Each of the 12 leading `β` maps at least `30%` of those points back into the support, while the median over random `b` is none of them. The interval `[N, 2N]` is not special in this way: a leading `β` maps it into itself no more often than a random `b` does.
- **The energy is these alignments.** Exactly, `κ = E(W)/(|W|⁴/L) = 1 + Σ_{b≠1}(|R(b)|/|W|)⁴`. So the law `κ ≈ 2q^{1/9}` of §11 says that the ℓ⁴ count of aligned values grows like `q^{1/9}`. The bounded-energy sets of §12 are those with few aligned values.

**Reading.** At these `q`, the configurations nearest the critical eigenvalue have three parts: a small group of rational dilations, a sparse subset of `[N, 2N]` that the group nearly preserves, and the group's near-annihilator as the character set. The inverse form would follow from showing that a large third moment forces such alignments. One step is elementary. Let `b` be supported on `s` points `n_i` with `Σ_W|D_b|² = cL‖b‖²` and `cL ≥ |W|`. The Gram matrix on the support has diagonal `|W|` and off-diagonal entries `R(n_j/n_i)`, so `(cL − |W|)² ≤ Σ_{i≠j}|R(n_i/n_j)|²`. Heavy concentration on few points thus forces large `|R|` on their ratios. Whether a large third moment forces alignment on small-height rationals in general is open.

## 14. Round 534: smooth numbers at a Farey point

The owner asked to keep researching. `farey_probe.py` identifies the configurations of §13 at `q = 10007`, `100003` and `1000003`.

- **A Farey point** (P1). Write the 24 leading `β` of §13 as `m/m′`. The differences `m − m′` have gcd `d = 5`, `9` and `14`, and `q/d` is the point `q/d′` nearest the centre `3N/2` of the weight. At `q = 10⁶`, §13's list reads `−5 ≡ 9`, `−11 ≡ 3`, `15 ≡ 1`, `−13 ≡ 15`, `33 ≡ 5` and `−1 ≡ 13 (mod 14)`.
- **Smooth numbers** (P2). Put `r = dn − q`. Then `n ≡ r/d (mod q)` and `r ≡ −q (mod d)`, and `|r| < q/2` on `[N, 2N]`. At least `90%` of the singular vector's mass lies on the `n` whose `r` is `y`-smooth, for `y = 11`, `17` and `29`, the least primes for which this holds. Those `n` are `6.7%`, `2.8%` and `1.0%` of the interval. On the main support every `b_n` has the same phase. At `q = 10007` the eight heaviest points have `r = −72, 168, −252, 48, −42, 288, 108, −112`, products of `2`, `3` and `7`.
- **A grading by the characters mod d** (P3). Label each `χ ∈ W` by the character `ψ` of `(Z/d)^*` that it most resembles on the integers up to `M`: the `ψ` maximising `|Σ_{h≤M} χ(h)ψ(h)|`. The labels split `W` into classes within `4%` of `|W|/φ(d)`. `χ(−1) = ψ(−1)` on all of `W`. The labels add on the additive quadruples `k₁ + k₂ = k₃ + k₄` of `W`, for shares of `1.000000`, `0.999955` and `0.999893`; at `q = 10007` a direct count in scratch found all `28,401,984` quadruples labelled additively. A random `W` labelled by the same rule gives `0.48`, `0.40` and `0.24`.
- **Primes the labels do not see** (P4). The labels use only `h ≤ M`. For the primes between `M` and `y`, the mean of `Re χ(p)ψ(p)` over `W` is `0.20` (`p = 11`); `0.39` and `0.25` (`p = 13`, `17`); and `0.35` and `0.23` (`p = 23`, `29`). For the random `W` it is within `0.03` of zero.
- **An explicit set** (P5). Let `b′` be `√w` times the indicator of the `n` with `y`-smooth `r` (`87`, `214` and `464` points), and `W′` the `|W|` characters where the transform of `b′` is largest. With no search, `W′` has `0.969`, `0.967` and `0.969` times the concentration of the search's set.

**Why.** One identity explains (P1)–(P4). If `dn = q + r`, then `χ(n) = χ̄(d)χ(r)` for every character `χ` mod `q`. So the transform of `b` is `Σ_n √w(n) b_n χ̄(n) = χ(d)Σ_r c_r χ̄(r)`, with `c_r` the weighted coefficient at `n = (q + r)/d`. Suppose `b` is supported on the `n` with `y`-smooth `r`, as (P2) finds for at least `90%` of the mass. Each such `r` is `±` a product of primes `p ≤ y` that do not divide `d`, since `r ≡ −q` is prime to `d`. So the modulus of the transform is `|g(θ(χ))|`, where `θ(χ) = (χ(−1); χ(p) : p ≤ y, p ∤ d)` is a point of a torus of dimension `k`, the number of those primes, and `g` is a trigonometric polynomial on that torus.

- A character `ψ` mod `d` gives the point `θ(ψ)`. Since `ψ(r) = ψ(−q)` for every `r` of the support, every term of `g` has the same phase at `θ(ψ)`. When the `c_r` share one phase, as (P2) finds, `|g(θ(ψ))| = Σ|c_r|`, the largest value `|g|` can take. Here the primes and `−1` generate `(Z/d)^*`, so the `φ(d)` points `θ(ψ)` are distinct, and they form a group `Θ_d`.
- The map `k ↦ θ(χ_k)` is a homomorphism on `Z/L`. Suppose every `θ(χ_k)` with `k ∈ W` lies within `U` of `Θ_d`, where `U − U + U − U` meets `Θ_d` only at `0`, and that each label names the point of `Θ_d` nearby. Then the labels add on every additive quadruple of `W`. That is (P3), and (P4) is the same alignment at primes the labels do not use.
- For `m` and `m′` products of those primes and `−1`, `R(m/m′) = Σ_W χ(m)χ̄(m′)`. If the classes are translates of one another in the torus, the sum over the classes carries the factor `Σ_ψ ψ̄(m)ψ(m′) = φ(d)·[m ≡ m′ (mod d)]`. So `R(m/m′)` is near zero unless `m ≡ m′ (mod d)`, which is (P1).

This ties §13's three parts together. The dilations are ratios `m/m′` of products of the basis primes with `m ≡ m′ (mod d)`. The approximate orbit is the smooth support, and the near-annihilator is the set of characters near `Θ_d`.

**Energy.** Put `W_U = {k : θ(χ_k) ∈ Θ_d + U}`. Since `θ` is a homomorphism and `Θ_d` a group, `W_U + W_U ⊂ W_{U+U}`. So by Cauchy–Schwarz every `W ⊂ W_U` has `E(W) ≥ |W|⁴/|W + W| ≥ |W|⁴/|W_{U+U}|`. If `|W_{U+U}| ≤ K|W|`, then `E(W) ≥ |W|³/K`, which is at least `|W|^{8/3}` once `K ≤ |W|^{1/3} = q^{2/9}`. For a box `U` in `k` coordinates one expects `K` near `2^k`, if the points `θ(χ_k)` are equidistributed at that scale; that is not checked. The sets found have `k = 4`, `6` and `8`, and `(E(W)/|W|³)^{1/k} = 0.730`, `0.728` and `0.735` (P6). So the energy falls by a nearly constant factor per prime of the torus, and that factor is above the box heuristic's `1/2`.

**Reading.** At these `q`, the configurations nearest the critical eigenvalue are explicit. The polynomial lives on the smooth numbers of the progression `r ≡ −q (mod d)`, carried into `[N, 2N]` by `r ↦ (q + r)/d`. Its character set behaves as a multiplicative Bohr set of rank `k` with a torsion part, the characters of `(Z/d)^*`.

- A concentration version of the inverse form would ask that `c ≥ q^{−η}` with `η < 2/9` force `E(W)` near `|W|^{8/3}` or above. For the sets found, `E(W)/|W|³ = c^γ` with `γ = 2.67`, `2.37` and `2.22` (P6).
- If `E(W)/|W|³ ≥ c³` held at large `q`, then `c = q^{−η}` with `η < 2/9` would give `E(W) ≥ |W|³q^{−3η} = |W|^{8/3}q^{−2η}·q^{2/9−η}`, above the inverse form's level. That is a heuristic for this family at three values of `q`, not a proof.
- The link from concentration to `S₃` is not settled here. The top eigenvalue alone does not carry `S₃`: §11 has `S₃ = 0.45q³`, `0.22q³` and `0.14q³`, against `(cL)³ ≈ 0.24q³`, `0.090q³` and `0.036q³`.
- Open: whether every set with a large third moment correlates with a multiplicative Bohr set of doubling at most `q^{2/9}`. That would be an inverse theorem of Bogolyubov type in the multiplicative group, and the energy bound above would turn it into an inverse form with losses `q^{O(η)}`. Also open: whether some set outside this family has a large third moment and low energy.
- §11's caveat stands: at these `q`, magnitudes cannot separate factors of `q^{1/18}`.

## 15. Round 535: at the critical point the large-values sets have minimal energy

The owner asked to attack the inverse theorem and to push toward a formalisation of an exponent below `7/3`. `low_energy_probe.py` records the measurements.

- **What Proposition 10.2 already gives** (L1). Chen–Gupta–Li's energy bound assumes "|D_N(t,χ)| ≥ N^σ/6 for all (t,χ) ∈ W and (qT)^{2/3}/2 ≤ N ≤ qT" and concludes "E(W) ⪅_ϵ |W|N^{4−4σ} + |W|^{21/8}(qT)^{1/4}N^{1−2σ} + |W|³N^{1−2σ}" (from the PDF's text layer, spaces and exponents restored). At `σ = 5/7`, `N = q^{7/9}`, `|W| = q^{2/3}` and `T = q^{o(1)}` the three terms are `q^{14/9}`, `q^{5/3}` and `q^{5/3}`. Every `W` of that size has `E(W) ≥ |W|⁴/L`, about `q^{5/3}` (§12). So at the critical point a large-values set has energy within `q^ε` of the least possible. The proposition's other hypothesis, "either |W| ≥ (qT)^{2/3} or that E(W)^{1/8}N ≥ (qT)^{1/2}|W|^{5/8}", holds there for large `q`: the second alternative needs `E(W) ≥ (qT)⁴|W|⁵N^{−8} = q^{10/9+o(1)}`, below that least energy.
- **What this says about rounds 533–534** (L2). The concentrated sets there have `κ = E(W)/(|W|⁴/L) = 6.13`, `6.93` and `8.48` at the three `q`, rising, and `E(W) ≈ 2|W|^{8/3}`, which exceeds `q^{5/3}` by about `q^{1/9}`. So for large `q` Proposition 10.2 itself rules them out as large-values sets at the critical point; at `q ≤ 10⁷` the factor `q^{1/9} ≤ 6` is within the constants. Their structure, smooth numbers and Bohr sets, describes the extreme Gram matrices of arbitrary sets, not the large-values problem.
- **The sharpened target.** At `E(W) = q^{5/3}` the energy term `qN|W|^{1/2}E(W)^{1/2}` is `q^{3−1/18}`, while the first term `(qT)²|W|^{3/2}` is `q³`. So going below `7/3` this way needs only: `S₃ ≤ q^{3−δ}` for the sets of size `q^{2/3}` with `E(W) ≤ q^ε|W|⁴/q`. In inverse form: `S₃ ≥ q^{3−δ}` forces `E(W) ≥ q^{δ′}|W|⁴/q`, energy above the minimum by a power. Round 531's form asked for energy near `|W|^{8/3}`. At the critical point, `S₃ ≤ q^{3−δ}` gives `|W| ≤ q^{2/3−δ/3}` through `s₁⁶ ≥ (|W|V²/N)³`, which is §5's socket at `κ = δ/3` there.
- **The small lines, exactly** (L3). Set `R(1)` to `0`, which leaves out the points where an argument is `1`, and take the box of lines `|m₁|, |m₃| ≤ M`, `1 ≤ m₂ ≤ M` with equal weights, a model of the dual weights. Write the sum of the line sums over the box as `Σ_x R(x)X(x)`, with `X(x) = Σ_m R(B_m(x)/x)R̄(B_m(x))` and `B_m(x) = (m₁x + m₃)/m₂`. Cauchy–Schwarz then bounds it by `θ^{1/2}` times the first term's level `|box|·q|W|^{3/2}`, where `θ = ‖X‖²/(|box|²q|W|²)` is the coherence of the `m`-sums (`1` at full coherence). Measured over the whole box, at `q = 10007` and `100003`:
  - Cauchy–Schwarz loses at most a factor `2`: the ratio of the sum to the bound is `0.60` to `0.80` for every set.
  - `θ` is `0.46` and `0.15` for the concentrated sets, `0.026` and `0.0081` for the sets of `energy_frontier.py` with `κ ≤ 1.25`, and `0.0025` and `0.0007` for random sets, about `4/|box|`~~, the diagonal's level~~. *(Round 563: retracted, false when written. Most of that level is not the diagonal. The terms `χ = χ′` of `R(B/x)R̄(B)` sum to `R̄(x)` on every line, so every pair of lines correlates by about `q|W|`, adding about `1/|W|` (`3.4/|box|` at `q = 10007`). Centred, the random sets sit at `1.2/|box|` and `1.5/|box|` at `q = 10007` and `100003`; §31.)*
  - For the low-energy sets `θ` falls by a factor `3.2` between the two `q`.
- **Four-point correlations.** `‖X‖²` is the sum over pairs of lines of `C(m, m′) = Σ_x R(B_m/x)R̄(B_m)R̄(B_{m′}/x)R(B_{m′})`. In scratch runs over 200 random pairs, the median `|C|` of a generic pair is of the random size `√q|W|²` for every set. So `θ` is carried by a heavy tail of pairs, which a random sample can miss: at `q = 10⁶` a 200-pair sample caught none of it.
- **Reading.** For prime `q` the open step is now this: when `E(W)` is within `q^ε` of the minimum, the `m`-sums over the small lines are incoherent, `θ ≤ q^{−2δ}`. Then the generic part of `S₃` is at most `q^{−δ}` times the first term. In the sets found, `θ` falls about like `q^{−1/2}` for the low-energy sets (two values of `q`). That is not a proof, and the weights of the true `S₃` are the dual weights over all lines, not the box's.
- **Toward a formalisation.** A Lean statement below `7/3` along this route has three layers.
  1. The socket exists: `Linnik.CharDensity (7/3 − κ + ε)`, fed to `Linnik.linnik_of_charDensity` (round 520).
  2. Chen–Gupta–Li's Proposition 3.1 (their §§4–11), with Heath-Brown's Theorem 10.1 on double zeta sums as a displayed hypothesis at first. ~~Its parts are the Guth–Maynard moment inequality, the line-sum identity for prime `q`, Propositions 7.1–7.2 and 8.1, Lemma 9.1, Proposition 10.2 and Proposition 11.1.~~ *(Round 537: retracted, false when written; the list is incomplete. Among their results it leaves out Lemma 4.1 (large values to the largest singular value), Lemmas 4.3–4.5 and Proposition 4.6 (the trace expansions), Proposition 5.1 (the bound for `S₁`) and Proposition 6.1 (the bound for `S₂`, with the approximate functional equation of their Lemma 6.2), among others. The line-sum identity is §6's exact evaluation of their sums `I_m` (their Lemma 4.5) at prime `q` with one point per character; it is not one of their results.)* This layer gives `7/3 + ε`, the record, and is not started. *(Round 537: started; their Lemma 4.2 is in Lean.)* *(Round 538: their Lemma 4.5 at `t = 0` for prime `q`, folded modulo `q`, is in Lean as the line-sum identity, and with Lemma 4.2 it bounds a large-values set through the line sums `L(k)` of §6: `LinnikLines.large_values_lines`.)* *(Round 539: their §5 split too. In the folded form the zero frequency is `(q − 1)²|W|`, the lines with exactly one nonzero coordinate carry nothing and those with exactly two collapse to `(q − 1)|R(c)|²`, so a large-values set obeys `(|W|V² − N_cβ)³ ≤ β³·Re q⁻²(S₂ + S₃)`: `LinnikSplit.large_values_split`.)* *(Round 540: `q⁻²S₂ = 3N_c(1 − 1/q)(‖E‖_F² + |W|N_c²/q)` by Parseval, so the open step at one point per character is a displayed hypothesis on the generic line sums: `LinnikS2.large_values_socket` gives `(|W|V² − N_cβ)³ ≤ β³(3N_c(A + |W|N_c²/q) + B)` from `‖E‖_F² ≤ A` and `Re q⁻²S₃ ≤ B`.)*
  3. The new step as a displayed hypothesis, the low-energy third-moment bound, which gives the socket at the critical point.

  Round 536 starts layer 2 with the moment inequality. ~~*(Round 536: done. `LinnikMoment.moment_three` and `LinnikMoment.moment_three_chars` in `external/pnt/LinnikMoment.lean`, kernel-checked with the standard axioms; `(Σ_{χ∈W}|D(χ)|²)³ ≤ ‖b‖⁶ Re tr(G³)` for the Gram matrix `G` of `W`. README round 536.)*~~ *(Round 537: retracted, false when written. Round 536 proved Chen–Gupta–Li's "simple bound" at `r = 3`, which they set aside as "quite lossy"; at the critical point it gives at best `|W| ≲ q^{2/3}`, because `tr(G³)` contains the all-equal triples `|W|N_c³`. The moment inequality of layer 2 is their Lemma 4.2, which they cite as Guth–Maynard's. It is `LinnikMoment.refined_moment_chars`, kernel-checked with the standard axioms: `(Σ_{χ∈W}|D(χ)|² − N_cβ)³ ≤ β³ Re Σ G(χ₁,χ₂)G(χ₂,χ₃)G(χ₃,χ₁)` over the triples of `W` that are not all equal, with `N_c` the diagonal of `G` and `β = ‖b‖²`. README round 537.)*

## 16. Round 541: the critical block, and a second socket through the sixth moment

The owner asked to keep attacking the step below `7/3`. `sixth_moment.py` is new.

- **Where the critical case sits in Chen–Gupta–Li's own argument.** Their §12 was read directly from the PDF's text layer (spaces and exponents restored below).
  - The class-II zeros: "where we have set X = (qT)^ϵ", and "upon choosing Y = (qT)^{1/2}, we obtain |R̃₂| ⪅ (qT)^{2(1−σ)}".
  - The class-I zeros: "Thus it suffices to bound |W| in the range (qT)^ϵ ≤ N ⪅ (qT)^{1/2}".
  - Each block is raised to a power: "we can choose k ≪_ϵ 1 so that (qT)^a ≤ N^k ≤ (qT)^{3a/2}".

  So the polynomial of length `q^{7/9}` at their critical point is a power of a block of length at most `q^{1/2}`. In the mean-value count it is the square of a block of length `q^{7/18}`.
- **The critical block** (check (K)). For the mean value theorem at Ingham's level `3(1 − σ)/(2 − σ)`, the window of lengths is exactly `[1/(2 − σ), 3/(2(2 − σ))]`, of ratio `3/2`. Let `ν_c(σ) = 1/(2(2 − σ))`. Its square is at the left end of the window and its cube at the right end, so no power of `ν_c` lies strictly inside. Every other `ν` in `(0, 1/2]` has a power strictly inside. If `kν` is the left end with `k ≥ 3`, then `(k + 1)ν` is at most `4/3` times the left end, so it is inside. Otherwise take `k = ⌈(left end)/ν⌉`. For `ν < ν_c` that gives `k ≥ 3`, and `kν` is inside because the ratio is `3/2`. For `ν > ν_c` it gives `k = 2`, and `2ν ≤ 1 <` (right end). The check verifies this exactly at `ν_c` and at 399 other exponents, for 41 values of `σ` in `[7/10, 4/5]` and at `5/7`. At `σ = 5/7`, `ν_c = 7/18`, the point of §4's set `B` in `(0, 1/2]`. So, for the mean value theorem with powers, Ingham's `3/(2 − σ)` is set by the blocks of length near `Q^{ν_c(σ)}`, and §4's barrier at `5/7` is about the block of length `Q^{7/18}`.
- **What these blocks are.** With the mollifier of length `(qT)^ε`, a block is, up to partial summation, `Σ_{N<n≤2N} c_nχ(n)n^{−it}` with `c_n = Σ_{d|n, d≤X} μ(d)` and `X = (qT)^ε`. That is a short combination of the sums `Σ_m χ(m)m^{−it}` over `m` of length `N/d`. §4's family treats the block as a general polynomial. An estimate that uses this structure lies outside the family, and §4's barrier says nothing about it.
- **The sixth-moment socket** (check (X)). The hypothesis `SIX(δ)`: for these blocks with `Q^{1/3} ≤ N ≤ Q^{1/2}`,

  ```
  Σ_{χ≠χ₀} ∫_{−2T}^{2T} |D_N(t, χ)|⁶ dt  ≤  Q^{o(1)} (Q N³ + Q^{−δ} N⁶).
  ```

  `SIX(0)` is the mean value theorem for `D_N³`, a polynomial of length about `N³ > Q` with divisor-bounded coefficients. Its term `N⁶` is the size of the principal character's contribution, which the divisor bound cannot separate from the rest. The model adds `SIX(δ)` for detectors whose mollifier exponent is `x = 0`, as Chen–Gupta–Li's is. Maximised over the grid of `seven_thirds.py` (with `5/7` and `7/10` added), the exponent it certifies is:
  - `δ = 0`: `7/3`, at `σ = 5/7`, with nothing below `7/3 − 10⁻⁴` there;
  - `δ = 1/100`, `1/50`, `1/20`: `2.3185`, `2.3013` and `2.2619`;
  - `δ = 1/12` and `1/6`: `2.2223`, within the bisection's tolerance `10⁻⁴` of `20/9`.

  The floor is at `σ = 7/10`. There the model certifies `20/9` with `δ = 1/6`, and nothing below `20/9 − 10⁻⁴` even with `δ = 1/2`. At that point the window is `[5/6, 10/9]`, of ratio `4/3`, and the block `5/18` has its cube at the left end and its fourth power at the right end: it is the next doubly-critical block. Its eighth moment wraps, since `(Q^{5/18})⁴ = Q^{10/9} > Q`.
- **What `SIX(δ)` asks.** For a smooth sum `S` of length `N` at `t = 0`, `Σ_{χ≠χ₀}|S|⁶ = (q − 1)(D₃ + O) − W⁶`. Here:
  - `D₃` counts the integer solutions of `x₁x₂x₃ = y₁y₂y₃`; it is the sixth moment of a Steinhaus random multiplicative function;
  - `O` counts the solutions of `x₁x₂x₃ ≡ y₁y₂y₃ (mod q)` that are not integer solutions;
  - `W = S(χ₀)`.

  At `N = q^{7/18}` the products reach `N³ = q^{7/6}`, so `O` comes from `x₁x₂x₃ − y₁y₂y₃ = ℓq` with `0 < |ℓ| ≪ q^{1/6}`. The divisor bound gives `(q − 1)O ≤ q^εW⁶`, which is `SIX(0)`. For `δ > 0`, `SIX(δ)` asks `(q − 1)O − W⁶ ≤ q^{o(1)}(q^{−δ}W⁶ + qN³)`: the off-diagonal count must match the principal character to within a power. Equivalently, the products of three short intervals are equidistributed in `L²` among the residue classes mod `q`, with a power saving. That is a ternary additive-divisor problem whose shifts lie in the progression `0 (mod q)`. This round's two web searches found no such saving. The searches are not exhaustive.
- **The probe** (check (M)). Take `φ = sin²(π(x − 1))` on `[1, 2]` and `N = round(q^{7/18})`. The gate checks Parseval, the fourth moment against `D₂` (no wrap, `4N² < q`), and the sixth moment from the FFT against a direct count over the residue classes. It records `ρ = Σ_{χ≠χ₀}|S|⁶/((q − 1)D₃)`:
  - `0.884`, `0.899` and `0.905` at the gated `q = 10007`, `100003` and `1000003`;
  - `0.898`, `0.901`, `0.908` and `0.911` at `q = 30011`, `300007`, `3000017` and `10000019`, in a run with `--extra`.

  The scale `W⁶/((q − 1)D₃)` is `0.208`, `0.235` and `0.266` at the gated `q`, and `0.305` at `q = 10000019`. It grows by a factor of about `1.15` per decade of `q`. So at these `q` the principal-size term is about a quarter of the diagonal. The probe cannot see `SIX(δ)`; it checks the pipeline and finds the sixth moment within `12%` of the random model.
- **Reading.** For prime `q` there are now two routes below `7/3`. Both go through the blocks of length near `q^{7/18}`; for `σ` near `5/7`, near `q^{ν_c(σ)}`.
  - (a) `S₃` for the square of the block, as a general polynomial of length `q^{7/9}` (§§6–15).
  - (b) `SIX(δ)`, the sixth moment of the block itself, past the `q`-threshold by up to `q^{1/6}`.

  In the model, route (b) lowers the exponent to `20/9` at best. To go further the model needs the eighth moment of the blocks of length `q^{5/18}` at `σ = 7/10`. Neither input is proved.

## 17. Round 542: the sixth-moment socket on the stack's own families

`sixth_moment.py` gains check (Y). It drops Chen–Gupta–Li's Proposition 3.1 from §16's model. What remains is the mean value theorem and Huxley's estimate, the two large-values families the stack has in Lean (rounds 524–527), with detectors whose mollifier exponent is `0` and with `SIX(δ)`.

- **The exponent at `σ = 3/4`** (Y1). It is `12/5 − 8δ/5` for `δ = 0`, `1/40`, `1/24` and `1/20`, to the bisection's tolerance `10⁻⁵`. That is `12/5` at `δ = 0`, the stack's landed exponent (round 527), and `7/3` at `δ = 1/24`.
- **Over the grid** (Y2), with `3/4` added: `δ = 1/24 − 1/1000` gives a maximum of `2.3349`, above `7/3`, and `δ = 1/24 + 1/1000` gives `2.3317`, below it. Both maxima are at `σ = 3/4`, where the mean value theorem and Huxley's estimate have the same window.
- **The floor** (Y3). At `σ = 3/4` the model certifies `16/7` with `δ = 1/14`, and nothing below `16/7 − 10⁻⁴` even with `δ = 1/2`. There the window is `[6/7, 8/7]`, of ratio `4/3`. The block `2/7` has its cube at the left end and its fourth power at the right end, so its eighth moment wraps, as the block `5/18` does at §16's floor `20/9`.
- **What this means.** In the model, `SIX(δ)` with `δ > 1/24` gives an exponent below `7/3` without any part of Chen–Gupta–Li's Proposition 3.1. With the proposition, any `δ > 0` does (§16).
- **A conditional Lean route, not started.** It would reuse the stack's detection identity and dyadic blocks (`LinnikDetect`), its power trick and block bins (`LinnikPower`, `LinnikTwelveBins`), Huxley's estimate (round 526) and the fourth moment for the integral class (round 524). It would add one class-I estimate, from `SIX(δ)` as a displayed hypothesis for the blocks with `Q^{1/3} ≤ N ≤ Q^{1/2}`, and the detector with a mollifier of length `Q^{o(1)}`. Its conclusion would be `Linnik.CharDensity (7/3 − κ + ε)` for some `κ > 0`, fed to `Linnik.linnik_of_charDensity`.

## 18. Round 543: moment hypotheses on the stack's families, and one attack note closed

`sixth_moment.py` gains check (Z).

- **The model of a moment hypothesis.** Suppose the `2k`-th moment of `L(½ + it, χ)` over the characters mod `q`, at one point per character, is at most `Q^{1+o(1)}`. That is the form in which the stack has the fourth moment (round 524, `LinnikFourth.fourth_moment`). In the model it does two things:
  - it counts the integral class, at mollifier exponent `0` and smoothing `Q^y` with `y = (1 − t)/(2k(σ − ½))`;
  - it counts every block of length at least `Q^y`. Through the Mellin integral of the block, a block of length `N` that detects a zero forces `|L(½ + it, χ)| ≥ N^{σ−½}Q^{−o(1)}` at a nearby `t`.

  The other blocks go by powers into the windows of the mean value theorem and Huxley's estimate.
- **The result** (Z1, Z2). For `k = 2`, `3` and `4` the model certifies `2 + 2/(2k + 1)` at `σ = 3/4`, and nothing below it by `10⁻⁴`. Over the grid, with `3/4` added, the maximum is that number, at `σ = 3/4`.
  - `k = 2` gives `12/5`, the stack's exponent from the fourth moment it has (round 527).
  - `k = 3` gives `16/7`, below `7/3`.
  - `k = 4` gives `20/9`.

  In the certificates for these values, every block is shorter than the integral class's `Q^y`. So the higher moment acts only through the integral class: it allows a shorter smoothing, and the blocks then fit the windows.
- **What this says.** In the model, a sixth moment of Dirichlet `L`-functions at one point per character, at Lindelöf strength, gives `16/7` with the stack's own large-values families. It needs no part of Chen–Gupta–Li. The sixth moment of `L(½ + it, χ)` over a single prime modulus at that strength is not known: this round knows of no such result, and its searches found none. It is a cleaner hypothesis than §16's `SIX(δ)`. It implies `SIX(δ)` for every block, through the same Mellin step.
- **A conditional Lean route, not started.** Take round 527's argument (Huxley's power trick, the detector of `LinnikDetect`), with the integral class counted by the sixth moment in place of the fourth, and a mollifier of length `Q^{o(1)}`. A conclusion `Linnik.CharDensity (16/7 + ε)` would follow under the displayed hypothesis, which would sit beside the proved fourth moment.
- **Attack note (i) of §6 is out of range.** Stevens–de Zeeuw's abstract (arXiv:1609.06284v4) states that "m points and n lines in F², with m^{7/8} < n < m^{8/7}, determine at most O(m^{11/15}n^{11/15}) incidences". The line sums of §6 pair about `q²` points, or level sets of comparable size, with `q^{2/3}` lines, so `n ≈ m^{1/3}`, outside that range. The line sums also need cancellation of complex weights, which incidence counts do not see.

## 19. Round 544: a sixth moment with a loss, and the threshold `1/6`

`sixth_moment.py` gains check (U). §18 assumed the sixth moment at Lindelöf strength. Here it may lose a power. Suppose that, at one point per character,

```
Σ_χ |L(½ + it_χ, χ)|⁶  ≤  Q^{1+θ+o(1)},
```

and keep the fourth moment the stack proves (round 524). In the model, the integral class and every block of length at least `Q^y` go through the critical line, with `y = min(ν₄, ν₆)`, `ν₄ = (1 − t)/(4h)`, `ν₆ = (1 + θ − t)/(6h)` and `h = σ − ½`. The other blocks go by powers into the windows of the mean value theorem and Huxley's estimate, as in §18.

- **The closed form** (U2). At each of eleven values of `θ` from `0` to `1/3`, the maximum over the grid, with `3/4` and the point `σ₀(θ)` below added, is

  ```
  max(16/7, min(2 + 2θ, 12/5)),
  ```

  within `2·10⁻⁵`. It is below `7/3` exactly at the values of `θ` below `1/6`.
  - `θ = 0`, `1/12` and `1/7` give the floor `16/7` of §§17–18.
  - For `1/7 < θ < 1/5` the value is `2 + 2θ`: `θ = 1/6 − 1/100` gives `2.31334`, and `θ = 1/6` gives `7/3`, at `σ = 5/7`.
  - `θ = 1/5`, `1/4` and `1/3` give `12/5`, the exponent without the sixth moment (round 527).
- **Why `2 + 2θ`** (U1). Let `[lo, hi]` be the mean value theorem's window, with `hi = t/(2(1 − σ))`. Below Ingham's level, `hi/3 < lo/2`, and a block with exponent in `(hi/3, lo/2)` has no power in the window: its square falls short of `lo`, and its cube passes `hi`. So, in the model, the moment's reach `y` has to stop at `hi/3`, unless Huxley's window covers the gap. Exact algebra gives the conditions, each checked on a rational grid of `σ`, `θ` and `A`:
  - the reach `(1 + θ − t)/(2kh)` of a `2k`-th moment with loss `θ` is at most `hi/3` if and only if `A(3 − k/2 + (k − 3)σ) ≥ 3(1 + θ)`, for `k = 2`, `3` and `4`;
  - so `ν₆ ≤ hi/3` if and only if `A ≥ 2 + 2θ`, for every `σ`, and `ν₄ ≤ hi/3` if and only if `A ≥ 3/(2 − σ)`, Ingham's exponent;
  - for `σ > 2/3`, Huxley's window, halved, reaches `hi/3` if and only if `A ≥ 3/(3σ − 1)`, Huxley's exponent.

  The sixth moment is the one, among `k = 2`, `3` and `4`, whose condition does not depend on `σ`. It caps the Ingham–Huxley envelope `min(3/(2 − σ), 3/(3σ − 1))`, whose maximum is `12/5` at `σ = 3/4`, at the constant `2 + 2θ`. The cap binds on `[σ₀(θ), σ_H(θ)]`, with `σ₀(θ) = (1 + 4θ)/(2 + 2θ)`, where Ingham's exponent equals `2 + 2θ`, and `σ_H(θ) = (5 + 2θ)/(6 + 6θ)`, where Huxley's does (U3). The check certifies `2 + 2θ` at both ends and nothing below it by `10⁻⁴`, and it certifies `2 + 2θ − 10⁻⁴` at `σ₀ − 1/100` and at `σ_H + 1/100`. `σ₀(1/6) = 5/7` and `σ_H(1/6) = 16/21`.
- **The critical event.** At `σ = 5/7` and `A = 7/3`, `t = 2/3` and `ν₄ = 7/18`, the critical block of §16. There the integral class detects `|L(½ + it, χ)| ≥ Q^{1/12}`, since `(7/18)(5/7 − ½) = 1/12`. The fourth moment counts these characters by `Q^{1−4/12} = Q^{2/3}`, which is exactly `Q^t`. The sixth moment counts them by `Q^{1/2+θ}`, which is smaller exactly when `θ < 1/6`. There `ν₆ − ν₄ = 7(θ − 1/6)/9`.
- **What is known.** The best single-modulus value of `θ` this round knows is `1/3`. It is the Weyl bound `L(½, χ) ≪ q^{1/6+ε}`, squared, times the fourth moment. The Weyl bound for Dirichlet `L`-functions of cube-free conductor, which includes the primes, is Petrow–Young (Ann. of Math. 192 (2020); arXiv:1811.02452). Their arXiv:1908.10346 removes the cube-free condition. This round takes the bound at the heights the model uses as given; it did not check the paper's dependence on `t`. The sixth-moment results its searches found average over the moduli (Huxley 1970, as cited in arXiv:2409.01457; arXiv:2409.01457 itself). In the model, `θ = 1/3` gives `12/5`, nothing beyond round 527, and an exponent below `7/3` by this route needs `θ < 1/6`, a saving of more than `q^{1/6}` on that bound.
- **Reading.** In this model, the sixth-moment route to an exponent below `7/3` comes down to one count at the critical point: the characters with `|L(½ + it, χ)| ≥ q^{1/12}`, with a power saving over the fourth moment's `q^{2/3}`. At this height the Weyl bound gives nothing, since `q^{1/12} < q^{1/6}`. The sixth moment it gives, `θ = 1/3`, counts these characters by `q^{5/6}`. The truth is expected to be far smaller: for random-model reasons `log|L(½, χ)|` has variance about `½ log log q`. That heuristic is not an estimate. At accessible `q` the logarithms dominate the powers. The leading term of the fourth moment for prime `q` is `(q/(2π²))(log q)⁴` (Heath-Brown, 1981). At `q = 10⁶`, divided by `q^{1/3}`, it is about `1.8·10⁷`, more than `q`. So at that size the fourth moment's count is trivial, and numerics there do not test the exponent of this count.

## 20. Round 545: large central values at height `q^{1/12}`, and the conditional ladder

`sixth_moment.py` gains check (V).

- **The band hypothesis.** At one point per character, the fourth moment bounds by `Q^{1−4a}` the number of characters with `|L(½ + it, χ)| ≥ Q^a`. Suppose that count is `Q^{1−4a−δ}` for `a` in a band `[a_lo, a_hi]` only, and `Q^{1−4a}` elsewhere. As in §19, the integral class and every block whose height `a = νh` has count at most `Q^t` go through the critical line; the other blocks go by powers.
- **With Proposition 3.1** (V1). Take all four families and the band `1/12 ∓ 1/100`. The maximum over the grid is `7/3` at `σ = 5/7` for `δ = 0`. It is `2.33198`, `2.32317` and `2.31326` for `δ = 1/1000`, `1/100` and `1/50`. So in this model any power saving in the count of central values of size about `q^{1/12}` gives an exponent below `7/3`. In the model the band has to reach a little below `1/12`. At `σ = 5/7` and `A = 7/3 − κ`, the top `hi/3` of the gap sits at height `t/8 = 1/12 − κ/28`. A band centred at `1/10` (one of the check's mutations) leaves the maximum at `7/3`, within the bisection's tolerance, for each of these `δ`.
- **With the stack's families only** (V2). Here the maximum sits just above `σ = 3/4`, where the critical height is near `1/10`: at `σ = 3/4` and `A = 12/5`, `ν₄ = 2/5` and the height is `1/10`. Take the band `[1/24, 1/8]`. `δ = 34/1000` leaves the maximum at `2.33396` and `δ = 35/1000` brings it to `2.33155`, both at `σ = 91/120`.
- **The ladder.** Each input below gives an exponent below `7/3` for prime moduli, in the model or, where stated, kernel-checked. None is known at the strength it needs. The list is what this strand has found; it is not shown to be exhaustive.
  - A uniform bound `|L(½ + it, χ)| ≪ (q(|t| + 2))^c` with `c < 1/12`. This one is kernel-checked: `LinnikDensity.linnik_of_critBound` gives Linnik's exponent `2 + 4c + η` from it, through round 521's `charDensity_of_LBound`. Known: `c = 1/6` for prime `q` (Petrow–Young, §19), which is not in the stack; the stack proves `c = 5/24 + ε` (round 522). Such a bound makes the count above `q^{1/12}` vanish.
  - The sixth moment with loss `θ < 1/6` (§19, model). Known: `θ = 1/3`. It gives the band hypothesis with saving `2a − θ` at height `a`, so `1/6 − θ` at `a = 1/12`.
  - Any power saving in the count of `|L(½ + it, χ)| ≥ q^{1/12}`, with Proposition 3.1 (this section, model). Known: the fourth moment's `q^{2/3}`.
  - `SIX(δ)` for the critical blocks: any `δ > 0` with Proposition 3.1, `δ > 1/24` without (§§16–17, model). Known: `δ = 0`.
  - The first term of `S₃` at `q^{3−κ}` (§5, model). Known: `κ = 0`.
- **Horizon scan, 2026-10-18** (arXiv listings and abstracts):
  - arXiv:2609.27715 (Cossaboom) extends Guth–Maynard to `GL₂` automorphic `L`-functions: "We show that $N_π(σ, T) \ll T^{\frac{5}{2}(1 - σ) + o(1)}$".
  - arXiv:2609.17875 (Dubon) proves concentration of the vertical zero density of finite Dirichlet sums. Its applications are to partial sums of `ζ`, fixed Dirichlet `L`-functions and Hecke eigenforms of fixed level.
  - arXiv:2607.04632 (Turnage-Butterbaugh) is an expository account. Its abstract says the Guth–Maynard theorem, "for a key location in the critical strip, strengthens previous work of Ingham and is the first such improvement in over 80 years".

  None of the three treats the characters mod a prime `q` at `σ = 5/7`. None fills a socket of the register entry or contradicts its barrier statements. At `σ = 5/7` the prime-modulus exponent `7/3` is Ingham's `3/(2 − σ)`, §2's triple point.

## 21. Round 550: the common target H*

Check (W) of `sixth_moment.py` is new. Check (X) of §16 uses `SIX(δ)` only through its large-values consequence: the blocks `Q^ν` with `max(1 + 3ν(1 − 2σ), 6ν(1 − σ) − δ) ≤ t` are counted. (W) keeps that consequence only for the blocks within `w` of `ν_c(σ) = 1/(2(2 − σ))`. Call the restricted hypothesis H\*(δ, w).

- **It suffices** (W1, W2). With all four families and `δ = 1/100`, `w = 1/1000` gives a maximum of `2.33010` over (X)'s grid, at `σ = 43/60`, below `7/3`. At `σ = 5/7`, `w = 1/100` certifies `2.31583`, the same as the unrestricted socket, and `w = 1/1000` certifies `2.32733`.
- **Every route on the register gives it, near `σ = 5/7`** (W3 for the identities).
  - `SIX(δ)` by Chebyshev.
  - The band hypothesis of §20. At `ν = ν_c(σ)` a large block forces `|L(½ + it, χ)M_X| ≥ Q^{a}` with `a = ν_c(σ)(σ − ½)`, which is `1/12` at `5/7`. The band's count `1 − 4a` equals the socket's `6ν_c(σ)(1 − σ)` for every `σ`.
  - The sixth moment with loss `θ < 1/6` (§19) and the uniform bound `c < 1/12`, through the band.
  - The `S₃` step, through the squares of these blocks. A square sits at the window's left end `1/(2 − σ)`, where a saving in Chen–Gupta–Li's third term acts (§5's socket).
- **What it does not need.** No piece longer than `Q^{ν_c+w}`. The band gives H\*, but H\* does not give the band. The band's hard range of approximate-functional-equation pieces up to `q^{1/2}` (the register's C9) is not on H\*'s path.
- **Its simplest instance.** The number of `χ mod q` with `|Σ_{n∼N} χ(n)| ≥ N^{5/7}` at `N = q^{7/18}` is below `q^{2/3−δ}`. The fourth moment gives `q^{2/3}` up to logarithms, and so does the cube's mean value, since `N³ = q^{7/6} > q`. In the multiplicative group, this is the large spectrum of an interval of length `q^{7/18}` at level `N^{−2/7}`.
- **What numerics can show.** At `N = q^{7/18}` the threshold `N^{5/7}` is `q^{1/12}·√N`. The root mean square of `S` is about `(3N/8)^{1/2}` for this weight. So the threshold is more than five standard deviations out at `q = 10⁶`, and the expected count is below `1` at every computable `q`. A probe there cannot test the exponent.

## 22. Round 554: the restricted large sieve, two routes closed, and where the critical eigenvalue sits

The owner chose "New mathematics": the three-way sign cancellation in `S₃` for sets of minimal energy (core 1). `anatomy_probe.py` records the measurements. The register's B16, B17 and G6 record the closures and the survey, and `idea_register.py` (R19) checks the exponents.

- **The restricted large sieve.** For a set `W` of characters, let `Δ(W)` be the top eigenvalue of its Gram matrix on `[N, 2N]`. That is the least constant with `Σ_{χ∈W}|Σ_n √w(n)a_nχ(n)|² ≤ Δ(W)‖a‖²`. A large-values set then has `|W|V² ≤ Δ(W)N` up to the weight.
  - At the critical point (`|W| = q^{2/3}`, `N = q^{7/9}`, `V = N^{5/7}`), the large sieve's `Δ ≤ N + q` gives exactly `|W| ≤ q^{2/3}`.
  - Chen–Gupta–Li's first term, read through their refined moment inequality `(|W|V² − N_cβ)³ ≤ β³ Re S₃` (round 537), bounds `|W|V²/β − N_c` by `q^{2/3}|W|^{1/2}`. That is `q` again at `|W| = q^{2/3}`.
  - So a bound `Δ(W) ≤ q^{1−δ}` for the large-values sets of size `q^{2/3}` gives the count below `q^{2/3−δ}`. This is §10's concentration question (the register's B10).
- **In compressed-sensing terms** (B10's marker, [R19a]). Take the unit columns `u_χ = √w χ/(Σw)^{1/2}`. Then `Δ(W)/Σw = ‖Φ_W‖²`, and the target is an upper restricted-isometry bound `M^{1−δ}` at order `q^{2/3}`, where the trivial bound is `M = q^{2/9}`. The coherence is about `√q/N` (Pólya–Vinogradov), so Gershgorin gives `q^{7/18}`, above the trivial bound. The order `q^{2/3}` lies far beyond the square-root bottleneck `N/√q = q^{5/18}`. The explicit construction that G6's survey records, Bourgain et al.'s Theorem 1, has constant `n^{−ε₀}` at order `n^{1/2+ε₀}`, just past the bottleneck. This target asks for a constant far above `1`, at an order far past it.
- **The flat route, closed in its direct form** (B16, [R19b]).
  - Bourgain–Dilworth–Ford–Konyagin–Kutzarova's Lemma 3 turns flat bounds `|⟨Σ_A u, Σ_B u⟩| ≤ δ(|A||B|)^{1/2}` into the isometry bound with a factor `44 log k`. Its proof uses only subsets of the support, so it works inside `W`.
  - Since the Gram kernel `K` has `Σ_m K(m) = L·w(1) = 0`, Cauchy–Schwarz against `r_{A−B} − |A||B|/L` gives `|⟨Σ_A u, Σ_B u⟩| ≤ c_wM^{1/2}Θ(|A||B|)^{1/2}`, with `Θ² = max(E(A, B) − |A|²|B|²/L)/(|A||B|)` over disjoint `A, B ⊂ W`.
  - So `Θ ≤ q^{1/9−δ}` would give `Δ(W) ≤ q^{1−δ}` up to logarithms. A progression of length `l` in `W` forces `Θ² ≥ l/3 − l²/(4L)`: its halves have `E(A, B) = l(l² + 2)/12` for even `l`. So the route needs `W` to hold no progression longer than about `q^{2/9}`.
- **Progressions in large-values sets.** Take `θ_n = ind(n)/L` on `I = [N, 2N]` and the chirp `b_n = φ(θ_n)e(−lθ_n²/2)`, with `φ` a smooth bump supported in `[1/8, 7/8]` and equal to `1` on `[3/16, 13/16]`. Expand `φ(θ)e(jθ − lθ²/2) = Σ_h c_j(h)e(hθ)`. Then `Σ_n b_nχ_j(n) = |I|c_j(0) + Σ_{h≢0 (L)} c_j(h)Σ_{n∈I}χ_h(n) + O(|I|/L)`.
  - For `l/4 ≤ j ≤ 3l/4` the stationary point `j/l` lies where `φ = 1`, and `|c_j(0)| = l^{−1/2} + O(1/l)`.
  - Van der Corput's second-derivative test bounds the `O(l)` coefficients with `|j − h| ≤ 2l` by `O(l^{−1/2})`, and two integrations by parts give `O(|j − h|^{−2})` beyond. So `Σ_h|c_j(h)| = O(√l)`.
  - With Pólya–Vinogradov the window `{χ_j : l/4 ≤ j ≤ 3l/4}` has `|Σ_n b_nχ_j(n)| ≥ |I|/(2√l)` once `l ≤ cN/(√q log q)`. This exceeds `N^{5/7}` there, since `N/√l` is then about `q^{23/36}` against `q^{20/36}`. So large-values sets can hold progressions of length about `q^{5/18}/log q`, above `q^{2/9}`.
  - **The limit.** Suppose `|Σ_n b_nχ_{a+jd}(n)| ≥ V` for `0 ≤ j < l`, with `|b_n| ≤ 1` and `(d, L) = 1`. Weight the `j` by a Fejér kernel whose Fourier transform is supported in `[−1/2, 1/2]`, at most `2` there, and which is at least `0.81` on `[0, l)`. The weighted sum is at most `2l` times the number of pairs `(n, n′) ∈ I²` with `d(ind(n) − ind(n′))` in an interval of length `L/l` about `0` mod `L`. By orthogonality and Pólya–Vinogradov that number is `N²/l + O(q log³q)`. So `l(0.81V² − Cq log³q) ≤ 2N²`, and `l ≪ N²/V² = q^{4/9}` once `V² ≥ Cq log³q`. At the critical point `V² = q^{10/9}`. If the character sums had their typical size `√N`, the construction would reach that limit; Pólya–Vinogradov gives `q^{5/18}`.
  - **Not a property of large-values sets.** Suppose a large-values set `W₀` of critical size exists, for coefficients `b⁰` with transform `B₀`.
    - Take `l` a small constant times `N/(√q log q)`, so that the Pólya–Vinogradov error is at most a sixteenth of the main term `|I|/(2√l)`.
    - Shift the window (multiply by `χ̄_a`) to where `|B₀| < 2V`. Most shifts qualify, since about `q^{2/3}` characters at most have `|B₀| ≥ 2V`, and the window and its neighbourhood hold `O(l)`.
    - With `ε|I|/(2√l) = 4V`, so `ε ≍ q^{−1/12}`, the coefficients `(1 − ε)b⁰ + ε·chirp` have `|B| ≥ 2V` on the window. They have `|B| ≥ V/2` on all of `W₀` except the `O(l)` characters near the window.
    - So the large-values property and the size together do not imply B16's condition.
  - **The progressions are harmless.** If every arc of length `1/l` holds at most `K` of the points `θ_n`, then `Σ_n|Σ_{j<l}x_je(jθ_n)|² ≤ 4Kl‖x‖²`. So the progression's own `Δ(P)` is `O(N + l√q log²q)`, which at `l = q^{5/18}` is `O(N)` up to logarithms (`l√q = N`). The direct route closes, not a variant that treats structured parts of `W` separately.
  - **Measured** (A3, `q = 10⁴`, `10⁵`, `10⁶`, sharp `I`). The longest window on a grid of `l` found inside `{|B| ≥ N^{5/7}}` has `l = 36`, `106` and `328`, against `N²/V² = 60.0`, `166.8` and `464.2`. Its `Θ²` is `6.32`, `17.66` and `54.99`, against `q^{2/9} = 7.74`, `12.92` and `21.54`. Its `Δ(P)/|I|` is `1.233`, `1.165` and `1.113`. With the chirp removed, no window on the grid is large.
- **Integer relations are subcritical** (B17, [R19c]). For the top eigenvector `x`, put `a = wV` with `V(n) = Σ_{χ∈W}x_χχ(n)`. Then `λ² = Σ_b R(b)ρ(b)`, with `R(b) = Σ_{χ∈W}χ(b)` and `ρ(b) = Σ_n conj(a(bn))a(n)`. The term `b = 1` is `|W|‖a‖²`, and `‖a‖² ≤ λ`.
  - Take the pairs `(n, n′)` with `n/n′ = s/t` in `ℚ`, `(s, t) ≠ (1, 1)` coprime, `s, t ≤ h`, `h² < q`. Then `(s, t) ↦ s/t mod q` is injective and misses `1`, so `Σ|R(s/t)|⁴ ≤ Σ_{b≠1}|R(b)|⁴ = |W|⁴(κ − 1)`.
  - With `c(s, t) = Σ_j conj(a(sj))a(tj)`, Hölder with `4` and `4/3`, and `Σ_{s,t}|c(s, t)|² ≤ (D_h‖a‖²)²`, bound the pairs' part of `λ²` by `|W|(κ − 1)^{1/4}h^{1/2}D_h‖a‖²`. Here `D_h` is the largest number of divisors up to `h` of an `n` in `[N, 2N]`.
  - At `h = √q` their share of `λ` is at most `q^{11/12+o(1)}(κ − 1)^{1/4}`. That is below `q` whenever `κ ≤ q^{1/3−ε}`, and `κ ≤ L/|W| = q^{1/3}` for every `W` of size `q^{2/3}`.
  - Every `b` is `s/t` with `|s|, t ≤ √q`. When `max(|s|, t) < M/2`, `|tn − sn′| < q` forces `tn = sn′`. So the critical mass, if any, sits on wrapped relations `tn − sn′ = jq`, `1 ≤ |j| ≤ 2max(|s|, t)/M`, at heights between `M/2` and `√q`.
  - Measured (A2): the bound holds for every set at every `q`, with `|I_h|` at most `5·10^{−4}` of it. At `h = ⌊q^{0.4}⌋` the integer share of `λ²` is at most `0.0005` for the frontier and concentrated sets, and `0.0018` to `0.0061` for the random sets.
- **Where the eigenvalue sits** (A4). Shares of `λ²` (the decomposition holds to `10^{−14}`), for energy_frontier.py's best set with `κ ≤ 1.25`:

  | `q` | `κ` | `λ/L` | `b = 1` | `H ≤ q^{0.2}` | `H ≤ q^{0.3}` | `H ≤ q^{0.4}` | `\|R\| ≥ 0.3\|W\|` | `\|R\| ≥ 0.1\|W\|` | `\|R\| ≥ 0.03\|W\|` |
  |---|---|---|---|---|---|---|---|---|---|
  | `10007` | `1.23` | `0.436` | `0.097` | `0.201` | `0.434` | `0.716` | `0.037` | `0.634` | `0.885` |
  | `100003` | `1.24` | `0.308` | `0.063` | `0.121` | `0.322` | `0.590` | `0.000` | `0.495` | `0.838` |
  | `1000003` | `1.22` | `0.213` | `0.043` | `0.081` | `0.234` | `0.463` | `0.000` | `0.314` | `0.712` |

  The `|R|` columns leave out `b = 1`. At `q = 10⁶` the concentrated (G1) set (`κ = 8.48`, `λ/L = 0.330`) has `0.413` of `λ²` on `|R| ≥ 0.3|W|`. The random set (`κ = 1.02`) has `λ/L = 0.057`, with `N/L = 0.046`.
- **Reading.** In the sets found, the critical eigenvalue is not carried by integer relations, nor by a few strongly aligned ratios. It is spread over many ratios `b` with `|R(b)|` between `0.03|W|` and `0.3|W|`, on wrapped relations. As `q` grows the mass moves to larger heights and weaker alignment, while the concentration falls about like `q^{−0.155}` (three `q`, one search method, as in §12). On these measurements a proof of core 1 has to control the wrapped part, `Σ R(b)ρ(b)` over the heights between `M` and `√q`. Neither lemma here does.
- **Also tried, in scratch.** Hölder over all `b ≠ 1` with `‖ρ‖_{4/3} ≤ ‖ρ‖_1^{1/2}‖ρ‖_2^{1/2} ≤ N^{3/4}‖a‖²` gives `λ ≤ |W| + |W|(κ − 1)^{1/4}N^{3/4}`. Since `κ − 1 ≥ (L − |W|)²/((L − 1)|W|²)`, about `q^{−1/3}` (Cauchy–Schwarz over `b ≠ 1`), that is at least `q^{7/6}` at the critical point, above `q`.

## 23. Round 555: an energy floor for large-values sets, and the Gauss-sum transfer

The owner asked to keep attacking core 1. No proof emerged. The round proves two elementary lemmas, says what each gives and what it does not, and measures the large spectrum of the interval sum. `transfer_probe.py` checks the lemmas and records the measurements; the register's B18, B19 and G7 record them, and `idea_register.py` (R20) checks their exponents.

- **An energy floor (B18).** Let `b` be supported on the integers of `[N₀, 2N₀)`, with `(2N₀)² < q`, and let `W` be a set of characters with `|S_b(χ)| ≥ V₀` on `W`, where `S_b(χ) = Σ_n b_nχ(n)`. As in §13, put `R(x) = Σ_{χ∈W}χ(x)` and `κ = L·E(W)/|W|⁴ = 1 + Σ_{x≠1}|R(x)|⁴/|W|⁴`.
  - Expanding the squares gives `|W|(V₀² − ‖b‖²) ≤ Σ_{n≠n′} b_n conj(b_{n′}) R(n/n′)`.
  - Hölder with exponents `4` and `4/3` bounds the right side by `|W|(κ − 1)^{1/4}‖ρ‖_{4/3}`, where `ρ(x) = Σ_{n≠n′, n/n′=x}|b_nb_{n′}|`.
  - No ratio wraps: `nm′ ≡ n′m (mod q)` forces `nm′ = n′m`, since both products are below `q`. So `‖ρ‖₂²` is at most `‖b‖_∞⁴` times the number `E_ℤ` of integer solutions of `n₁n₂ = n₃n₄` in the block, and `‖ρ‖_{4/3}⁴ ≤ ‖ρ‖₁²‖ρ‖₂² ≤ ‖b‖₁⁴‖b‖_∞⁴E_ℤ`.
  - Hence `κ − 1 ≥ ((V₀² − ‖b‖²)/‖ρ‖_{4/3})⁴ ≥ (V₀² − ‖b‖²)⁴/(‖b‖₁⁴‖b‖_∞⁴E_ℤ)`. For `|b_n| ≤ 1` and `V₀ = N₀^σ` the right side is `N₀^{8σ−6}` up to a constant and a logarithm, since `E_ℤ ≪ N₀² log N₀`.
  - Cauchy–Schwarz in place of Hölder gives `Σ_{n≠n′}|R(n/n′)|² ≥ |W|²(V₀² − ‖b‖²)²/‖b‖⁴`.
  - Take `b = 1`, and call the height of `n/n′` the larger of its reduced numerator and denominator. The reduced fractions in `(1/2, 2)` of height `h` number at most `h`, and each is `n/n′` for at most `N₀/h + 1 ≤ 2N₀/h` pairs when `h ≤ N₀`. So the pairs with `n/n′` of height at most `H` number at most `2HN₀`, and since `|R| ≤ |W|`, the ratios of height at most `(V₀² − N₀)/(4N₀)` carry at most half of `Σ_{n≠n′}R(n/n′)`. Hölder with `4` and `4/3` over those ratios instead bounds their part by `2(3/2)^{3/4}N₀H^{1/2}|W|(κ − 1)^{1/4}`, using `Σ_{h≤H}h^{−1/3} ≤ (3/2)H^{2/3}`.
- **At the critical point.** The polynomial of length `q^{7/9}` is the square of a block of length `N₀ = q^{7/18}` (§16), and a large-values set of the square at `N^{5/7}` is one of the block at `N₀^{5/7}`. There `(2N₀)² < q`, and [R20a]:
  - the floor is `κ − 1 ≥ q^{−1/9−o(1)}`. Every `W` of size `q^{2/3}` has `κ − 1 ≥ (L − |W|)²/((L − 1)|W|²)`, about `q^{−1/3}` (§22), and a random `W` about twice that. So a large-values set at the critical point carries at least `q^{2/9−o(1)}` times the least possible excess energy;
  - the excess `(κ − 1)|W|⁴/L` is at least `q^{14/9−o(1)}`, which is Proposition 10.2's first term `|W|N^{4−4σ}` at the critical point (§15). With `|W| = q^w` and `N₀ = q^ν`, the two exponents agree exactly when `3w = 1 + ν(14 − 16σ)`. So at the critical point `q^{14/9−o(1)} ≤ E(W) − |W|⁴/L ≤ q^{5/3+o(1)}`, the upper bound being Proposition 10.2's;
  - the Cauchy–Schwarz form gives `q^{5/3}`, against `q^{13/9}` for a random `W`;
  - the ratios of height at most `(N₀^{3/7} − 1)/4`, about `q^{1/6}/4`, carry at most half of `Σ_{n≠n′}R(n/n′)`, with no hypothesis on `κ`. With Proposition 10.2's bound `κ ≤ q^{o(1)}` (the coefficients of the square are at most `q^{o(1)}`), the Hölder form gives more: the ratios of height at most `q^{1/3−ε}` carry a proportion `o(1)`. The block's ratios have height below `2N₀ = 2q^{7/18}`, so the large-values mass sits on the ratios of height between `q^{1/3−ε}` and `2q^{7/18}`.
- **What the floor gives.** It narrows round 535's sharpened target to the sets with `1 + q^{−1/9−o(1)} ≤ κ ≤ q^{o(1)}`, and it places the critical alignment on ratios `n/n′` of height above `q^{1/6}/4`, and above `q^{1/3−ε}` with Proposition 10.2. It does not bound `S₃`. An energy route needs an upper bound on `κ`, which is what Chen–Gupta–Li's energy term uses, or a lower bound of power size (B12). The floor is neither.
- **The large spectrum of an interval, measured** (T4, T5). Take `b = 1` on `[N₀, 2N₀)` and `W` the `q^{2/3}` characters with the largest `|S_b|`: H\*'s simplest instance at a lowered threshold.
  - At `q = 10⁴`, `10⁵` and `10⁶`, the least value on `W` is `N₀^σ` with `σ = 0.670`, `0.674` and `0.677`. `κ − 1` is `0.654`, `1.723` and `3.246`: `15.5`, `83.5` and `331.2` times the least possible value. The floor `((V₀² − N₀)/‖ρ‖_{4/3})⁴` is `0.021`, `0.019` and `0.016`.
  - The share of `κ − 1` from `x = s/t` with `|s|, t ≤ 10` is `0.732`, `0.740` and `0.648`. At `q = 10⁵` the largest `|R(x)|/|W|` are `0.578` at `4/5` and `5/4`, `0.567` at `5/6` and `6/5`, `0.566` at `3/4` and `4/3`, and `0.542` at `2/3` and `3/2` (scratch).
  - In scratch runs, not in the gate, the same construction at `q = 10000019` gives `κ − 1 = 5.47` at `σ = 0.678`, so the growth slows: factors `2.63`, `1.88` and `1.68` per decade. At `|W| = q^{1/2}` and `q^{0.6}` it also grows at each tested `q`.
  - At the critical threshold itself (scratch): for `b = 1` the characters `χ ≠ χ₀` with `|S_b(χ)| ≥ N₀^{5/7}` number `156`, `692`, `2652` and `10092` at `q = 10007`, `100003`, `1000003` and `10000019`, that is `q^{0.548}`, `q^{0.568}`, `q^{0.571}` and `q^{0.572}`. The largest `|S_b|` is about `N₀^{0.80}`. The fourth moment's count `Σ|S_b|⁴/N₀^{20/7}` is `q^{0.753}` to `q^{0.736}` there, its logarithms included. For the weight `sin²` on `[N₀, 2N₀)` no character reaches the threshold at these `q` (largest `|S| = N₀^{0.66}` to `N₀^{0.69}`), as §21 expected.
  - So at these `q` the large spectrum of the interval sum aligns strongly on small primes, and its energy grows with `q` at this threshold. That regime is not the critical one, where the heights up to `q^{1/6}/4` carry at most half, and with Proposition 10.2 the heights up to `q^{1/3−ε}` a proportion `o(1)`. Proposition 10.2 is not tested here: it assumes `1`-bounded coefficients, and the square of the interval sum has coefficients up to `8`, `10` and `14` at these `q`, which lowers the effective `σ` by about `0.25`.
- **The Gauss-sum transfer (B19).** Write the weight as `w(y) = Σ_ξ c_ξe(ξy/q)` on `F_q`. For `ψ ≠ χ₀`, `K(ψ) = Σ_y w(y)ψ(y) = τ(ψ)Σ_{ξ≠0}c_ξψ̄(ξ)`, where `τ(ψ) = Σ_yψ(y)e(y/q)`.
  - So the off-diagonal Gram matrix is `E_W = Σ_{ξ≠0}c_ξD_ξ^*T′_WD_ξ`, where `T′_W` is the matrix of the Gauss sums `τ(χχ̄′)` off the diagonal and `D_ξ = diag(χ(ξ))`. Hence `‖E_W‖ ≤ C‖T′_W‖`, with `C = Σ_{ξ≠0}|c_ξ|`. For the weight `sin²` on `[N, 2N]`, `C` is `0.977`, `1.002` and `1.018` at the three `q`.
  - `T_W = T′_W − I`, the matrix of Gauss sums with its diagonal `τ(χ₀) = −1`, is `L` times the compression of multiplication by `e(y/q)` to `span(W)`. It does not depend on `N` or on the weight. Since `span(W)` is invariant under dilations, every additive character `e(ξy/q)` with `ξ ≠ 0` has the same compression norm.
  - Equivalently, over the `X ∈ span(W)` with `Σ_y|X(y)|² = 1`: `‖E_W‖/L` is the largest `|Σ_y w(y)|X(y)|² − Σ_y w(y)/L|`, and `‖T_W‖/L` the largest `|Σ_y e(y/q)|X(y)|²|`, the additive bias of `|X|²` at the frequency `1`, or at any frequency `ξ ≠ 0`.
- **What the transfer gives.** At the critical point it loses at most the constant `C`: a critical `E_W` makes `T′_W` critical. So a bound on `‖T′_W‖` for the large-values sets is at least B10. It can be much more.
  - `T′_W` sees bias toward arcs of every length. For the annihilator `W = H^⊥` of a subgroup `H`, `span(W)` is the functions constant on cosets of `H`, so `‖T_W‖/L = max_{c≠0}|Σ_{h∈H}e(ch/q)|/|H|` exactly. At `(q, |H|) = (10009, 24)` this is `0.633`, while `‖E_W‖/L = 0.130`. At `(100003, 42)` it is `0.576`, against `0.117`.
  - For a set of minimal energy, a bound `‖T′_W‖ ≤ q^{1−δ}` gives `Δ(W) ≤ N + Cq^{1−δ}` at every length `N` at once. At the threshold `V² = q^{1/3}N`, where the mean value theorem gives exactly `q^{2/3}` at every length `N < q`, it gives `|W| ≤ (N + Cq^{1−δ})/q^{1/3}` [R20b]. At `N = q^{7/9}` that threshold is `σ = 5/7`.
- **Measured** (T1–T3).
  - Random sets have `‖T′_W‖/L` within `2.1%` of `2(α(1 − α))^{1/2}`, `α = |W|/L`. That is the norm of the compression of a unitary with uniformly distributed spectrum by a free projection of trace `α`. It is a calibration, not a theorem about these sets.
  - The frontier sets with `κ ≤ 1.25` have `‖T′_W‖/L = 0.5510`, `0.4195` and `0.3060`: `1.31`, `1.44` and `1.54` times the random calibration. Their `‖E_W‖/(C‖T′_W‖)` is `0.691`, `0.641` and `0.609`; for the (G1) sets it is `0.802`, `0.732` and `0.709`; for the random sets it is `0.17` to `0.30`.
- **Survey and horizon scan** (G7). Two web searches found four abstracts not on file, read through the arXiv API. None states a large-values bound for one prime modulus.

## 24. Round 556: six more routes, and where they stop

The owner asked to keep attacking core 1. No proof emerged. The round records six routes and why each stops. The register's B20–B24 and E8 hold them, and `idea_register.py` (R21) checks their exponents. No probe was run: the claims are exponent arithmetic and short identities. Notation as in §§22–23: the block has length `N₀ = q^{7/18}` and threshold `V₀ = N₀^{5/7}`, its square has length `N = N₀²` and threshold `V = V₀²`, and `|W| = q^{2/3}`.

- **The Hadamard square (B20).** With the convolved weight `w ∗ w`, the Gram matrix of the square is the entrywise square `G ∘ G` of the block's. A large-values set needs `λ_max(G ∘ G) ≥ q`, and Schur's product theorem `λ_max(G ∘ G) ≤ N₀λ_max(G)` turns that into `λ_max(G) ≥ q^{11/18}`. The block's own large values already need `q^{5/6}`, so the structure adds nothing.
- **The large-spectrum energy bound (B21).** Hölder gives `κ ≥ δ⁴|A|` for the characters where the transform of a set `A` exceeds `δ|A|`. For the block, `δ = q^{−1/9}` and the bound is `κ ≥ q^{−1/18}`, below the trivial `κ ≥ 1`. B18 is its effective form.
- **Lemma 10.5 at the block (B22).** Chen–Gupta–Li bound the energy by the third moment of `R` on the ratios of the polynomial's support. At the block the diagonal alone is `q^{11/6}`, a factor `q^{1/6}` above the least energy `q^{5/3}`. At the square it is exactly `q^{5/3}`.
- **The energy squeeze (B23).** At the square, the diagonal of Lemma 10.5's first step, expanded exactly, is the least energy times the mean value theorem's slack `L‖b‖²/(|W|V²)`. With no slack, and a uniform spread of the off-diagonal pairs (a heuristic), it bounds the excess energy by Proposition 10.2's first term `q^{14/9}`, which is B18's floor. So a set exactly at the mean value bound would have its excess pinned at `q^{14/9}`. The density argument must exclude sets a power or a constant factor below that bound, and there the slack term (`q^{5/3−3d}` at `|W| = q^{2/3−d}`) exceeds the floor.
- **The convolution form (B24).** With `J(ψ₁, ψ₂) = τ(ψ₁)τ(ψ₂)/τ(ψ₁ψ₂)`, the Gauss-sum form of §6 is, for fixed `χ₂`, a convolution over `X(q)` against `F/τ`. Its kernel on `F_q^*` is the additive transform of the dual weights, which is the weight again: the second Poisson summation undoes the first.
- **The polynomial method (E8).** Each line sum is an additive correlation `Σ_x A(x)B(αx + β)` of two functions with flat multiplicative spectra in translates of `W`. Stepanov's method, the standard tool for additive shifts of a multiplicative subgroup, uses that a subgroup of order `d` is the zero set of `x^d − 1`. A set of minimal energy has no such description.
- **Reading.** Each route stops for one of three reasons. It is weaker than a condition already in hand (B20, B21, B22). It needs the set to sit within a factor `1 + q^{−1/9}` of the mean value bound (B23). Or it reformulates the problem (B24, E8). None of the routes in §§22–24 reaches core 1. The input they lack is cancellation along the small lines in the additive correlations of functions with flat multiplicative spectra, for sets with no multiplicative structure. No method for that is on the register. *(This round ran no horizon scan: round 555's is from the same day.)*

## 25. Round 557: the Gauss-sum matrix by its moments, energies, and Linnik's deduction

The owner asked to keep hunting, and said conditional results are not of interest. No unconditional route emerged. The register's B25, B26, D4 and G8 record the attempts, and `idea_register.py` (R22) checks their exponents.

- **The Gauss-sum matrix by its moments (B25).** B19 reduces core 1 to `‖T′_W‖ ≤ q^{1−δ}`, which no longer involves the dual sums. The `2k`-th moment of `T′_W` has a tree part `C_kq^k|W|^{k+1}`, the free-probability value. If the other walks were no larger, `k = 3` would give `‖T′_W‖ ≤ Cq^{17/18}`, and a large-values set at the critical point would have `|W| ≤ q^{1/2}`. The other walks at `k = 3` form a sum over a four-dimensional linear section of six values of `R` at consecutive ratios. That sum needs about two-thirds of square-root cancellation, and Cauchy–Schwarz and Hölder with the energy give none, already at `k = 2`. *(Round 558: two-thirds is what matching the free value needs. For a power saving the route needs a little more than half, and `k = 3` needs the least share; see §26.)*
- **Multiplicative energies (B26).** Concentration on `I` forces the multiplicative `k`-energy of `f·1_I` to be at least `c^{2k}q^{(k−1)/3}`. The interval itself has `k`-energy about `N^k/q`, larger for every `k ≥ 2` because products wrap modulo `q`. So no energy condition separates a critical configuration spread over `I` from the interval.
- **Linnik's deduction with phases (D4).** Keeping `χ̄(a)` in the explicit formula saves for most residues `a` (Parseval over `a`), but Linnik's problem needs every `a`. For the worst `a` the near-real zeros give a weighted `R(a)`, which the energy does not bound with a saving.
- **Literature (G8).** For high moments of short character sums, Szabó (arXiv:2409.13436) writes that sharp unconditional upper bounds for large `k` seem "hopeless with our current knowledge, since only one ‘badly behaving’ character could mess up the bound", and the upper bound he cites for `k > 2` assumes GRH. That obstruction bears on core 2, which is about moments. It does not bear on H\*, which is a count. Three new abstracts give nothing unconditional for one prime modulus.
- **Reading.** Two kinds of input would close core 1. One is cancellation in mixed additive-multiplicative sums over arbitrary sets of minimal energy: the six-cycle of B25, or B10 itself. The other is a count of large values of the block that, unlike a moment bound, can ignore a few exceptional characters. The register holds neither, and this round's searches found neither.

## 26. Round 558: the six-cycle as a bilinear form

The owner's instructions stand: keep hunting, and unconditional results only. No unconditional route emerged. The register's B27 and G9, and a marker on B25, record the round. `idea_register.py` (R23) checks the exponents, and `sixcycle_probe.py` checks the identity and the bounds below numerically.

- **What B25's sum needs (marker on B25).** For `k ≥ 3` the tree part of `tr((T′_WT′_W^*)^k)` has exponent `(5k + 2)/3`, below `2k`. The other walks, bounded flat with `|R|` at its typical size `|W|^{1/2}`, give `(8k − 3)/3`. For this route to save a power, the other walks need a saving of more than `(2k − 3)/3` there, out of the `k − 1` that square-root cancellation would give. The share `(2k − 3)/(3k − 3)` is least at `k = 3`, where it is `1/2`, and it stays below `2/3`. Round 557's "two-thirds" is what matching the free value needs at `k = 3`.
- **The six-cycle as a bilinear form (B27).** Let `T_W = [τ(χχ̄′)]` (diagonal `−1`) and `D = diag(χ(−1))`. Then `T_W^* = DT_WD`, so `tr((T_WT_W^*)³) = ‖(T_WD)³‖_F²`. Expanding the Gauss sums gives `q·Σ_{χ₁≠χ₄}|S(χ₁, χ₄)|² + Σ_χ|Z(χ) − S(χ, χ)|²`, with `S(χ₁, χ₄) = Σ_{x+y+z=1}χ₁(x)χ̄₄(z)R(−y/x)R(−z/y)`. The diagonal terms are at most `2κL³|W|⁴ + 2L⁴|W|²`, which is about `q^{17/3}` when `κ ≤ q^{o(1)}`. Orthogonality over all pairs of characters gives `Σ_{W×W}|S|² ≤ L⁴|W|² = q^{16/3}`, and for the sixth moment to save a power the off-diagonal sum must be at most `q^{5−δ}`. The gap is `L/|W| = q^{1/3}`, the density of `W`. Saving the density in both variables would give `q^{14/3}`, the free value.
- **Measured.** `sixcycle_probe.py` checks the identity entry by entry, and the bounds, for fourteen sets at `q = 101, 499, 1009, 2003`. For random sets at the three larger `q` the trace is within 4% of its free value `(5 − 6α + 2α²)L³|W|⁴`, `α = |W|/L`, which tends to the tree part `5L³|W|⁴` as `α → 0`; the probe gates this at 6%. The diagonal part is at most 1.2% of the trace in every case. The sets with the largest block sums exceed the free value by 14%, 26% and 32%, and two subgroup annihilators by 122% and 58% (printed, not gated). At these sizes `L/|W|` is only about `8` to `13`, so the numbers calibrate the conventions and do not separate the regimes.
- **Literature (G9).** Three searches gave six abstracts. They cover short-interval Legendre sums averaged over prime moduli (higher moments only under GRH), short sums of the powers of one character, exponential sums with one multiplicative coefficient, a central limit theorem for very short sums, the Bourgain–Glibichuk–Konyagin bound for small subgroups, and the nonvanishing minors of a compressed Fourier matrix. None of the six abstracts states a norm or large-values bound for an arbitrary set of characters of one prime modulus.
- **Reading.** The six-cycle route now needs one precise input. It is a restricted large sieve on `W × W`, for the function `G` built from `R`, that saves a little more than one density factor `L/|W|` against orthogonality over all characters. Uniform spread would save two. This is an uncertainty statement of B10's kind, and the register holds no tool for it.

## 27. Round 559: the gcd dichotomy

The owner's instructions stand: keep hunting, and unconditional results only. No unconditional route emerged. The register's B28 and G10 record the round. `idea_register.py` (R24) checks the exponents, and `gcd_probe.py` checks the identity and the inequalities below numerically.

- **The dichotomy (B28).** Group the pairs `(n, n′)` of `|D_I(χ)|²` by their gcd. The part from gcd above `G` is `Σ_{f>G}c_f|D_{I/f}(χ)|²`, a combination of squared sums over the shorter intervals `I/f = {m : fm ∈ I}`, with `|c_f| ≤ d(f)`. The cube's mean value theorem at those shorter lengths, with Hölder over `W`, bounds that part by `q^{o(1)}|W|^{2/3}(q^{1/3}N₀ + N₀²/G)`. So at most `q^{1/2+o(1)} + q^{2/3−3d+o(1)}` characters take half of a large value from the pairs with gcd above `q^d`. At the critical point that part carries a share at most `q^{o(1)}(q^{−1/18} + q^{−d})`.
- **What is left.** The pairs with gcd at most `G` have the fourth moment of `|D_I|²` with `log G` in place of `log N₀`. So the critical count drops from `q^{2/3}·O(log q)` to `q^{2/3}·O(log log q)`, which does not move the exponent. The critical characters are those whose large values come from nearly coprime pairs. For gcd `1` that is the large spectrum of the Farey set `F* = {a/b : a, b ∈ I, (a, b) = 1}` (about `q^{7/9}` elements of `F_q^*`) at level `|F*|^{5/7}`, which is core 1 in another form.
- **Measured.** At `q = 10007` and `100003`, the characters with the largest `|D_I|` take a fraction `0.69` and `0.77` of `Σ_W|D_I|²` (as `Σ_W|P_{>1}|`) from the pairs with gcd above `1`. These sets are far from the critical regime, and there the lemma's bound exceeds the mass, so the numbers check conventions only.
- **Literature (G10).** Three searches, one arXiv abstract and two PDFs: additive congruences in inverse powers over short intervals (thresholds near `p^{1/2}`), multiplicative energy of polynomial images of intervals for smooth moduli, and Shparlinski's open-problems survey. None states a sixth moment or a large-values count for short character sums at `N = q^{7/18}` for one prime modulus.
- **Reading.** At most `q^{2/3−3d+o(1)}` critical characters can take their large values from common factors of the pairs. The rest need `χ(a/b)` to align, in aggregate, on the primitive fractions `a/b` of height about `N₀`. No tool on the register counts that.

## 28. Round 560: the sixth moment by the dispersion method

The owner asked to keep hunting. No unconditional route emerged. The register's B29 and G11 record the round, and `idea_register.py` (R25) checks the exponents. No probe was run: the claims are exponent arithmetic and one extremal example.

- **The dispersion route (B29).** Count `x₁x₂x₃ − y₁y₂y₃ = ℓq` as `Ax₃ − By₃ = ℓq` with `A = x₁x₂`, `B = y₁y₂`. For coprime `(A, B)` the solution `x₃ ≡ ℓqĀ (mod B)` is detected by additive characters mod `B`, which leaves bilinear forms `Σ τ_I(A)τ_I(B)e(aĀ/B)` at frequencies `a = hℓq`. Bounded trivially they give an error `q^{31/18}` against the main term `q^{4/3}`. The power saving needs each form below `N₀³q^{−δ}`.
- **Why it stops.** Up to logarithms, `N₀³` is `‖α‖‖β‖M^{1/2}` with `M = N₀²`, the sharp single-frequency bound for arbitrary coefficients (attained with one modulus and matched phases). So single-frequency Kloosterman-fraction bounds cannot give the saving, and the best balanced savings found are `M^{1/48}` and `M^{1/12}`. Summed over the frequencies, the forms give back the original count, so a trilinear bound would need the structure of those frequencies; this round did not test one.
- **As an exponent of distribution.** SIX(δ) is the mean-square distribution of the balanced `τ_{3,I}` mod `q` at `q = x^{6/7}`, `x = N₀³`. With smooth weights, Petrow–Young's Weyl bound and the fourth moment give `q ≤ x^{3/4−ε}` for `d₃` (round 544's `θ = 1/3`). Aydemir–Boran state `8/11` for `d₃` averaged over residues mod a prime.
- **Literature (G11).** Six searches and eleven abstracts on zero density, divisor functions in progressions, and Kloosterman fractions. None applies at the critical ranges for one prime modulus.
- **Reading.** Both cores now meet classical barriers. Core 1 is the large spectrum of the critical Farey set (round 559). Core 2's dispersion route needs, in bilinear form, more than any bound for arbitrary coefficients can give. ~~Its trilinear form is SIX(δ) itself, equivalent to a fixed-modulus sixth moment with `θ < 1/6` in round 544's terms.~~ *(Round 561: retracted, false when written. Summed over the frequencies, the forms are SIX(δ) itself. But no equivalence between SIX(δ) and the fixed-modulus sixth moment was shown, and the register keeps them as cores 2 and 3. B29 compares SIX(δ) with the corresponding statement for `d₃` with smooth weights, which needs `θ < 1/6` by that route. §29 tests the trilinear form, which B29's extremal example does not block.)*

## 29. Round 561: the trilinear form against Bettin–Chandee

The owner asked to keep hunting. No unconditional route emerged. The register's B30 records the round, with a marker on B29, and `idea_register.py` (R26) checks the exponents. No probe was run and no search was made. The round reads Bettin–Chandee's paper (arXiv:1502.00769) from its PDF's text layer.

- **The form (B30).** Summed over the frequencies, B29's error is a trilinear form `Σ_{a,m,n} ν_aα_mβ_n e(ϑaḿ/n)`, with `ḿ` the inverse of `m` mod `n`, `ϑ = q`, `a = hℓ` up to `A = q^{5/9}`, and `m, n` up to `M = N = q^{7/9}`. So `ϑA = MN`. Write the bound as `‖α‖‖β‖‖ν‖·Y`. The trivial bound is `Y = q^{19/18}`, which is B29's error `q^{31/18}`, and the main term `q^{4/3}` needs `Y < q^{2/3}`.
- **What the extremal example allows.** A frequency set concentrated at one point forces `Y ≥ M^{1/2} = q^{7/18}` for any bound valid for all coefficients. That is below `q^{2/3}`, so B29's extremal example does not close the trilinear form.
- **Bettin–Chandee's Theorem 1.** Here its two terms are `q^{14/15}` and `q^{23/24}`. That saves `q^{7/72}`, against the needed `q^{28/72}`: a quarter of the exponent. At a block `q^v` with `1/3 ≤ v ≤ 1/2` the same bookkeeping needs a saving `q^v`, and their bound gives at most `q^{1/8}`.
- **A correction.** §28's reading called SIX(δ) equivalent to a fixed-modulus sixth moment with `θ < 1/6`. No such equivalence was shown, and the sentence is struck there.
- **Reading.** The trilinear form of core 2 is OPEN on the register (B30). In this form it needs a trilinear bound with Kloosterman fractions saving more than `N^{1/2}` in these ranges. That is four times the exponent Bettin–Chandee save. Alternatively, a bound could use the structure of the frequencies `a = hℓ` and of the convolution coefficients. The reduction also owes routine steps this round did not write out: the terms with `gcd(A, B) > 1`, separating the weights, and matching the main term.

## 30. Round 562: spectral bounds for the trilinear form

The owner asked to keep hunting. No unconditional route emerged. The register's B31 records the round, with a marker on B30, and `idea_register.py` (R27) checks the exponents. No probe was run and no search was made. The round read Drappeau's statement of the Deshouillers–Iwaniec bound (arXiv:1504.05549) from its PDF's text layer.

- **Why it was tried.** In B30's form every coefficient is a sum over smooth variables. Deshouillers–Iwaniec's Theorem 12 bounds sums of Kloosterman fractions whose modulus and inverted argument each carry a smooth variable.
- **What it gives (B31).** At a block `q^v` with `1/3 ≤ v ≤ 1/2` the bound is `q^{6v−1/2}`, against the trivial `q^{7v−1}` and the main term `q^{6v−1}`. It is worse than trivial by `q^{1/2−v}`. Its first term is linear in the frequencies' range `N = q^{4v}`, which the factor `q` in `n = hℓq` makes large.
- **Sparsity.** Only `q^{4v−1}` of the frequencies occur. With `N` replaced by that count, the same shape gives `q^{5v−1/2}`, above the main term by `q^{1/2−v}`. The theorem does not state that version.
- **Reading.** Bounds of this shape do not reach B30's target at any block below `q^{1/2}`. B30 stays OPEN.

## 31. Round 563: where the coherence of the small-line sums lives

The owner quoted Holmes on eliminating the impossible, and asked to keep going. No unconditional route emerged. The register's B32 records the round, with a marker on B12, and `idea_register.py` (R28) checks the exponents. `farey_coherence_probe.py` is new. No search was made.

- **What remains.** Every route on the register except B30, which is open (§29), closes or reduces to a core. Core 1's sharpest form is round 535's: for sets of minimal energy, the sums over the small lines must be incoherent. Round 535 found the coherence carried by a heavy tail of pairs of lines. This round looks for where it lives.
- **A common component.** The terms `χ = χ′` of `R(B/x)R̄(B)` give `R̄(x)` on every line, about `1/|W|` of round 535's `θ` (§15 is corrected). Centred, random sets sit at `1.2/|box|` and `1.5/|box|`.
- **On the Farey points** (B32). For the low-energy sets of `energy_frontier.py`, the points `x` of height at most `30` carry `91%` and `72%` of the centred coherence at `q = 10007` and `100003`, though they are `11%` and `1.1%` of `F_q^*`. Random sets show no such concentration. At `x = a/b` every line's argument is a rational of small height, and `R` is biased there on these sets. The pairs of lines that a diagonal scaling relates carry `7%`, though they include the largest entries.
- **A lemma, and what it leaves.** ~~The centred sum is `Σ_{ψ≠1}c_x(ψ)T_ψ(x)` with `|c_x(ψ)| ≤ |W ∩ ψW|`.~~ *(Round 564: retracted, false when written. That expansion holds for the sums built from `R`, not `R₀`, and only up to `Z(x)R̄(x)`, where `Z(x)` counts the lines with `B_m(x) = 0`. The exact form uses the centred indicator `1_W − |W|/L` and an explicit term, and the bound that follows holds with a factor `16`; §32.)* With the energy, a set `A` of characters carries at most `|S||A|κq^{−2/3}` of the coherence on a set `S` of points. The major arcs of length `M` therefore carry at most `q^{−δ}` on the Farey points of height up to `q^{5/18−8η/9−δ}`. Coherence there needs at least about `q^{2/3}/(κH²)` characters acting in phase, most of them off the major arcs.
- **A heuristic.** If `R`'s large values were spread evenly within the energy budget, the Farey points would carry about `q^{−1/9}`, which through round 535's Cauchy–Schwarz and the socket would give `κ = 1/54` at the critical point. That is not a bound.
- **Reading.** The open step of core 1 is now localized. For minimal-energy `W`, the characters off the major arcs must not act in phase at the points of small height, and the points of large height must stay at the random level. The second is what the random sets show, and the first is where the measured coherence lives.

## 32. Round 564: twisted energies on the Farey points

The owner asked to keep digging. The register's B33 records the round, with a strike and a marker in B32, and `idea_register.py` (R29) checks the exponents. `twisted_energy_probe.py` is new. No search was made.

- **A correction.** §31's expansion of the centred sum is exact only for the sums built from `R`, and only up to `Z(x)R̄(x)`. For `X′`, built from `R₀`, the exact form uses the centred indicator `w = 1_W − |W|/L`: `X′(x) + e(x) = Σ_{ψ≠1}c_x(ψ)T_ψ(x)`, with `c_x(ψ) = Σ_χ w(χ)w(ψ̄χ)χ̄(x)` and an explicit term `e(x)` (B33). §31's lemma holds with a factor `16`.
- **Twisted energies.** `Σ_ψ|c_x(ψ)|² = E_x = L^{−1}Σ_z|R₀(z)|²|R₀(x/z)|²`, with `E_1 = (κ − 1)|W|⁴/L` and `|E_x| ≤ E_1`. Cauchy–Schwarz over `ψ` bounds `|X′(x) + e(x)|²` by `E_x` times `ω(x) = Σ_{ψ≠1}|T_ψ(x)|²`. At a point of height `h ≤ 2M` the lines collide at most `128M⁴(1 + log M)/h` times, so `ω(x) ≤ 128LM⁴(1 + log M)/h`.
- **What it proves.** Summed over the Farey points of height at most `H`, the bound is `Σ_φ r_w(φ)²S(φ)` with `S(φ) = Σ_x ω(x)φ(x)`. While `2H⁸ < q`, the eighth moment of `S` is an integer count. Hölder against it gives: the Farey points of height up to `(q/2)^{1/8}` carry at most `q^{−1/36+o(1)}` of `θ′` when `κ ≤ q^{o(1)}`. That piece of core 1 is proved with no hypothesis. It is asymptotic only: the `o(1)` hides a large power of `log q`.
- **What it does not reach.** For the low-energy sets of `energy_frontier.py`, the points of height up to `q^{1/8}` carry `20%` and `7%` of `‖X′‖²` at `q = 10007` and `100003`, and those up to `4M` carry `91%` and `84%`. On the points of height up to `30`, Cauchy–Schwarz over `ψ` loses factors of `135` and `238` for those sets. With the methods tried (Cauchy–Schwarz over `ψ`, Hölder with integer moments, Burgess), the argument stops at height `q^{1/8}`. Above it the eighth moment leaves its integer range, and `S(φ)` is a bilinear sum of `φ` over integers below `q^{1/4}`, where Burgess gives nothing. An eighth moment at its diagonal size beyond that range would carry the bound to height `q^{1/4}`, past `4M`.
- **Reading.** In round 535's form, core 1's open step is now the points of height above `q^{1/8}`, which must carry at most `q^{−2δ}` of `θ′`. Between `q^{1/8}` and `q^{1/4}`, a moment bound for the Farey sums beyond their integer range would give that. Above `q^{1/4}` nothing here bears on it.

## 33. Round 565: the open range as a large-values count

The owner asked to keep going. The register's B33 carries a marker, G12 records a scan, and `idea_register.py` (R30) checks the exponents. No new probe.

- **A cleaner form.** Every `E_x` is a sum of squares, so `E_x ≥ 0`, and `ω(x) ≤ Ω/ht(x)` with `Ω = 128LM⁴(1 + log M)`. So §32's bound over the Farey points of height up to `H ≤ 2M` is at most `Ω·Σ_φ r_w(φ)²S̃(φ)`, with the Farey sum `S̃(φ) = Σ_{x∈F_H}φ(x)/ht(x)`, which does not depend on the lines. Group the characters `φ ≠ 1` by `λ = |S̃(φ)|`, and let `N(λ)` count those with `|S̃(φ)| ≥ λ`. A class carries at most `q^{−4/9+o(1)}λ·min(N(λ/2), (κ − 1)q^{1/3})` of `θ′`, and the term `φ = 1` carries `q^{η−4/9+o(1)}` at `H = q^η`. So, when `κ ≤ q^{o(1)}`, these points carry at most `q^{−2δ+o(1)}` if `N(λ) ≤ q^{4/9−2δ}/λ` for `q^{1/9−2δ} < λ ≤ 4H`.
- **What the moments give.** While `2H^{2k} < q`, `Σ_φ|S̃(φ)|^{2k}` is an integer count and `N(λ) ≤ q^{1+o(1)}λ^{−2k}`, whatever `H`. With `k = 2`, an integer count below height `q^{1/4}` and so on all of `F_{2M}`, this meets the condition for `λ ≥ q^{5/27}`. With `k = 3`, below height `q^{1/6}`, it meets it for `λ` above `q^{1/9}` by any power. With `k = 4`, below height `q^{1/8}`, it meets it for every `λ`, which is §32's bound.
- **What is left.** Between heights `q^{1/8}` and `q^{1/6}`, a count below `q^{1/3−δ}` of the characters with `|S̃(φ)|` near `q^{1/9}`: a power below the sixth moment. Between `q^{1/6}` and `2M`, `N(λ) ≤ q^{4/9−δ}/λ` for `q^{1/9} < λ < q^{5/27}`, where the fourth moment gives `qλ^{−4}`: `q^{5/9}` against the condition's `q^{1/3}` at `λ = q^{1/9}`. Roughly, `|S̃(φ)| ≥ λ` asks that `|Σ_{n≤T}φ(n)|² ≥ λT` on a range of `T ≤ H`. At `T = q^{2/9}` and `λ = q^{1/9}` that is `|Σ_{n≤T}φ(n)| ≥ T^{3/4}`, to be counted below `q^{1/3−δ}`. These are large-values counts for short character sums below the Burgess range, of H\*'s kind (§21). The scan (G12) found none, as G4 found none for H\*.
- **The eighth-moment note.** §32's sufficient input, an eighth moment at its diagonal size above height `q^{1/8}`, says more than it seems to when taken for `S̃`. At a height `H ≥ q^{1/8+ε}` it bounds every `|S̃(φ)|`, `φ ≠ 1`, by `q^{1/8+o(1)}`. But an even character with `φ(n) = 1` for every `n ≤ H` has `S̃(φ) = S̃(1) ≫ H`. So it would give every even nonprincipal character, and the square of every odd one of order above `2`, a value other than `1` below `q^{1/8+ε}`. Burgess's bound with Vinogradov's trick gives `q^{1/(4√e)+ε}`, and `1/8 < 1/(4√e) < 1/6`. The count above has no such consequence: a few characters with `|S̃(φ)|` near `S̃(1)` cost only as much as the term `φ = 1`. *(Round 567: in this stack that consequence is no obstruction. The half-plane's Lindelöf bound (round 522), through Perron's formula, gives every nonprincipal character a value other than `1` below `q^{o(1)}`, and round 482 proves `n(p) ≤ C(log p)^A` for the quadratic ones; §35.)*
- **Reading.** Within this route, a large-values count for short character sums would carry core 1 past height `q^{1/8}`: a power below the sixth moment up to height `q^{1/6}`, and up to `q^{2/9}` below the fourth moment of `S̃` from there to `2M`. That is this route's input, not a bound on what core 1 needs. The route itself loses a factor above `100` at `q ≤ 10⁵` (§32), so a route that keeps the phases of `c_x(ψ)` against `T_ψ(x)` may ask for less.

## 34. Round 566: a sharper trilinear bound, tested against B30

The owner asked to keep going. B30, the register's one OPEN entry, carries a marker; G13 records a scan, and `idea_register.py` (R31) checks the exponents. No probe.

- **The new bound.** Wright (arXiv:2608.27732, Theorem 2.1) sharpens Bettin–Chandee's trilinear bound when the two inner variables run over subdyadic intervals or progressions, of relative length `X^{−η}`. The `A^{7/20}` terms gain `X^{−2η/5}`; the `A^{1/2}` terms are Bettin–Chandee's second term unchanged (G13 quotes the statement).
- **Against B30.** At a block `q^v` with `1/3 ≤ v ≤ 1/2`, B30's form has `A = q^{4v−1}` and `M = N = q^{2v}`. There the second term binds for every `η ≥ 0`, tying the first only at `v = 1/3` and `η = 0`. So the saving stays `q^{v/4}` against the needed `q^{v+δ}`, `q^{7/72}` at the critical block, as in §29. B30's variables `A = x₁x₂` and `B = y₁y₂` also run over full dyadic ranges, and by our count splitting them into subdyadic pieces costs more in the triangle inequality than the pieces gain: `X^{2η}` in the `A^{1/2}` terms.
- **Reading.** B30 stays OPEN. What it asks is a trilinear bound whose `A^{1/2}`-type term, the one that binds here, saves more, or one that uses the structure of the frequencies `hℓq` and of `τ_I`.

## 35. Round 567: block moments, and the half-plane's pointwise bound

The owner asked to keep going. The register's B33 carries a marker, and `idea_register.py` (R32) checks the exponents. No probe.

- **Block moments.** Write `A_y(φ) = Σ_{n≤y}φ(n)`. For even `φ`, `S̃(φ) = ∫_1^∞C(min(t, H))dt/t²` with `C(u) = 2Σ_{e≤u}μ(e)|A_{u/e}(φ)|²`, and `S̃(φ) = 0` for odd `φ`. So `|S̃(φ)| ≥ λ` forces some `y ≤ H` with `|A_y(φ)|² ≥ λy/(2(1 + log H)²)`. Split `[1, H]` into dyadic blocks, and bound the maximal partial sum in each through its dyadic subintervals. On an interval `I ⊂ [1, 2H]` the moment `Σ_φ|Σ_{n∈I}φ(n)|^{2k}` is an integer count while `(2H)^k < q`, at most `q^{1+o(1)}|I|^k`. So `N(λ) ≤ q^{1+o(1)}λ^{−k}`, with `k` the largest integer with `(2H)^k < q`.
- **What it gives.** The worst level is `λ = q^{2/(3k)}`, where `qλ^{1−k}` meets `λq^{1/3}`. So, when `κ ≤ q^{o(1)}`, the points of height up to `H` carry at most `q^{−1/9+2/(3k)+o(1)} = q^{−(k−6)/(9k)+o(1)}` of `θ′`. At even `k` this is §32's Hölder bound, through the moment of `S̃` of order `k`. The odd `k = 7` is new: up to height `(q/2)^{1/7}/2`, at most `q^{−1/63+o(1)}`. A moment of `S̃` counts products of Farey fractions, two integers each, while a block moment counts products of integers, so it stays an integer count twice as long in `k`.
- **What is left.** From height `q^{1/7}` to `q^{1/6}` the block moments have `k = 6`, exactly borderline at `λ = q^{1/9}`. Beyond `q^{1/6}`, `k ≤ 5`, and §33's window stands. *(Round 568: the block moments need not stop at their integer range. The large sieve for one modulus adds a factor `q + (2H)^k` in place of `q`, and with `k = 7` past its integer range the unconditional range reaches `q^{10/63}`; §36.)*
- **The half-plane.** The stack's Lindelöf bound on `Re s ≥ σ₀ > 11/12` (round 522), through Perron's formula, gives `|A_y(χ)| ≪ y^{σ₀}(qy)^ε` for every `χ ≠ 1` mod `q`. So `|S̃(φ)| ≪ H^{5/6+ε}` for every `φ ≠ 1`, which alone reaches height `q^{2/15}`, below `q^{1/7}`. A half-plane `Re s > σ₁` with Lindelöf there would reach `q^{1/(9(2σ₁−1))}`, which is `q^{2/9}` at `σ₁ = 3/4`.
- **The eighth-moment note, revisited.** The same bound gives every nonprincipal character mod `q` a value other than `1` below `q^{o(1)}`: if `χ(n) = 1` for all `n ≤ y`, then `y/2 ≤ |A_y(χ)| ≪ y^{σ₀}(qy)^ε`. Round 482 proves `n(p) ≤ C(log p)^A` for the quadratic characters. So the consequence §33 drew from the eighth moment is already a theorem of the stack and no obstruction to that moment here. §33's comparison with Burgess's bound and Vinogradov's trick stands only as a statement about that method.
- **Reading.** The unconditional range of the Farey points is now `q^{1/7}`. Beyond it this route asks for counts of large short sums a power below the twelfth moment (up to `q^{1/6}`) or further below lower moments, as in §33. *(Round 568: the range is now `q^{10/63}`; §36.)*

## 36. Round 568: the block moments past their integer range

The owner set the goal "keep pushing until exponent is below 7/3". The register's B33 and B32 carry markers, and `idea_register.py` (R33) checks the exponents. No probe.

- **The large sieve.** Round 567 used the block moments `Σ_φ|Σ_{n∈I}φ(n)|^{2k}` only while they are integer counts, `(2H)^k < q`. They need not stop there. The `k`-th power of the sum over `I ⊂ [1, 2H]` is `Σ_m c(m)φ(m)`, with `c(m)` the number of ways to write `m` as a product of `k` elements of `I`. So `m` runs over an interval of length at most `(2H)^k`, `c(m) ≤ d_k(m) = q^{o(1)}` and `Σ_m c(m)² ≤ q^{o(1)}|I|^k`. Within each residue class mod `q` there are at most `(2H)^k/q + 1` such `m`, so Cauchy–Schwarz in each class gives `Σ_φ|Σ_m c(m)φ(m)|² ≤ (q + (2H)^k)Σ_m c(m)²`. Round 567's chaining then gives `N(λ) ≤ q^{o(1)}(q + (2H)^k)λ^{−k}` for every fixed `k`.
- **What it gives.** At height `H = q^η`, `k` contributes the crossing `λ_k` of `q^{max(1, kη)}λ^{−k}` with `q^{1/3}`, so the points of height up to `H` carry at most `q^{e(η)+o(1)}` of `θ′` when `κ ≤ q^{o(1)}`, where `e(η) = min_k (max(1, kη) − 1/3)/k − 1/9`.
  - With `k = 7` past its integer range, `e(η) ≤ η − 10/63`. So the unconditional range of the Farey points is now height `q^{10/63}`, up from `q^{1/7} = q^{9/63}`, with `q^{η−10/63+o(1)}` at height `q^η`.
  - `e(η) = 0` from `10/63` to `1/6`: there `k = 6` is borderline and every other `k` is worse.
  - Below `q^{1/7}`, `e` agrees with round 567 at `q^{1/7}` and `q^{1/8}`. With `k = 8` past its range, it improves round 567's `q^{−1/63}` to `q^{η−11/72}` between `q^{1/8}` and `q^{23/168}`.
- **B32's major arcs.** The same factor lets the fifth moment of `Σ_{m≤M}ψ(m)` run past the wrap, `M⁵ = q^{10/9}`. It leaves at most `q^{20η/9+o(1)}` characters with `|Σ_{m≤M}ψ(m)| ≥ M^{1−η}`, fewer than the fourth moment's `q^{1/9+16η/9}` when `η < 1/4`. With B32's lemma, under minimal energy these characters carry at most `q^{−δ}` of `θ′` on the points of height up to `q^{1/3−10η/9−δ}`. That covers all of `F_{4M}` for `η < 1/10`, against `η < 1/16` before.
- **What is left.** From height `q^{10/63}` to `q^{1/6}`, the count at `λ = q^{1/9}` must be a power below `q^{1/3}`. The twelfth moment gives `q^{1/3}` there, and the fourteenth with the large sieve gives `q^{2/9} + (2H)^7q^{−7/9}`, which is larger. Beyond `q^{1/6}`, §33's window stands. Off the Farey points, B32's requirement that the points of large height carry `θ′` at the random level is still owed. The twisted-energy bound does not give it. At those points `ω(x)` is about `L|box|` and `E_x` averages about `|W|²`, so the summed bound is about `q^{1/3}` times the target.
- **Reading.** This is a small extension of an unconditional partial result inside core 1's Farey route. It does not touch the points of large height, and no exponent below `7/3` follows.

## 37. Round 569: Turán's power sums at σ = 5/7, the half-plane form of the reflection route, and §7's unsurveyed machinery

The owner's goal stands: "keep pushing until exponent is below 7/3". This round derives what the register left underived at `σ = 5/7`: Turán's power-sum method (A2, A3), the half-plane form of round 526's reflection route (B5), and two items of §7's "Not surveyed" list. All of them stay closed. `idea_register.py` (R34) checks the exponents. No probe.

- **Why Turán's method looked promising.** The barrier `B = {7/18, 7/9} ∪ [7/6, ∞)` of §4 has its two points a factor exactly `2` apart. A mollifier detector's blocks always meet `B` (§4's (B2)). Turán's second main theorem detects a zero through the derivatives of `L′/L` of the orders in `[m + 1, m + n]`. With `m = n − 1` that range has ratio `(2n − 1)/n < 2`, and so does the range of detection lengths. A range of ratio below `2` can sit inside `(7/18, 7/9)`, where some power of every block lies strictly inside the good window (§4's (B1)).
- **What it costs.** The theorem's lower bound carries the factor `(n/(8e(m + n)))^n`, which is about `(16e)^{−n}` at `m = n − 1`, with `n` the number of zeros in the disc around the detecting point.
  - The detecting point lies where the Dirichlet series of `L′/L` converges: with the half-plane, at `Re s > 11/12`.
  - There the half-plane bounds `|L|` below by `q^{−o(1)}`. That is our derivation from the zero-free region by the Borel–Carathéodory argument, not a Lean theorem.
  - A disc centred on `Re s = 11/12` that stays in `Re s ≥ 1/2` has radius at most `5/12`. A zero at `β = 5/7` lies at distance at least `17/84` from the centre, so Jensen's formula gains only `log(35/17)` per zero.
  - So a character whose disc holds `n` zeros has `|L| ≥ q^θ` on the disc's boundary once `n ≥ θ log q/log(35/17)`, and not necessarily before.
- **The trade-off.** The fourth moment counts the characters with `|L| ≥ q^θ` near the critical line by about `q^{1−4θ}`, treated optimistically as if the boundary lay on the line. That is below `q^{2/3}` only for `θ > 1/12`. The other characters can have `n` up to `(1/12)log q/log(35/17)`, and for them Turán's factor is `q^{−0.435…}`. The detected value then sits that factor below the level `N^{5/7}`. At every scale of the good window, the mean value theorem's count at that reduced level is at least `q^{4/7+0.87…}`, against the `q^{2/3}` needed. So Turán's method, with Turán's second main theorem as the lemma, does not move the critical count. A2 had been closed only through the exponent database's recorded bounds. It is now closed at `σ = 5/7` by this derivation, and A3 with it.
- **The half-plane form of the reflection route.** Round 526's bound `GN/V² + G³NqT/V⁶`, with `G = Σ|a_n|²`, carries `qT` in its second term. In this round's reading of round 526's proof, that factor is the large sieve's at the length of the product of the polynomial with its dual.
  - At `σ = 5/7` the second term is `qN^{4−6σ}`: `q^{7/9}` at `N = q^{7/9}` and `q^{8/9}` at `N = q^{7/18}`.
  - The half-plane improves the pointwise Gram entries from `√q` to `N^{1/12}q^{5/12}` (B5): by `q^{1/54}` at `N = q^{7/9}` and by `q^{11/216}` at `N = q^{7/18}`.
  - Even taken squared off the factor `q`, that gain leaves `q^{20/27}` and `q^{85/108}`, above `q^{2/3}`.
- **§7's "Not surveyed" list.**
  - Additive, planar and higher-order large sieves. For all the characters of one prime modulus the additive sieve is the multiplicative one through Gauss sums. The planar sieves concern Hecke characters over `ℤ[i]` or `ℤ[ω]`, and the higher-order ones the residue symbols of a fixed order over varying moduli. These families meet the characters mod `q` only through base change (E7) or in the two cubic characters mod `q`. So they bear on no set `W ⊂ X(q)` of size `q^{2/3}`.
  - Metaplectic and cubic theta. The stack's own cubic-theta family (the half-plane's proof, round 466) bounds the Möbius signal `A_1^{(χ)}(Z) = Σ_𝔞 μ(𝔞)χ(N𝔞)W(N𝔞/Z)` by `Z^{(11+5σ)/12+ε}` through its sixth-power members. Over `χ mod q`, the large sieve on each member costs `(q + Z)Z`, so the extraction gives `Σ_χ|A_1^{(χ)}(Z)|² ≲ (q + Z)Z^{(11+5σ)/6}`: the pointwise size on average, not less. At `β = 5/7` the count this gives is at least `q`. A zero also makes the Möbius signal large only through the residues `1/L′(ρ)`, at no controlled scale.
- **Reading.** The register's routes stop at core 1 (B1, B12), core 2 (`SIX(δ)`), cores 3 and 4, or the barrier itself. This round adds no route. No exponent below `7/3` follows.
