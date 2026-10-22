# The release's exponent system at 5/6

Side-branch note, 2026-10-22, on branch `claude/latest-commit-branch-ik1pj3`. It follows `PAIRING.md` in this directory. It is not a README round, and it adds no Lean. The numbers below come from the gate script `fivesixths.py` (section 6), or are quoted from the sources cited.

**The question.** The owner's goal: "widen the zero free strip to at least 5/6", that is, a zero-free half-plane `Re s > 5/6` for the release's families. This note asks what the release's method, as the pilot models it (README rounds 496–508, `frontier/wall78`), would need to reach `5/6`. It does not reach it. It finds where `5/6` sits in that exponent system and names the two inputs that are missing.

**Summary.**
1. **Horizon scan** (section 0). Nothing found reaches `5/6`. The best recorded boundary is Liu's `B_♭ = 0.874886647…` (arXiv 2610.26835, 19 October, every number field).
2. **5/6 is the floor of the release's low side** (gate F1, exact). Given the Gram bound's range `b ≥ 0` and the compensated probe's `l_x > ℓ`, the low side satisfies `s₀ − 5/6 = (M − 2ℓ)/12 + (Gram excess) + L/2 + μ/2 ≥ (l_x − ℓ)/6 ≥ 0` in every geometry. Equality holds only at `l_x = l_y = ℓ` with no row loss and no crossing. In `PAIRING.md`'s reading, `β_b = 5/6 − ℓ/6 + M/12 + L/2`. There the amplifier's gain `ℓ/6` is exactly what the theta deficit `M/12` takes back once `M ≥ 2ℓ`.
3. **The second branch is a slot sum at a trivial dual** (gates F3, N1).
   - Round 500's second branch is attained at a dyad whose dual is trivial and whose slots are all active. There the completed row is a fixed multiple of `Σ_P a(P)/√q_P`, and Lemma `lem:hybrid-energy` bounds that sum by Cauchy–Schwarz.
   - By the release's marked reflection, `a(P)` is a product, over the active slot primes `q`, of the normalized cubic Gauss sum `γ₂(q)`, the angle `ᾱ(q)²` and finite-order characters.
   - Over the 7827 split primes of norm `≤ 8·10⁴`, of the twists `α^k` with `|k| ≤ 3` only the untwisted sum `Σ γ₂(π)` carries Patterson's main term: `893` against `√n = 88`. Every twist `α^k` with `k ≠ 0` is at square-root size; at `k = −2`, the slot coefficient's twist, the sum is `91`.
4. **The low side's least value** (gate F2, closed form). Let `σ` be the slot sum's exponent: its square is `Z^{σ z_a}`. Then the least low side over all geometries is `5/6 + max(0, (2σ − 1)/(6(4σ + 1)))`:
   - `13/15` at the release's `σ = 1`;
   - `28/33` at `σ = 2/3`, the size of the cubic large sieve's `(NL)^{2/3}` term at a trivial dual;
   - exactly `5/6` for every `σ ≤ 1/2`.
5. **The whole exponent system at 5/6** (gates F4, F5, F6). Take round 499's program with round 500's crossing cost, Xu–Sang's admissibility rows and round 498's readings. Add four more:
   - no numerator rotation, which makes Xu–Sang's `h < 2l_y` idle;
   - the third Gram term carried in the low side's maximum;
   - the small rows' `z`-line near `1/6`;
   - a uniform row-sum saving `U^η` on every bin.

   With all of these, the boundary is `5/6`, at the vertex `l_x = l_y = ℓ = 1/3`, provided `σ ≤ 1/2` and `η ≥ 0.168`; Xu–Sang's own counts and fourth moment need `η ≥ 0.178`. At `σ = 2/3` the same system gives `28/33`.
6. **What is missing.** Two estimates, neither in the sources read here:
   - the release's trivial-dual slot sums with `σ ≤ 1/2`, that is, angle-twisted cubic Gauss sums over primes below `X^{3/4}`;
   - a saving `U^{1/6}` on the high side's sums over the Poisson rows near `a = 1/2`, where the C₀ wall sits.

   The register gets both as targets (section 5). This note does not prove either, and so does not prove `Re s > 5/6`.

## 0. Horizon scan, 2026-10-22

CLAUDE.md asks for a scan at the start of each RH-strand round series. Each item below was read in its arXiv abstract (the arXiv API), except Xu–Sang's 2610.15291v2, whose LaTeX source was read where section 3 quotes it.

- `github.com/openai/math` is at `1581d4c` (`git ls-remote`), as in round 506.
- **arXiv 2610.26835**, Baiying Liu, "Zero-free half-planes for Hecke L-functions over number fields" (v1, 19 October). It extends the cubic-theta argument to cyclotomic fields containing `μ₁₂` and, adapting Xu–Sang's averaged numerator "combining it with a limiting contradiction argument, we obtain the boundary `$B_\flat=0.874886647039964\ldots$`", "the exact infimum of the refined comparison system, unattained by finite chains starting above it", and concludes that "every finite-order Hecke `$L$`-function over every number field is zero-free for `$Re(s)>B_\flat$`". New against the pilot.
- **arXiv 2610.15291v2** (15 October), now by Yuanda Xu and Hejian Sang and titled "Amplified moments and a refinement of the quasi-Riemann hypothesis". The abstract keeps "`$8748867/10000000=0.8748867$`". New version against the pilot (round 506 recorded v1).
- **arXiv 2610.17675v2** (14 October), Xu and Sang, now "A matching lower bound for the sextic large sieve and structured prime moments": "we prove a lower bound of order (AB)^(-epsilon) times (A + B + A^(5/6) B^(1/3) + A^(1/3) B^(5/6)), matching de Faveri's upper bound throughout the full parameter range".
- **arXiv 2610.15989v2**, Yangbo Ye, "Zero density in short strips and short-interval bounds toward Hypothesis S": it uses "the recent quasi-Riemann theorems" as an input.
- **arXiv 2610.18214**, Michel Planat, on the de Bruijn–Newman constant; its abstract "records Raymond's ceiling below `\(0.116398\)` under the distinct `\(7/8\)` zero-free hypothesis".

None of these reaches `5/6`, or claims a boundary below Liu's `0.8748866…`. The Lean community was not searched.

## 1. The floor

The release's low side, as the boundary it gives (README round 503), is

`s₀ = 5/6 + l_x/6 − ℓ/6 + max(0, θb, 2b − l_y)/2 + L/2 + μ/2`,

with `θ = 1/6` (the Gram bound's exceptional term), `L` the completed rows' norm loss and `μ = (M + ℓ − 1)₊` the crossing (round 500). Two of the method's own conditions bound it below:
- the Gram bound's range, "`P_a=Y'^2/Q\ge1.`" (README round 499), which is `b ≥ 0`;
- the compensated probe's geometry: it rescales `X` and `Y` by every slot product, and Xu–Sang state "We will require `\begin{equation}\label{eq:low-geometry} l_x>\ell,\qquad l_y-\ell>11b/6. \end{equation}`".

With `b ≥ 0` the Gram term is at least `b/12`, and `l_x/6 + b/12 = M/12`. So

`s₀ − 5/6 = (M − 2ℓ)/12 + (max(0, b/6, 2b − l_y) − b/6)/2 + L/2 + μ/2 ≥ (l_x − ℓ)/6 ≥ 0`.

**Gate F1** checks the identity and the inequality at 4000 random rational geometries. It also checks that equality holds exactly when `l_x = l_y = ℓ` and `L = μ = 0`, and that the identity agrees with `lowbudget.steps` (round 503) at the 1113 geometries where both are defined. The vertex `(1/3, 1/3, 1/3)` gives exactly `5/6`.

**The theta reading.** In `PAIRING.md` the boundary is `β_b = 5/6 − ℓ/6 + M/12 + L/2`: the amplified Möbius mass reaches the completed rows' energy bound there. The slots gain `ℓ/6`, and the theta function's energy deficit on `Z^M` rows costs `M/12`. With `b ≥ 0` and `l_x > ℓ`, `M = l_x + l_y ≥ 2ℓ`, so in this exponent system the slots' gain does not exceed the deficit, and the base `5/6` stays. That base is the Möbius mass's exponent `1/2 + 1/3` at order 6.

## 2. The second branch: a slot sum at a trivial dual

**Where the loss is attained.** Round 500's dyad program (`crossing.py`) maximizes the energy exponent of Lemma `lem:reflected-energy` over the dyads. On the slice, its second branch `M′ + (1 + 3ℓ′ − 2M′)/4` is what limits `ℓ` to Sang's `1/5`. **Gate F3** finds the maximizing dyad at `(M′, ℓ′) = (2/3, 1/3)`:
- the dual is trivial (`v = ℓ_b = e = 0`) and every slot is active (`z_a = ℓ′`);
- the powerful part has `O = M′ − (1 − ℓ′)/2`;
- `E = O/2 + H + z_a` exactly.

With the powerful part forced to `0`, the maximum is `M′ + 1/9`, at a dyad whose squarefree dual part is again trivial (`v = 0`, cube part `ℓ_b = 2/9`).

Take such a dyad. The release identifies the moving columns as "`\chi_R(nb^3)^3=\chi_R(nb)^3,\qquad \chi_P(nb^3)^{-2}=\chi_P(n)^{-2}1_{(P,b)=1}.`" So at `n = 1` they carry no character of `P`, and each row's completed sum is a fixed multiple of `Σ_P a(P)/√q_P`. The lemma assumes only "`|a(P)|\le1,\qquad |\beta(n,b)|\le1.`", and its bound at `N = 1` is Cauchy–Schwarz, `Z^{z_a}`.

**What `a(P)` is.** By Corollary `cor:marked-reflection`, an active marked prime `q` carries the scalar factor "`\chi_q(\sigma_q)^{-2}(-\omega_{q,0})`", with "`-\omega_{q,0}=\tau_{q,2}^{+}\chi_q(\epsilon_q)^{-2}`" and "`\tau_{p,m}^{\pm}=q_p^{-1/2}\sum_{y\bmod p}\chi_p(y)^m e(\pm y/p),`". That is `γ₂(q)`, the normalized cubic Gauss sum, by the release's "`\gamma_j(c)=q_c^{-1/2}\sum_{v\bmod c}\chi_c(v)^j e(v/c),`". The same scalar has "`\bar\alpha(c)^2`", with "write `$\alpha(a)=a/|a|$`". The primal slot coefficient is "`\overline{\eta(p_i)}W_i(q_{p_i}/P_i)`". The other factors are cubic symbols of fixed elements, the pairwise mark–mark phases and the target's finite-order `η̄`. So, as a function of the slot prime, `a(q)` is `γ₂(q)ᾱ(q)²` times finite-order factors.

**Patterson's bias (gate N1).** Over the 7827 split primary primes of norm `≤ 8·10⁴`, in the pilot's Gauss sums (`composite.py`, `periods.c`):
- `γ₂³ = μα` at every prime (error `1.2·10⁻¹¹`), as in the release's eq. (signal);
- `|Σ γ₂(π)α(π)^k|` is `893` at `k = 0`, against `√n = 88.5`, growing with log-slope `0.77` between `2·10⁴` and `8·10⁴`: Patterson's main term `X^{5/6}/log X`;
- every twist with `k ≠ 0` stays at square-root size: `112, 91, 160, 43, 49, 34` for `k = −3, …, 3`.

The slot coefficient is the case `k = −2`. So at these sizes its prime sums carry no main term.

**The exponent `σ`.** Write the slot sum's square as `Z^{σ z_a}`.
- The release's bound is `σ = 1`.
- `σ = 2/3` is the cubic large sieve's `(NL)^{2/3}` term at a trivial dual (`N = 1`). The release quotes that sieve from Heath-Brown: "`\{U+V+(UV)^{2/3}\}`". It is also the size of Patterson's main term, which the theta-aligned coefficients (`k = 0`) attain.

With the cubic sieve's `L` term dropped for these coefficients, the dyad program's maximum becomes `M′ + max(0, M′ + ℓ′ − 1, (1 + 5ℓ′/3 − 2M′)/4)`. **Gate F3** checks this at 300 random `(M′, ℓ′)` with `ℓ′ ≤ 0.36`; above `ℓ′ ≈ 0.4` another branch appears, which this note does not need. In general the second branch becomes `(1 + (4σ − 1)ℓ′ − 2M′)/4`.

**The low side's least value (gate F2).** Over the whole geometry, with `b ≥ 0`, `l_x ≥ ℓ`, the first-branch crossing at cost `1` and a retained dyad:

`min s₀ = 5/6 + max(0, (2σ − 1)/(6(4σ + 1)))`

The linear programs agree with this to `10⁻¹⁶` at `σ = 0, 1/4, 1/2, 2/3, 3/4, 1`:

| `σ` | least low side | where |
|---|---|---|
| `1` (the release) | `13/15` | `ℓ = 1/5`, round 496's W6b |
| `3/4` | `41/48` | `ℓ = 1/4` |
| `2/3` (the cubic sieve's `(NL)^{2/3}` term) | `28/33` | `ℓ = 3/11` |
| `≤ 1/2` | `5/6` | `l_x = l_y = ℓ ∈ [1/(5 − 4σ), 1/3]` |

Without `l_x ≥ ℓ`, `σ = 0` goes down to `2/3`. That condition is what makes `5/6` the floor.

So the release's low side reaches its floor only with `σ ≤ 1/2`. That means slot sums of angle-twisted cubic Gauss sums over primes of size `X^{3/4}` or less. N1 suggests that their true size is near `X^{1/2}`. The obstacle is the method's bound, not a main term.

## 3. The whole exponent system at 5/6

`fivesixths.py`'s `Five` extends `offslice.OffSlice` (round 499) with:
- round 500's crossing cost on the first branch only;
- the second branch at exponent `σ`;
- a uniform row-sum saving `U^η = Z^{ηh}` on every bin: the bins with `δ ≥ 1/8`, the small bins and the floor bin;
- the small rows' `z`-line `z₀`;
- dropped rows.

**The readings it needs.** Each is a reading of the cited text, in the sense of round 498, not a re-derivation.
- **No rotation.** Xu–Sang impose `h < 2l_y` for the rotated numerator: "The next section therefore imposes `\(h<2l_y\)`: at the critical row scale `\(d=h\)`, the averaged numerator then improves the complete high-side estimate, not just one factor." Their admissibility list files it under "`\emph{Prime supply and numerator amplification.}`". With `ϑ = 0`, the factor "`\(Z^{\vartheta(d/2-l_y)}\)`" is `1`, and the condition does nothing. Round 507 found that on Sang's slice, from `k = 5/2` on, "the best numerator line is `Re w = 1/2`, unamplified".
- **The third Gram term soft**: round 499's S3. The condition's one use is "and hence `$P_a^2/Y'\ll P_a^{1/6}$`".
- **The small rows' `z`-line.** Xu–Sang: "For rows below `\(Z^{d_{\min}}\)`, including the nonprincipal unit rows, the absolute numerator bound and full correction give exponent at most `\(C_b(\beta_*)+h(z_0-1/6)-l_y/2+2d_{\min}\)`", with "`\(z_0=17/50\)`". The release's line for these rows is "`x_r=\beta_*+e,\qquad w_r=1/2,\qquad z_r=17/50,`". Its proof uses four exponents off `u`, "`Q^{-x_r}+Q^{-6z_r} +Q^{4-5x_r-6z_r}+Q^{1-w_r-6z_r}`", the boundary terms on `u`, and the first Euler region's normal convergence. **Gate F6** checks every one of these at `x_r = 5/6`, `w_r = 1/2`, `z_r = 1/6 + 1/100`; the line stays right of `ζ_F(6z)`'s pole at `1/6`.
- Round 498's five readings, `ℓ ≥ 1/6` dropped (rounds 501–502), and Sang's `ℓ ≤ 1/5` replaced by the second branch at `σ`. **Gate F6** also checks that at the vertex the rescaled tuples' exponent `−d + L_σ(d)/2` is at most `0`, so the low side is still taken at `d = 0`.

**Results** (gates F4, F5; `κ` least over `13/18`, `0.7226111` and `3/4`; "no rotation" means the readings above):

| configuration | `σ` | `η` | `z₀` | boundary | at `(l_x, l_y, ℓ)` | walls |
|---|---|---|---|---|---|---|
| round 498's "everything" (Gram removed) | `1` | `0` | `17/50` | `0.8613056` | `(0.3345, 0.4988, 0.1667)` | as recorded |
| Lindelöf + all readings | `1` | `0` | `17/50` | `0.8667866` | `(0.4002, 0.4002, 0.1995)` | as recorded |
| DH + Lindelöf, no rotation | `2/3` | `0.13` | `17/50` | `28/33` | `(0.3636, 0.3636, 0.2727)` | `b > 0`, low side, row loss |
| Sang's counts and fourth moment, no rotation | `1/2` | `0.18` | `1/6 + 1/100` | `5/6` | `(1/3, 1/3, 1/3)` | `b > 0`, low side, `l_x > ℓ`, row loss |
| DH + Lindelöf, no rotation | `1/2` | `0.18` | `1/6 + 1/100` | `5/6` | `(1/3, 1/3, 1/3)` | the same |
| Sang's, no rotation | `1/2` | `0.18` | `17/50` | `0.835` | `(0.3267, 0.3467, 0.3267)` | the small rows |
| DH + Lindelöf, no rotation | `1/2` | `0.16` | `1/6 + 1/100` | `0.8351476` | `(0.3370, 0.3370, 0.3261)` | the floor bin |
| DH + Lindelöf, no rotation | `1` | `0.3` | `1/6 + 1/100` | `13/15` | `(0.4, 0.4, 0.2)` | row loss |

**The row saving the vertex needs (gate F5).** At `(1/3, 1/3, 1/3)`:
- `h = 1`, and round 499's C₀ wall `4/3 − 5l_x/6 − l_y/2 + ℓ/3` is `1`, so `η ≥ 1/6`.
- The floor bin adds half its width: DH counts with Lindelöf reach `5/6` at `η = 0.168` and not at `0.166`.
- Xu–Sang's counts and fourth moment reach it at `0.178` and not at `0.175`, with the bins `E` binding below.

The boundary `5/6` is approached, not attained: `b > 0` and `l_x > ℓ` are strict, and at `σ = 1/2` the second branch is tight there. Liu's and Xu–Sang's limiting contradiction arguments are of that kind.

## 4. What it would take

Within this exponent system, the half-plane `Re s > 5/6` needs both of:

1. **The slot sums at a trivial dual with `σ ≤ 1/2`.**
   - The target: `|Σ_P a(P)/√q_P|² ≪ Z^{z_a/2 + ε}` for the release's slot coefficients, which are products of `γ₂(q)ᾱ(q)²` and finite-order factors over the slot primes.
   - In one slot, that is `Σ_{q ∼ P} γ₂(q)ᾱ(q)²ψ(q) ≪ P^{3/4 + ε}` over primes. The sources read on this branch bound such sums only through the cubic large sieve, whose `(NL)^{2/3}` term gives `σ = 2/3` and the floor `28/33`.
   - N1 finds no main term at `k = −2`. Dunn and Radziwiłł's corrected large sieve (`CUBIC.md`, section 2) subtracts the theta term and beats `(AB)^{2/3}`, "albeit only for sequences that have substantial cancellations against all non-principal cubic characters".
2. **A row-sum saving `U^η`, `η ≥ 1/6`, on the bins near `a = 1/2`.**
   - The high side bounds each Poisson row's contribution absolutely, then sums over the rows of a bin.
   - At `δ → 0` every row counts (`R = 1`), and that sum is the C₀ wall.
   - A saving there means cancellation in `Σ_u q_u^{−z}ξ̄(u)ζ_F^S(6z)L^S(w, χ_•(u))/L^S(s, ηχ̄_•(u))·𝔥_{η,u,Z}` over the rows `u` (the release's eq. `stage-high-identity`), on lines near `Re s = 1/2`.

The other ingredients are readings of the cited texts (section 3) or the configurations of round 498 (DH counts or Lindelöf on average help, but are not needed: Xu–Sang's own counts and fourth moment reach the vertex at `η ≥ 0.178`).

**Where the walls meet.** At `l_x = l_y = ℓ = 1/3` four walls meet at `5/6`:
- the low side's floor (`l_x = ℓ`, `b = 0`);
- the second branch at `σ = 1/2`;
- the cube-dual branch of section 2, `(1 + ℓ′ − 2M′)/3`, which is `0` at `M′ = 2/3`, `ℓ′ = 1/3`;
- the C₀ wall at `η = 1/6`.

So `5/6` is a natural point of the method, not an arbitrary target. By gate F1, going below it in this exponent system needs a geometry without `l_x > ℓ` or `b ≥ 0`, or a low side without the exceptional Gram term. Rounds 504–505 found that removing that term removes the principal residue with it.

## 5. Outcome, register entry and signals

**Outcome.** The goal is not reached. This note proves no new zero-free region. It maps what the release's method needs for `5/6`, and finds `5/6` to be that method's floor.

**Check 9 (a), scope.** Every boundary, floor and threshold here is a statement about the pilot's model of the release's exponent system (rounds 496–508), with the readings of section 3. That includes "the floor" and "needs".
- "The floor" assumes `b ≥ 0`, `l_x > ℓ` and the exceptional term `θ = 1/6`.
- "Needs" is relative to the configurations computed: twelve programs in F4 and F5, and the low side's linear programs in F2.
- The statement that the sources read bound the slot sums only through the cubic large sieve is scoped to the release, Xu–Sang's v2 and the notes on this branch. The literature on prime sums of cubic Gauss sums was not surveyed, so no claim is made about what it contains.

**Check 9 (b), register.** STRUCTURAL-REVIEW §6, the sub-entry "Below `7/8` in the release's exponent comparison", gets a bullet "The release's exponent system at `5/6`" with two targets.
- **T1, trivial-dual slot sums with `σ ≤ 1/2`.**
  - Socket: the `L` term of Lemma `lem:hybrid-energy` inside the second branch of Lemma `lem:probe-row-norm`, which is `fivesixths.py`'s gate F3.
  - Attack notes:
    1. a corrected cubic large sieve, in the sense of Dunn–Radziwiłł's Proposition 9.1, for angle-twisted Gauss-sum coefficients, which do not attain the `(NL)^{2/3}` term;
    2. a Type I/Type II decomposition of the slot sums, whose Type I part has no pole for `k ≠ 0`;
    3. slot structures other than single primes, which the compensation would have to accommodate.
- **T2, a row-sum saving `U^{1/6}` near `a = 1/2`.**
  - Socket: the bins' sums in Lemma `lem:bin-contour-accounting` and Xu–Sang's eq. `full-exponent` at `R = 1`.
  - Attack notes:
    1. the diagonal of the ratio average over `u`, where `ξ`, nonprincipal at every prime of `S`, may vanish;
    2. the sextic large sieve over the rows, whose limits Xu–Sang's matching bound now fixes;
    3. a first moment of the reflected numerator with the inverse polynomial in place of Sang's fourth moment.

**Check 9 (c), signals.** The signal is unchanged: the release's probe. T1 bounds Gauss sums at primes. They do not involve the target's zeros, so the input is auxiliary, not circular. T2 concerns the sum over the twisted rows near `Re s = 1/2`. The hypothetical zero sits near `5/6`, not on those lines, so T2 is auxiliary too.

**The machinery checklist.**
- Surveyed:
  - the release's Corollary `cor:marked-reflection`, Proposition `prop:completed-reflection`'s scalar, Lemmas `lem:hybrid-energy`, `lem:reflected-energy`, `lem:probe-row-norm` and `lem:compensated-absolute-local-bounds`, the local Euler regions, and Definition `def:stage-high-data`;
  - Xu–Sang's v2 sections on the low estimate, the numerator and admissibility;
  - the pilot's Gauss sums for Patterson's bias.
- Not surveyed:
  - the literature on cubic Gauss sums over primes;
  - ratio averages over sextic families;
  - large values of Guth–Maynard type for the rows near `1/2`.

## 6. Reproduce

From this directory:

```
python3 fivesixths.py periods_w_8e4.txt    # gates F1-F6 and N1, about 15 s
```

`periods_w_8e4.txt` is the prime data of `PAIRING.md` section 7 (`./periods w 80000`). Without it, N1 is skipped and reported. The script imports `crossing.py`, `offslice.py`, `levers.py` and `lowbudget.py` from `../wall78`.

In session runs these perturbations fail the gates shown:
- the exceptional exponent `θ = 1/12` fails F1;
- the second branch's coefficient raised by `0.02` fails F4 and F5;
- the floor bin without the row saving fails F4 and F5;
- the release's pieces in place of the `L`-free ones fail F3;
- the sextic `γ₁` in place of `γ₂` fails N1;
- the second branch's constant `1/7` in place of `1/8` fails F2.

## Check 4 and bearing on RH

**Check 4.**
- Acknowledged:
  - the release's low side and its steps (rounds 496, 500, 503);
  - the C₀ wall and the obstruction `13/15` (rounds 498–500);
  - round 500's dyad program;
  - rounds 501–502's lower end in `ℓ`;
  - round 498's readings;
  - Xu–Sang's admissibility conditions;
  - the moment lever's limits (rounds 506–508);
  - `PAIRING.md`'s boundary formula;
  - Liu's `0.874957…` (round 471) and Sang's `0.8748867` (round 496).
- New here:
  - the floor `5/6` and its identity (F1);
  - the closed form of the low side's least value in `σ` (F2);
  - the second branch's trivial dual, and its slot coefficient `γ₂ᾱ²` from the marked reflection (F3);
  - the formula without the `L` term (F3);
  - the bias measured by infinity type (N1);
  - the vertex `(1/3, 1/3, 1/3)` and the two inputs it needs (F4, F5);
  - the readings of `h < 2l_y` and of the small rows' line (F6);
  - the horizon scan's hits: Liu's 2610.26835 and the two new versions of Xu–Sang.

**Bearing on RH: none.** The note proves no zero-free region and gains no constraint on zeros. It maps what one method would need.
