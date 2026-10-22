# The release's exponent system at 5/6

Side-branch note, 2026-10-22, on branch `claude/latest-commit-branch-ik1pj3`. It follows `PAIRING.md` in this directory. It is not a README round, and it adds no Lean. The numbers below come from the gate script `fivesixths.py` (section 6), or are quoted from the sources cited.

**The question.** The owner's goal: "widen the zero free strip to at least 5/6", that is, a zero-free half-plane `Re s > 5/6` for the release's families. This note asks what the release's method, as the pilot models it (README rounds 496–508, `frontier/wall78`), would need to reach `5/6`. It does not reach it. It finds where `5/6` sits in that exponent system and names the two inputs that are missing.

**Summary.**
1. **Horizon scan** (section 0). Nothing found reaches `5/6`. The best recorded boundary is Liu's `B_♭ = 0.874886647…` (arXiv 2610.26835, 19 October, every number field).
2. **5/6 is the floor of the release's low side** (gate F1, exact). Given the Gram bound's range `b ≥ 0` and the compensated probe's `l_x > ℓ`, the low side satisfies `s₀ − 5/6 = (M − 2ℓ)/12 + (Gram excess) + L/2 + μ/2 ≥ (l_x − ℓ)/6 ≥ 0` in every geometry. Equality holds only at `l_x = l_y = ℓ` with no row loss and no crossing *(at round 500's crossing cost `c = 1`; at a smaller cost a crossing is cheaper, and at `c = 0` free: section 8)*. In `PAIRING.md`'s reading, `β_b = 5/6 − ℓ/6 + M/12 + L/2`. There the amplifier's gain `ℓ/6` is exactly what the theta deficit `M/12` takes back once `M ≥ 2ℓ`.
3. **The second branch is a slot sum at a trivial dual** (gates F3, N1).
   - Round 500's second branch is attained at a dyad whose dual is trivial and whose slots are all active. There the completed row is a fixed multiple of `Σ_P a(P)/√q_P`, and Lemma `lem:hybrid-energy` bounds that sum by Cauchy–Schwarz.
   - By the release's marked reflection, `a(P)` is a product, over the active slot primes `q`, of the normalized cubic Gauss sum `γ₂(q)`, the angle `ᾱ(q)²` and finite-order characters.
   - Over the 7827 split primes of norm `≤ 8·10⁴`, of the twists `α^k` with `|k| ≤ 3` only the untwisted sum `Σ γ₂(π)` carries Patterson's main term: `893` against `√n = 88`. Every twist `α^k` with `k ≠ 0` is at square-root size; at `k = −2`, the slot coefficient's twist, the sum is `91`.
4. **The low side's least value** (gate F2, closed form). ~~Let `σ` be the slot sum's exponent: its square is `Z^{σ z_a}`.~~ *(Struck in section 7: `σ` is the parameter of the second branch `(1 + (4σ − 1)ℓ′ − 2M′)/4`, not the exponent of a slot sum at the trivial dual.)* Then the least low side over all geometries is `5/6 + max(0, (2σ − 1)/(6(4σ + 1)))`:
   - `13/15` at the release's `σ = 1`;
   - `28/33` at `σ = 2/3`, ~~the size of the cubic large sieve's `(NL)^{2/3}` term at a trivial dual~~ *(section 7: the hybrid bound with the `L` term dropped at every dual length)*;
   - exactly `5/6` for every `σ ≤ 1/2`.
5. **The whole exponent system at 5/6** (gates F4, F5, F6). Take round 499's program with round 500's crossing cost, Xu–Sang's admissibility rows and round 498's readings. Add four more:
   - no numerator rotation, which makes Xu–Sang's `h < 2l_y` idle;
   - the third Gram term carried in the low side's maximum;
   - the small rows' `z`-line near `1/6`;
   - a uniform row-sum saving `U^η` on every bin.

   With all of these, the boundary is `5/6`, at the vertex `l_x = l_y = ℓ = 1/3`, provided `σ ≤ 1/2` and `η ≥ 0.168`; Xu–Sang's own counts and fourth moment need `η ≥ 0.178`. At `σ = 2/3` the same system gives `28/33`.
6. **What is missing.** Two estimates, neither in the sources read here *(section 8: with round 500's crossing cost; a cheaper crossing of the slice is a third route)*:
   - ~~the release's trivial-dual slot sums with `σ ≤ 1/2`, that is, angle-twisted cubic Gauss sums over primes below `X^{3/4}`;~~ *(struck in section 7: such sums, at square-root size in every column, give only `σ = 5/8` and `71/84`; `σ ≤ 1/2` needs a square-root cubic large sieve `N + (NL)^{1/2}` for the slot coefficients;)* *(Section 9: "at square-root size" is wrong there. The `5/8` row is squared slot sums `≪ L^{1/2}` in every column, that is slot sums `≪ L^{3/4}`; square-root cancellation in every column gives `5/6`. And `σ = 1/2` also follows from the weaker `N + N^{3/4}L^{1/2}`.)*
   - a saving `U^{1/6}` on the high side's sums over the Poisson rows near `a = 1/2`, where the C₀ wall sits.

   The register gets both as targets (section 5). This note does not prove either, and so does not prove `Re s > 5/6`.
7. **Follow-up (section 7, gate script `slotsplit.py`).**
   - The literature: Heath-Brown's twisted bound `X^{5/6+ε} + |l|X^{3/4+ε}`, and Dunn–Radziwiłł's proof, under GRH, that the cubic large sieve's `(AB)^{2/3}` term is sharp.
   - A slot-split bound from the release's own pair phase: `σ = 3/4`, least low side `41/48` (S1, S2). *(Superseded the same day: the trilinear split gives `σ = 2/3`, least low side `28/33`; section 9.1, gate S8.)*
   - The dictionary between hybrid bounds and `σ`, which corrects items 4 and 6 (S5). *(Its labels are corrected in section 9.5.)*
   - With the release's inputs and no row saving, the boundary stays `0.8748866` at every `σ` (S3).
   - At the vertex, every bin with `δ < 1/2` needs a saving beyond what density-hypothesis counts give (S4).
   - The goal is still not reached.
8. **The crossing cost (section 8, gate S6).**
   - Round 500's first branch charges a crossing of the slice `M + ℓ = 1` at cost `c = 1`.
   - In the model, with the slot-split's `σ = 3/4` and no row saving, `c = 0.15`, `0.1` and `0.05` give `0.8725510`, `0.8615362` and `0.8486654`. *(The same at the trilinear `σ = 2/3`: S6, section 9.)*
   - ~~`c = 0` gives `5/6` on the ray `l_x = l_y = ℓ ≥ 1/2`, with neither T1 nor T2.~~ *(False as written: on that ray the bins `E` bind below `t ≈ 0.5572`, and at `t = 1/2` the boundary is `0.8786610`. `c = 0` gives `5/6` on the ray for `t ≥ 0.5572`, still with neither T1 nor T2: S6, section 9.)*
   - These geometries lie far across the slice, where the release's lemmas were not re-derived.
9. **The trilinear split and the review of sections 7–8 (section 9, gate S8).**
   - A hostile review found that the trilinear split's character is `conj((B/jA)_3)`, with a squarefree modulus. Heath-Brown's sieve then gives `N + (NL)^{2/3}`: `σ = 2/3`, least low side `28/33`, by a written argument checked against the release's lines (9.1). Alone it moves nothing: the boundary stays `0.8748866` (S3).
   - The slot coefficient is the composite cubic Gauss sum `γ₂(P)`, angle-twisted: the release's one-prime scalar `τ⁺_{q,2}` and its pair phases combine by the Chinese remainder theorem (9.2, S8).
   - Dunn and Radziwiłł's corrected sieve assumes, for prime-supported coefficients, input of GRH strength: circular here (9.2).
   - The review's other findings are swept (9.4). The goal is still not reached.
10. **A horizon hit (section 10).** OpenAI's "An unconditional first moment for cubic Gauss sums" (September 25), cited but not used by the release, proves Patterson's first moment and its fixed angular twists without GRH. For the slot coefficients it bears on the trivial dual, which does not move `σ`. Its power-saving Proposition `prop:dual` for prime convolutions is recorded as a T1 attack note.

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

**The exponent `σ`.** ~~Write the slot sum's square as `Z^{σ z_a}`.~~ *(Struck in section 7. A bound at the trivial dual alone does not move the dyads' maximum: dyads with a short dual have nearly the same energy. Below, `σ` is the parameter of the second branch `(1 + (4σ − 1)ℓ′ − 2M′)/4`; section 7's dictionary says which hybrid bound gives which `σ`.)*
- The release's bound is `σ = 1`.
- `σ = 2/3` ~~is the cubic large sieve's `(NL)^{2/3}` term at a trivial dual (`N = 1`)~~ *(section 7: is the hybrid bound `N + (NL)^{2/3}`, the `L` term dropped at every dual length, which gate F3 computes)*. The release quotes that sieve from Heath-Brown: "`\{U+V+(UV)^{2/3}\}`". Its `(NL)^{2/3}` term is also the size of Patterson's main term, which the theta-aligned coefficients (`k = 0`) attain.

With the cubic sieve's `L` term dropped for these coefficients, the dyad program's maximum becomes `M′ + max(0, M′ + ℓ′ − 1, (1 + 5ℓ′/3 − 2M′)/4)`. **Gate F3** checks this at 300 random `(M′, ℓ′)` with `ℓ′ ≤ 0.36`; above `ℓ′ ≈ 0.4` another branch appears, which this note does not need. In general the second branch becomes `(1 + (4σ − 1)ℓ′ − 2M′)/4`. *(Section 7: this is the parametrization used below; it does not follow from a bound at the trivial dual.)*

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

So the release's low side reaches its floor only with `σ ≤ 1/2`. ~~That means slot sums of angle-twisted cubic Gauss sums over primes of size `X^{3/4}` or less.~~ *(Struck in section 7: such slot sums in every column give `σ = 5/8` and `71/84`; `σ = 1/2` is a square-root sieve `N + (NL)^{1/2}` for the slot coefficients, gate S5 of `slotsplit.py`.)* *(Section 9: `σ = 1/2` also follows from `N + N^{3/4}L^{1/2}`, S5 (c).)* N1 suggests that the slot coefficient's prime sums are near square-root size. The obstacle is the method's bound, not a main term. *(Section 7: beating `(NL)^{2/3}` has to use the coefficients themselves; Dunn and Radziwiłł show that the term is sharp for general coefficients under GRH.)*

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

Within this exponent system, the half-plane `Re s > 5/6` needs both of *(section 8: this assumes round 500's crossing cost `c = 1`; a cheaper crossing is a third route)*:

1. **~~The slot sums at a trivial dual with `σ ≤ 1/2`.~~ A square-root sieve for the slot coefficients (`σ ≤ 1/2`)** *(corrected in section 7)*.
   - ~~The target: `|Σ_P a(P)/√q_P|² ≪ Z^{z_a/2 + ε}` for the release's slot coefficients, which are products of `γ₂(q)ᾱ(q)²` and finite-order factors over the slot primes.~~
   - ~~In one slot, that is `Σ_{q ∼ P} γ₂(q)ᾱ(q)²ψ(q) ≪ P^{3/4 + ε}` over primes. The sources read on this branch bound such sums only through the cubic large sieve, whose `(NL)^{2/3}` term gives `σ = 2/3` and the floor `28/33`.~~
   - *(Section 7: the target is `Σ_{j∼N}|Σ_P a(P)χ_P(j)^{−2}/√q_P|² ≪ Z^ε(N + (NL)^{1/2})` at every dual length `N`, for the release's slot coefficients, which are products of `γ₂(q)ᾱ(q)²` and finite-order factors over the slot primes, times the mark–mark phases. A bound at the trivial dual alone gives nothing, and square-root slot sums in every column give `71/84`.)* *(Section 9: `N + N^{3/4}L^{1/2}` suffices, and only `N < L²` matters, since for `N ≥ L²` the release's factor is already `≪ N`. The `71/84` row is squared slot sums `≪ L^{1/2}`, not square-root size.)*
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
- The statement that the sources read bound the slot sums only through the cubic large sieve is scoped to the release, Xu–Sang's v2 and the notes on this branch. The literature on prime sums of cubic Gauss sums was not surveyed, so no claim is made about what it contains. *(Section 7: surveyed since, in Heath-Brown 2000 and Dunn–Radziwiłł 2024.)*

**Check 9 (b), register.** STRUCTURAL-REVIEW §6, the sub-entry "Below `7/8` in the release's exponent comparison", gets a bullet "The release's exponent system at `5/6`" with two targets.
- **T1, ~~trivial-dual slot sums with `σ ≤ 1/2`~~ a square-root sieve for the slot coefficients, `σ ≤ 1/2`** *(corrected in section 7)*.
  - Socket: the `L` term of Lemma `lem:hybrid-energy` inside the second branch of Lemma `lem:probe-row-norm`, which is `fivesixths.py`'s gate F3.
  - Attack notes:
    1. a corrected cubic large sieve, in the sense of Dunn–Radziwiłł's Proposition 9.1, for angle-twisted Gauss-sum coefficients, which do not attain the `(NL)^{2/3}` term *(section 9.2: that proposition assumes their axiom (3.2), which for prime-supported coefficients is of GRH strength: circular here as stated)*;
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
  - the literature on cubic Gauss sums over primes *(section 7: surveyed since)*;
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

## 7. Follow-up: the literature, the slot product split in two, and what `σ` means

Same day, same branch. The gate script is `slotsplit.py` (gates S1–S5; with sections 8 and 9, S1–S8, about 70 s; `python3 slotsplit.py`). Every number is a statement about the pilot's model of the release's exponent system, as in sections 1–5.

### 7.1 The literature on T1

Surveyed on 2026-10-22 by web search. Two sources were read: Heath-Brown's abstract in the Oxford ORA record, and Dunn and Radziwiłł's arXiv text (2109.07463v3), whose quotes below are from its PDF text with the extraction's symbol damage repaired.
- **Heath-Brown, "Kummer's conjecture for cubic Gauss sums" (2000).** For the sum over the integers `c ≡ 1 (mod 3)` of `ℚ(√−3)` with `N(c) ≤ X` of `g̃(c)Λ(c)(c/|c|)^l`, the abstract gives `≪_ε X^{5/6+ε} + |l|X^{3/4+ε}`, and adds: "When $l=0$ it is conjectured that the above sum is asymptotically of order $X^{5/6}$, so that the upper bound is essentially best possible." For `l ≠ 0`, which includes the slot coefficient's angle `ᾱ²`, the bound is still `X^{5/6+ε}`. The `X^{3/4}` term is the angle's cost, not a bound for the sum.
- **Dunn and Radziwiłł, "Bias in cubic Gauss sums: Patterson's conjecture".**
  - Under GRH, Theorem 1.1 gives Patterson's asymptotic, and Theorem 1.3 gives `o(X^{5/6}/log X)` for the powers `g̃(ϖ)^k`, uniformly in `1 < |k| ≤ X^{1/100}`. Neither saves a power of `X` below `5/6`.
  - The abstract: "we show that Heath-Brown's cubic large sieve is sharp up to factors of $X^{o(1)}$ under the Generalized Riemann Hypothesis".
  - Their corrected sieve, eq. (1.13), allows them "to beat the exponent $(AB)^{2/3}$, albeit only for sequences that have substantial cancellations against all non-principal cubic characters", with a small fixed saving `δ`.
- **For T2 (found by search, not read; as the search results summarize them):** ~~ratios conjectures over cubic families have been proved with one shift by multiple Dirichlet series, under GRH: Gao and Zhao, arXiv 2311.08626 (cubic Hecke `L`-functions of prime moduli over the Eisenstein field), and Čech, arXiv 2110.04409 (real characters).~~ *(Section 9: misfiled, since Čech's family is not cubic. From the two abstracts, read since: Gao and Zhao develop the ratios conjecture with one shift "for the family of cubic Hecke $L$-functions of prime moduli over the Eisenstein field using multiple Dirichlet series under the generalized Riemann hypothesis"; Čech considers "the family of real Dirichlet characters", and "All of the results are conditional under the Generalized Riemann hypothesis.")* Here GRH for the rows' family is stronger than the conclusion sought, so those results are not usable as stated.

### 7.2 What `σ` means (gate S5)

Section 2 called `σ` the exponent of the slot sum at the trivial dual. That is false. A bound at the trivial dual alone does not move the dyads' maximum, because dyads with a short dual have nearly the same energy.

What the second branch `(1 + (4σ − 1)ℓ′ − 2M′)/4` needs is a hybrid bound for `Σ_{j∼N} |Σ_P a(P)χ_P(j)^{−2}/√q_P|²`, at every dual length `N`. Gate S5 replaces the release's factor in round 500's dyad program by each bound below. *(Section 9: S5 then covered the table's last three rows, and "never exceeds" is checked at S1's points, `ℓ′ ≤ 0.36`; only the dual lengths `N < L²` matter. The corrected table is in 9.5.)* For each it checks three things:
- the program never exceeds the second branch with the `σ` shown;
- it equals that branch at the low side's optimum;
- the least low side agrees between F2's linear program and the exact program on a grid.

| hybrid bound | `σ` | least low side |
|---|---|---|
| the release's `N + L + (NL)^{2/3}` | `1` | `13/15` |
| the slot-split bound, `min(·, N L^{2/3})` (section 7.3) | `3/4` | `41/48` |
| ~~every column's slot sum at square-root size~~ *(mislabelled: every column's squared slot sum `≪ L^{1/2}`, section 9.5)*, `min(·, N L^{1/2})` | `5/8` | `71/84` |
| the `L` term dropped, `N + (NL)^{2/3}` | `2/3` | `28/33` |
| a square-root sieve, `N + (NL)^{1/2}` | `1/2` | `5/6` |

~~So the low side's floor needs a square-root cubic large sieve for the slot coefficients. Slot sums at square-root size in every column (prime sums `≪ X^{3/4}`, beyond Heath-Brown's `X^{5/6}`) would give only `71/84`.~~ *(Struck in section 9, false as written. `σ = 1/2` follows from the weaker `N + N^{3/4}L^{1/2}` (S5 (c)). The `71/84` row is squared slot sums `≪ L^{1/2}`, that is slot sums `≪ L^{3/4}`, not square-root size; square-root cancellation in every column gives `5/6` (S5 (e)). And the slot sums are not products of prime sums: the pair phases couple the slots.)* Dunn and Radziwiłł's sharpness result says `(AB)^{2/3}` cannot be improved for general coefficients (their lower bound assumes GRH). A bound `N + (NL)^{1/2}` therefore has to use the coefficients themselves: the angle `ᾱ²`, which removes Patterson's main term at the primes measured (N1), and the slots' product structure.

### 7.3 The slot-split bound (gates S1, S2)

The release keeps the slot coefficients' structure up to the norm step:
- "The physical slot sets remain disjoint and their separated coefficients are product-form." (paper.tex lines 8204–8205).
- Its eq. `reflection-pair-phase` (lines 7443–7449): "`For distinct active good primes \(p,q\), Equation~\eqref{eq:reflection-cross-prime-phase} and cubic reciprocity give`" `\chi_p(q)^{2j_p+2}\chi_q(p)^{2j_q+2} =\left(\frac qp\right)_3^{j_p+j_q+2}`, and "`For an active mark the exponent is \(j_q=0\)`". So two active marks carry `(q/p)_3^2`.
- "Row-row phases are row scalars, mark-mark phases are tuple scalars, and their interactions with frozen primes depend on only one of those sets." (lines 7464–7466). "The angular conductor scalar factors in the same way."
- It then gives the structure up: "`The function \(a\) need not retain product form at this norm step.`" (lines 7966–7967).
- Its slots: "`Choose a fixed even integer \(K\) with`" `\ell_i=\frac{\ell}{K}\quad(1\le i\le K)` (lines 16246–16250).

**The bound.** In the proof of Lemma `lem:hybrid-energy`, each column `j` meets the inner sum `Σ_{P′} a_{D,r}(P′)q_{P′}^{−1/2}χ_{P′}(j)^{−2}1_{(P′,ht)=1}`. The release bounds the sum of its squares over the columns by its eq. `cubic-large-sieve` (lines 7491–7497), giving the factor `N/r_0 + L/D_0 + (NL/(r_0D_0))^{2/3}` (lines 7632–7640).

Split the active slots that remain after the Möbius divisor `D` into two halves of nearly equal length, `P′ = AB`. For a fixed column, the column character, the divisor's phases, `χ_{P′}(r)^{−2}`, the class characters modulo `M_ref²` and the coprimality masks are one-prime factors. The mark–mark phases across the halves multiply to `(B/A)_3^2`. So the inner sum is `Σ_{A,B} x_j(A)y_j(B)·conj((B/A)_3)`. The same cubic sieve in `(A, B)` bounds its square by `(L_A + L_B + (L_AL_B)^{2/3})Z^ε‖x_j‖²‖y_j‖²`, about `(L/D_0)^{2/3}` for balanced halves.

Summed over the `≪ N/r_0` columns, the factor may be replaced by its minimum with `(N/r_0)(L/D_0)^{2/3}Z^{O(ℓ/K)}`. That bound also increases when `D_0, r_0` are replaced by `1`. When fewer than two active slots remain, the release's factor is kept, and then `L/D_0 ≤ Z^{ℓ/K}`. With `K` large, the lemma's factor becomes `min{N + L + (NL)^{2/3}, N L^{2/3}}`. In the energy of Lemma `lem:reflected-energy`, `u = min{v, z_a, (v + z_a)/3}` becomes `max{u, z_a/3}`.

**What it gives.**
- **S1:** the dyads' maximum is `M′ + max(0, M′ + ℓ′ − 1, (1 + 2ℓ′ − 2M′)/4)`.
  - It holds as an upper bound everywhere sampled, with equality when `M′ ≥ 1/2 − ℓ′/3 + 1/100`.
  - At `(2/3, 1/3)` the excess is `1/12`, against the release's `1/6`, and the maximum moves from the trivial dual to `v = z_a/3`.
- **S2:** the least low side is `41/48 = 0.8541667`, at `(l_x, l_y, ℓ) = (1/4, 1/2, 1/4)`, against the release's `13/15`. *(Section 9: at `(M, ℓ) = (3/4, 1/4)` the low side is the same for every `l_x ∈ [1/4, 3/8]`. Xu–Sang's `l_y − ℓ > 11b/6` fails at the point named and holds for `l_x > 21/64`: S2.)*

**Scope.** This is a written argument checked against the release's text at the lines cited. It has not been refereed or formalized. *(Superseded the same day by the trilinear split, `σ = 2/3`: section 9.1.)*

### 7.4 The ladder (gate S3)

The release's unconditional inputs here are Xu–Sang's counts and fourth moment, the readings of section 3, and Sang's rotation. With them, the boundary is `0.8748866` at `σ = 1`, `3/4` and `1/2` alike *(and at `2/3`: S3, section 9)*. The walls are the bins `δ ≥ 1/8` ("`E`") and the low side without row loss. So the slot-split bound does not move the release's boundary by itself.

With a uniform row saving `U^{1/10}`, no rotation and the small rows' line at `1/6 + 1/100`:
- `13/15` at `σ = 1`;
- `41/48` at `σ = 3/4`;
- *(section 9)* `0.8537843` at `σ = 2/3`, with the bins `E` binding.

### 7.5 The vertex's bins (gate S4)

At `(1/3, 1/3, 1/3)`, with density-hypothesis counts `R = 1 − δ`, Lindelöf and no rotation, the bins at `x = 1/2` have endpoint `1 − δ/3 − s₀` (exact). So `s₀ = 5/6` needs a saving of at least `1/6 − δ/3` on every bin with `δ < 1/2`. That is more than those counts give: either counts below `5/6 − 2δ/3` or cancellation among the rows.

In the program, savings `U^{3/10}` on the floor bin and the small bins alone stop at `31/36`, with the bins `E` binding. `U^{1/5}` on every bin gives `5/6`.

### 7.6 The targets, corrected

- **T1** (`σ ≤ 1/2`): the square-root sieve `Σ_{j∼N}|Σ_P a(P)χ_P(j)^{−2}/√q_P|² ≪ Z^ε(N + (NL)^{1/2})` for the release's slot coefficients, at every dual length. *(Section 9: `N + N^{3/4}L^{1/2}` suffices, and only `N < L²` matters; 9.5 restates T1.)*
  - Socket: unchanged (F3's `L` term), widened to the `(NL)^{2/3}` term.
  - Known here: `σ = 3/4` by the slot-split bound (7.3). *(Now `σ = 2/3`, by the trilinear split of section 9.1.)*
  - Attack notes:
    1. ~~a trilinear split that treats `(j, A)` as one modulus. With `B`'s character `(B/jA²)_3` it needs a cubic large sieve over cube-free moduli. If it held with the plain sieve's shape, it would drop the `L` term, giving `σ = 2/3` and `28/33`.~~ *(Struck in section 9, false as written: `B`'s character is `conj((B/jA)_3)`, whose modulus `jA` is squarefree, so the plain sieve applies, and the split gives `σ = 2/3` and `28/33`: section 9.1, gate S8.)*
    2. Dunn–Radziwiłł's corrected sieve for the angle-twisted coefficients: by eq. (1.13), a small power below `(NL)^{2/3}`. *(Section 9.2: its Proposition 9.1 assumes their axiom (3.2), of GRH strength for prime-supported coefficients: circular here as stated.)*
    3. slots over squarefree or rough integers, where Patterson's Kubota series bounds the twisted sums at `X^{3/4}` by its functional equation. The compensation and the high side's prime-factor moments would have to be redone.
  - ~~In every source surveyed (7.1), the `(NL)^{2/3}` term is sharp for general coefficients, and no bound below `X^{5/6}` is proved for prime sums of twisted cubic Gauss sums, even under GRH.~~ *(Struck in section 9, false as written. Heath-Brown's abstract, the only text of his read, says nothing on that term, and Dunn and Radziwiłł quote him: "It seems possible that the term (AB)^{2/3} could be removed with further effort". Their own lower bound, under GRH, shows the term sharp for general coefficients. Their Theorem 1.3 gives `o(X^{5/6}/log X)` under GRH: below `X^{5/6}`, though not by a power. No power saving below `X^{5/6}` was found in the two sources read.)*
- **T2:** on the high side at the vertex, a saving `U^{max(0, 1/6 − δ/3)}` on every bin with `δ < 1/2`, beyond what density-hypothesis counts give, and `U^{1/6}` plus the floor bin's half-width on the floor bin.
  - The saving can come from counts below `5/6 − 2δ/3` or from cancellation among the rows.
  - The floor bin holds the generic rows (`R = 1`), so there, in this model, the saving can only come from cancellation among them.
  - ~~Ratio averages over cubic families are proved by multiple Dirichlet series only under GRH (7.1).~~ *(Struck in section 9: unscoped, and Čech's family is real characters. The two papers found prove their ratios results under GRH, by their abstracts.)*

**Check 9.**
- (a) Scope: "surveyed" means the two sources read in 7.1; the ratios papers were found, not read. "Needs" is relative to the hybrid bounds of S5 and the configurations of S3–S4.
- (b) The register entry is corrected with strikes and markers.
- (c) The signals are unchanged: T1 and T2 are auxiliary inputs.

**Outcome.** The goal `Re s > 5/6` is still not reached, and no new zero-free region is proved. This section adds:
- an improvement of the release's second branch from `σ = 1` to `σ = 3/4`, by the written argument of 7.3, which alone does not move the boundary *(to `σ = 2/3` by section 9.1's trilinear split, which alone does not move it either)*;
- a correction of what `σ = 1/2` requires;
- the finding that the vertex's high side needs more than density-hypothesis counts give.

## 8. The crossing cost, a third lever

Same day. Gates S6 and S7 of `slotsplit.py`.

**What it is.** Round 500 derived the crossing cost from the release's proof of Lemma `lem:probe-row-norm`. Crossing the slice `M + ℓ = 1` by `μ` costs `μ/2` on the low side (`c = 1`). The cost is the first branch `M′ + ℓ′ − 1` of the dyads' maximum: the column term `NB` of the factor `K + NB` in Lemma `lem:hybrid-energy`, where the dual is longer than the rows.

The release states the slice in two places only:
- in that proof: "Since $M'+\ell'-1=-3d$, direct subtraction gives" (paper.tex line 8246);
- at its fixed geometry: "M=l_x+l_y=\frac56,\qquad M+\ell=1." (line 6864).

**What a cheaper crossing would give** (S6). The settings are: `σ = 3/4` (the slot-split bound), no row saving, Sang's rotation, round 502's reading that drops `l_y < 1/2`, and the program's cap on `μ` raised from `1/2` to `2`. Both of the last two matter. *(Section 9: S6 now runs at the trilinear `σ = 2/3`, with the same numbers. The settings also include round 498's readings, which matter too: without them `c = 0` gives `0.8700000`, with the principal edge binding, S6.)* In session runs, keeping `l_y < 1/2` gives `0.8504534` at `c = 0`, and keeping the cap at `1/2` gives `0.8436087`. Round 502 found `l_y < 1/2` used only for a slope bound, which holds for `l_y < 1` (its gate F3).

| crossing cost `c` | boundary |
|---|---|
| `1` (the release) | `0.8748866` |
| `0.15` | `0.8725510` |
| `0.1` | `0.8615362` |
| `0.05` | `0.8486654` |
| `0` | `5/6` |

At `c = 0` the low side reaches its floor on the ray `l_x = l_y = ℓ = t`:
- the second branch at `σ = 3/4` is `(1 − 2t)/4`, which is `≤ 0` for `t ≥ 1/2`;
- the C₀ wall `4/3 − t` is at most `5/6` there.

The optimum found is `t = 0.5572`, with `M + ℓ = 1.67`; the bins `E` bind as well. *(Section 9: the two bullets hold for `t ≥ 1/2`, but the bins `E` hold only from `t ≈ 0.5572` on. On the ray at `κ = 3/4` the boundary is `0.8786610` at `t = 1/2` and `0.8390211` at `t = 0.55`, both with `E` binding, and `5/6` at `t = 0.56` (S6). So `c = 0` reaches `5/6` on the ray for `t ≥ 0.5572` only.)* With the release's `σ = 1`, the second branch `(1 − t)/4` vanishes only at `t = 1`, and `c = 0` gives `5/6` at `(1, 1, 1)` *(section 9: the corner of the model's length box `[0, 1]³`, which has no source in the release's Definition `def:stage-high-data`, and only with `μ = 2`, the raised cap; with the cap at `1.9` the program gives `0.8350000`, S6)*. So in this model a free crossing reaches `5/6` with neither T1 nor T2, ~~and a cost above about `0.16` buys nothing (round 499's break-even)~~ *(struck in section 9: in S6's configuration `c = 0.16` gives `0.8744704` and `c = 0.165` gives `0.8748866`, the release's value, so the break-even lies between them; `0.16` was round 499's configuration)*.

**`c = 0` is exactly T3** (gate S7). Replace the quadratic sieve's factor `K + NB` by `K` in round 500's dyad program. Then its maximum has no first branch: it is `M′ + max(0, (1 + 3ℓ′ − 2M′)/4)` at 300 random `(M′, ℓ′)` in `[0.3, 2] × [0, 1]`, and at most `M′ + max(0, (1 + 2ℓ′ − 2M′)/4)` with the slot split. So removing the column term leaves no further branch in the dyads, and the program's `c = 0` is that removal. (With the column term, the maximum on the ray `(2t, t)` is the first branch `3t − 1` for `t ≥ 0.4`. The other branch that F3 avoided above `ℓ′ ≈ 0.4` also comes from the column term: in a session run, its maximizing dyads have a dual longer than the rows, `v > H`. It disappears with the column term.) Keeping the column term in S7's check fails it, in a session run.

**Scope.** Far across the slice, the model's admissibility rests on Xu–Sang's conditions and on the pilot's high side extended there. The release's lemmas are stated for its fixed geometry and were not re-derived at `M + ℓ ≈ 1.7`. Round 496 lists what the model leaves out: "the intermediate range, small and large rows, the frequency extension, and the prime supply against the capacities". The numbers for small `c` are statements about the model, not about the release's argument there.

**Target T3: the column term.** At round 500's first-branch dyad (`O = 0`, `H = M′`, `z_a = ℓ′`, `v = T`), the squarefree dual has length `T = 2M′ + ℓ′ − 1`, longer than the rows' `H = M′`. The quadratic large sieve then charges `K + N ≈ N`.
- The target: a bound `Σ_{k∼K}|Σ_{n∼N} γ(n)χ_k(n)³|² ≪ Z^ε K Σ|γ(n)|²` for `N > K`, for the release's dual coefficients `γ` (the reflection's coefficients times the slot sums). That would make `c = 0`.
- The quadratic large sieve's column term is attained by a coefficient aligned with one row's character. So for general coefficients `N` cannot be improved, and such a bound has to use the coefficients themselves. For coefficients with independent random phases the expected size is `K Σ|γ|²`, with no column term.
- Attack note: a corrected quadratic large sieve, in the sense of Dunn–Radziwiłł's eq. (1.13), for the reflection's metaplectic coefficients twisted by the slot sums.
- Signals (Check 9(c)): auxiliary, like T1.

**Outcome.** The goal is still not reached. The routes to `5/6` in the model are now three:
- T1 and T2 at the vertex `(1/3, 1/3, 1/3)` (sections 4 and 7);
- T3 alone across the slice, with the slot-split bound (this section);
- combinations of partial inputs. For example, `c = 0.05` with a row saving `U^{1/20}` gives `0.8442662` (a session run of S6's program without rotation, with the small rows' line at `1/6 + 1/100`).

Each needs a bound that beats a large sieve that is sharp for general coefficients.

## 9. The trilinear split, the slot coefficient as a Gauss sum, and the review of sections 7–8

Same day. Gate S8 of `slotsplit.py` is new, and gates S2–S7 are extended. A fresh-context hostile review of sections 7–8 and `slotsplit.py` returned one major finding, six minor and ten cosmetic. Each was checked directly before it was accepted (9.4). Every number is a statement about the pilot's model of the release's exponent system, as in sections 1–8.

### 9.1 The trilinear bound: `σ = 2/3`

Section 7.6's first attack note gave `B`'s character in a trilinear split as `(B/jA²)_3`, and concluded that the split needs a cubic large sieve over cube-free moduli. That is false. In column `j`:
- the half `B` carries its column factor `χ_B(j)^{−2}` (paper.tex line 1792), and the release has "`for a good prime $p\notin S$, one has $(x/p)_3=\chi_p(x)^2$`" (lines 1905–1906), so the factor is `conj((j/B)_3)`;
- the mark–mark phases across the halves multiply to `conj((B/A)_3)` (section 7.3);
- cubic reciprocity turns their product into `conj((B/jA)_3)`. The modulus `jA` is squarefree, because the factor `conj((j/A)_3)` vanishes unless `(j, A) = 1`.

**The bound.** For fixed `h, t, D, r`, the release's proof of Lemma `lem:hybrid-energy` notes that "`the \(P'\)-coefficients are independent of \(j=c'm\)`" (lines 7622–7623), and it sums over the columns with "`Cubic reciprocity, conjugation, and Equation~\eqref{eq:cubic-large-sieve}`" (lines 7632–7633). Write column `j`'s inner sum as `Σ_A x(A)conj((j/A)_3)·Σ_B y(B)conj((B/jA)_3)`, where `x` and `y` carry each half's one-prime factors and inner phases.
1. Cauchy–Schwarz in `A` costs `Σ_A|x(A)|²`, which is `≪ Z^ε` by the release's ideal count (line 7623).
2. The rows `m = jA` have norm up to about `N L_A`, and each occurs at most `d(m)` times. The release's eq. `cubic-large-sieve`, "`where both stars mean squarefree in \(\mathcal O\), and the coefficients are arbitrary complex numbers`" (lines 7491–7499), bounds the sum over the columns by `Z^ε(N L_A + L_B + (NL)^{2/3})`.
3. The slots have one scale: "`Put \(P_i=P=Z^{\ell/K}\).`" (line 16253). So when `L > N`, `L_A` can be chosen within a factor `Z^{ℓ/K}` of `(L/N)^{1/2}`; when `L ≤ N`, take `L_A = 1`. Either way the bound is `Z^{ε + O(ℓ/K)}(N + (NL)^{2/3})`. Like the release's, it increases when `D_0, r_0` are replaced by `1`.

That is the factor with the `L` term dropped: the second branch at `σ = 2/3`, and the least low side `28/33` (S5's row (b)). Gate F3 of `fivesixths.py` checks the dyads' maximum `M′ + max(0, M′ + ℓ′ − 1, (1 + 5ℓ′/3 − 2M′)/4)`. The bound supersedes the slot split's `σ = 3/4`.

**Gate S8** checks the ingredients directly in `Z[ω]`, with cubic residue symbols computed by Euler's criterion:
- (i) at 2000 random triples of split primes of norm below `4000`, cubic reciprocity holds, and the half's character equals `conj((B/jA)_3)` at every triple. The struck `jA²` form agrees at 674, about a third, as chance predicts. With the column factor unconjugated (a session sabotage run), the identity holds at 673 and the gate fails.
- (iii) `min_a max(v + az, (1 − a)z, 2(v + z)/3) = max(v, 2(v + z)/3)` on a grid, and a split in eighths of the slots costs at most `z/8`.

**What it moves.**
- With the release's inputs and no row saving: nothing. The boundary stays `0.8748866` at `σ = 2/3` (S3).
- With a uniform row saving `U^{1/10}`, no rotation and the small rows' line at `1/6 + 1/100`: `0.8537843`, with the bins `E` binding, against `41/48 = 0.8541667` at `σ = 3/4` (S3).
- Section 8's crossing-cost table is unchanged at `σ = 2/3` (S6).

**Scope.** A written argument checked against the release's lines, at the rigour of section 7.3. It has not been refereed or formalized.

### 9.2 The slot coefficient is a composite Gauss sum

For an active mark the release gives "`\(-\omega_{q,0}=\tau_{q,2}^{+}\chi_q(\epsilon_q)^{-2}\)`" (line 7429). Its eq. `reflection-cross-prime-phase` gives `\chi_p(\sigma_p)^{-2}\omega_{p,j} =\xi_{p,j}\chi_p(c/p)^{2j+2}`, with "`a scalar $\xi_{p,j}$ of absolute value one, depending on $p,j$ but on no other active prime`" (lines 2269–2273). Over the active marks of `P`:
- the one-prime parts multiply to `Π_q τ⁺_{q,2}`, times finite-order factors;
- the cross parts multiply to the pair phases `χ_p(q)²χ_q(p)²` (eq. `reflection-pair-phase` at `j_p = j_q = 0`).

By the Chinese remainder theorem, `τ_{c₁c₂,2} = χ_{c₁}(c₂)²χ_{c₂}(c₁)²τ_{c₁,2}τ_{c₂,2}` for coprime `c₁, c₂`. So the tuple's Gauss-sum part is `γ₂(P)`, the release's "`\gamma_j(c)=q_c^{-1/2}\sum_{v\bmod c}\chi_c(v)^j e(v/c),`" (line 642) at the composite modulus `P`. With the angle, which is multiplicative,

`a(P) = γ₂(P)ᾱ(P)²ψ(P)ΠW_i`, with `ψ` of finite order (the fixed elements' characters and the target's `η̄`).

In column `j`, `γ₂(P)χ_P(j)^{−2} = γ₂(j; P) := q_P^{−1/2}Σ_v χ_P(v)²e(jv/P)` when `(j, P) = 1`. So each column's slot sum is `Σ_P γ₂(j; P)ᾱ(P)²ψ(P)ΠW_i/√q_P`: shifted cubic Gauss sums, twisted by an angle, over the products of one prime from each active slot.

**Gate S8(ii)** checks the CRT identity at 25 random pairs of split primes of norm below `400`, by summing over `Z[ω]/pq` directly. The error is `1.6·10⁻¹⁵`; with the conjugate phase it is at least `1.73`. Gate N3 (9.3) measures these sums with `α^k` in place of `ᾱ²ψ`.

**Dunn and Radziwiłł's corrected sieve, as stated, is circular here (Check 9(c)).**
- Their eq. (1.13) is stated for sequences of this shape, `β_b g̃(b)`. It lets them "beat the exponent $(AB)^{2/3}$, albeit only for sequences that have substantial cancellations against all non-principal cubic characters".
- Its precise form, Proposition 9.1, assumes `β ∈ C_η(B, w)` with `0 < η ≤ 1/4`. Their Definition 3.1 makes this an axiom, eq. (3.2): square-root cancellation `(A/N(u))^{1/2+η+ε}` against every angle `(a/|a|)^ℓ`, every `N(a)^{it}` and every cubic character `(k/a)_3`, the trivial ones aside.
- They add: "The Generalized Riemann Hypothesis is used to show that axiom (3.2) above holds for sequences of interest to us".
- For `β` supported on products of slot primes, the axiom asks for prime sums of Hecke characters over `ℚ(ω)` that cancel down to `P^{1/2+η}` in every slot. For the cubic characters among them, which belong to the release's own family, that amounts to a zero-free region `Re s > 1/2 + η`: more than the conclusion `5/6` sought.

The register records the route with this signal.

### 9.3 The coefficient models (gates N2, N3 of `columnterm.py`)

Commits `19f70fbc` and `ffb66062`, the same day. Both gates measure models of the coefficients at small norms. They are evidence about those models, not bounds.

**The theta term in the columns (N3).** Let `R_k = Σ_j|Σ_P γ₂(P)α(P)^kχ_P(j)^{−2}|²/(#columns·Σ|coefficient|²)`, over the squarefree `P` of norm in `(L/2, L]` and the squarefree columns `j` of norm `≤ N`, with `χ_P(j)^{−2} = conj((j/P)_3)`.
- On average over the columns, the untwisted sum carries Patterson's theta term. As `(L, N)` doubles from `(2·10⁴, 500)` at `L/N = 40`, `R_0 = 7.09, 8.56, 10.86`. That is about `2^{1/3}` per doubling, the growth of `(NL)^{2/3}/N`. At `(8·10⁴, 500)`, `R_0 = 17.45`.
- The twists `k = −2` (the slot coefficient's angle), `−1`, `1` and `2` give `R_k` between `0.48` and `0.75`: no excess over the diagonal.

**The column term (N2).** The rows `k` are squarefree of norm `≤ K`, and the columns `n` squarefree of norm in `(N/2, N]`. Let `Q = Σ_k|Σ_n c_n(n/k)_2|²/(#rows·Σ|c_n|²)`. At `(N, K) = (8·10⁴, 250)`, `(8·10⁴, 500)` and `(4·10⁴, 1000)`:
- the aligned control `c_n = (n/k₀)_2` gives `Q = 131.2, 70.9, 21.0`, about `#columns/#rows`;
- random phases give `0.82–1.08`;
- the Gauss-sum models `conj(g₃)`, times `1`, `α`, `α²` or `μ`, give `0.59–1.02`;
- a two-slot model `conj(g₃)α·S`, built from 25 slot pairs like the release's marked slots, gives `0.99`.

The dual coefficients the models stand for come from Proposition `prop:completed-reflection`. Its "`The function $d$ is one of three fixed cusp coefficient functions.`" (line 1795), "constructed from the theta expansions in the proof" (line 1754), has support in "`\{u\lambda^k n b^3:k\ge-4,\ n,b\equiv1\pmod3,\ n\ {\rm sf}\}`" with "`|d(\mu)|\le27\,3^{k/6}|b|`" (lines 1798–1800). At squarefree `n` the models take the conjugate normalized cubic Gauss sum. That is a model of `d`, not derived here.

### 9.4 The review: findings and dispositions

The reviewer ran `slotsplit.py` (46.4 s, rc 0) and `fivesixths.py` (12.0 s, rc 0) on the four files under review. The lead verified every finding directly:
- the release's lines named (1754, 1786–1800, 1813, 1902–1910, 2258–2290, 5582–5590, 7440–7470, 7491–7499, 7505–7660, 16240–16262);
- Dunn and Radziwiłł's text (abstract, Theorems 1.3–1.4, eq. (1.13), Definition 3.1, Propositions 9.1–9.2);
- Heath-Brown's abstract;
- the two ratios papers' arXiv abstracts;
- the model, in session runs, now gated where this note relies on them.

| # | severity | finding | disposition |
|---|---|---|---|
| 1 | major | the trilinear note's character `(B/jA²)_3` is wrong; it is `conj((B/jA)_3)`, and the plain sieve gives `σ = 2/3` | accepted; struck at 7.6 and on the register; 9.1, S8 |
| 2 | minor | `σ = 1/2` also follows from `N + N^{3/4}L^{1/2}`, so the "needs" sentences overstate | accepted; markers in the Summary and sections 2, 4, 7.2, 7.6; S5 row (c) |
| 3 | minor | "square-root size" means two things, and slot sums are not products of prime sums | accepted; struck at 7.2, markers; S5 rows (a), (e) |
| 4 | minor | the ray reaches `5/6` only for `t ≥ 0.5572`, not for `t ≥ 1/2` | accepted; struck in the Summary and on the register, marker in section 8; S6 |
| 5 | minor | `(1, 1, 1)` is the corner of the length box and needs `μ = 2` | accepted; marker in section 8; S6 |
| 6 | minor | Čech's paper concerns real characters, and "only under GRH" is unscoped | accepted; struck at 7.1, 7.6 and on the register |
| 7 | minor | "in every source surveyed … no bound below `X^{5/6}`" overstates both sources | accepted; struck at 7.6 |
| 8 | cosmetic | register: "the follow-up below" is above | edited |
| 9 | cosmetic | S2's point `(1/4, 1/2, 1/4)` fails Xu–Sang's `11b/6` | accepted; marker at 7.3; S2 |
| 10 | cosmetic | an antecedent lost to the strike in section 2 | edited |
| 11 | cosmetic | the Summary's "no crossing" holds at `c = 1` | marker |
| 12 | cosmetic | S4(i) checks a hand-written expression | S4 now also reads the model's coefficients |
| 13 | cosmetic | S5 covered three of five rows, "never exceeds" was sampled at `ℓ′ ≤ 0.36`, and "every dual length" | marker at 7.2; table in 9.5 |
| 14 | cosmetic | section 8's settings omit round 498's readings (`0.8700000` without them) | marker in section 8; S6 |
| 15 | cosmetic | "a cost above about `0.16` buys nothing" | struck in section 8; S6 |
| 16 | cosmetic | Heath-Brown sums over integers `c ≡ 1 (mod 3)`; "(Annals 2024)" is not in the text read | edited at 7.1 |
| 17 | cosmetic | Check 4 omits S7; runtimes | edited |

Out of scope:
- O1: commits `19f70fbc` and `ffb66062` (`columnterm.py`) were not reviewed. Section 9.3 writes them up, and the next round reviews them.
- O2: `crossing.py`'s docstring and README round 500 state the dyads' maximum "In any geometry", but gate X1 samples only `ℓ′ ≤ 0.3`. At `(0.6181, 0.9935)` the program exceeds the formula by `0.178`, through a branch with `v > H`. Every low side has `M′ ≥ 2ℓ′`, because `l_x ≥ ℓ` and `b ≥ 0` give `M′ − 2ℓ′ = M − 2ℓ ≥ 0` at every tuple size. There, gate S7 now checks the formula at 300 random points. `crossing.py` gets a bracketed scope note.

### 9.5 The dictionary, corrected

| hybrid bound on `Σ_{j∼N}\|slot sum\|²` | `σ` | least low side | gates |
|---|---|---|---|
| the release's `N + L + (NL)^{2/3}` | `1` | `13/15` | F2, F3 |
| the slot split, `min(·, N L^{2/3})` (7.3) | `3/4` | `41/48` | S1, S2 |
| squared slot sums `≪ L^{1/2}` in every column (slot sums `≪ L^{3/4}`), `min(·, N L^{1/2})` | `5/8` | `71/84` | S5 (a) |
| the trilinear bound, `N + (NL)^{2/3}` (9.1) | `2/3` | `28/33` | S5 (b), S8 |
| `N + N^{3/4}L^{1/2}` | `1/2` | `5/6` | S5 (c) |
| a square-root sieve, `N + (NL)^{1/2}` | `1/2` | `5/6` | S5 (d) |
| square-root cancellation in every column, `N` | `≤ 1/2` | `5/6` | S5 (e) |

Each row's program is checked at S1's points (`ℓ′ ≤ 0.36`). Only the dual lengths `N < L²` matter: for `N ≥ L²` the release's factor is already `≪ N`.

**T1, restated.** For the release's slot coefficients (9.2) and `N < L²`:

`Σ_{j∼N}|Σ_P γ₂(j; P)ᾱ(P)²ψ(P)ΠW_i/√q_P|² ≪ Z^ε(N + N^{3/4}L^{1/2})`.

That gives `σ = 1/2`. Known here: `σ = 2/3` (9.1).

### 9.6 Outcome

The goal `Re s > 5/6` is still not reached, and no new zero-free region is proved. This section adds:
- the trilinear bound, `σ = 2/3` and the least low side `28/33`, by a written argument. Alone it does not move the boundary.
- the slot coefficient as a composite Gauss sum, which states T1 inside the Kubota–Patterson family;
- the finding that Dunn and Radziwiłł's corrected sieve, as stated, needs input of GRH strength here;
- the review's corrections.

Section 8's routes stand: T1 and T2 at the vertex, T3 alone across the slice for `t ≥ 0.5572`, and combinations of partial inputs.

Reproduce, from this directory:

```
python3 slotsplit.py                          # gates S1-S8, about 70 s
python3 columnterm.py periods_w_8e4.txt       # gates N2, N3, about 15 s; skipped without the prime data
```

## 10. A horizon hit: an unconditional first moment for cubic Gauss sums

Found the same day through the release's own citation: "`The corresponding first-moment asymptotic is proved unconditionally in an independent manuscript \cite[Theorem~1.1]{OpenAICubicFirstMoment}; that result is also not used here.`" (paper.tex lines 125–128). The manuscript is OpenAI, "An unconditional first moment for cubic Gauss sums" (September 25, 2026), under `preprints/` in `github.com/openai/math`. It was read in the local mirror at commit `1581d4c`, the commit of section 0's scan. No surface of the pilot recorded it, and section 0's scan missed it.

**What it states.**
- Abstract: "We prove Patterson's first-moment conjecture for normalized cubic Gauss sums over all primary Eisenstein primes, unconditionally." Its Theorem `thm:main` is `Σ_{Nπ≤X} G(π) = (6/5)c_* X^{5/6}/log X + o(X^{5/6}/log X)`.
- Its Theorem `thm:angular`: for every fixed nonzero `ℓ`, `Σ_{Nπ≤X} θ_ℓ(π)G(π) = o_ℓ(X^{5/6}/log X)`, where `θ_ℓ(z) = (z/|z|)^ℓ`. "`The assertion is pointwise in the integer $\ell$.`"
- "In particular, no GRH-dependent cancellation result is an input." And: "We do not improve the cubic large sieve for arbitrary coefficients."
- Its Proposition `prop:dual` gives a power saving `Σ_{p,q}|A(p,q)|² ≪ Y^{7/3−η}`. It holds for character sums of "admissible prime convolutions": products of a bounded number of primes with independent smooth norm weights, every prime of norm at least `Y^c`. It holds at "the two boundary configurations of the dispersion argument", where Heath-Brown's sieve and the ordinary sieve each give `Y^{7/3}`.

**Its bearing here.**
- At one prime, the slot coefficient `γ₂(π)ᾱ(π)²` is `θ_{−2}(π)G(π)` times factors of finite order: the additive characters' normalizations and `ψ`. So `thm:angular` gives `o(X^{5/6}/log X)` unconditionally for its prime sums, up to those finite-order factors, which the theorem as stated does not include.
- That is a statement at the trivial dual, in one slot. By section 7.2 the trivial dual alone does not move the dyads' maximum, so it does not change `σ`.
- The slot products are admissible prime convolutions in the sense of `prop:dual`: each slot prime has norm `Z^{ℓ/K}`, a fixed power of the product's norm, and each slot carries its own smooth weight `W_i`.
- It is open whether the preprint's corrected dispersion, applied to the angle-twisted coefficients in the mean square over the columns, saves a power on `(NL)^{2/3}`. In a corrected sieve of the shape of Dunn and Radziwiłł's eq. (1.13), the correction term for these coefficients carries sums of `β(B)θ_{−2}(B)ψ(B)N(B)^{−1/6}` over the slot products. Those are products of angular Hecke prime sums, one per slot. Unconditionally such sums save less than any fixed power (the prime ideal theorem for Hecke characters), and without a saving the correction term is the size of the `(NL)^{2/3}` term itself.
- Even with that settled, the remainder `(NL)^{2/3−δ}` with a small fixed `δ` would move `σ` only slightly below `2/3`, short of T1's `1/2`.

**Check 9.**
- (b) The register gets a T1 attack note: the preprint's corrected dispersion with Proposition `prop:dual`, applied to the slot coefficients.
- (c) The signal it needs is a zero-free strip for the angular Hecke `L`-functions `L(s, θ_{−2}ψ)` over `ℚ(ω)`. These have infinite order and are outside the release's finite-order family, so the signal is auxiliary, not circular. It is also a family question in the sense of CLAUDE.md's "Families before single functions": the slot coefficients themselves generate the angular twist `θ_{−2}`. So: does the release's method, or Liu's, reach Hecke characters of nonzero infinity type?

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
  - the horizon scan's hits: Liu's 2610.26835 and the two new versions of Xu–Sang;
  - section 7: the slot-split bound (S1, S2), the dictionary between hybrid bounds and `σ`, which corrects section 2 (S5), the ladder (S3), the vertex's bins (S4), and the literature's scope for T1;
  - section 8: the crossing cost as a third lever, and the target T3 (S6, S7);
  - section 10: the horizon hit (the cubic first-moment preprint) and its scoped bearing on T1;
  - section 9: the trilinear bound `σ = 2/3` (S5 (b), S8); the slot coefficient as the composite Gauss sum `γ₂(P)`, angle-twisted (S8 (ii)); Dunn–Radziwiłł's corrected sieve found circular as stated; the dictionary's rows (c) and (e); the ray's threshold, the corner `(1, 1, 1)` and the readings' load (S6); `crossing.formula`'s region (S7); the coefficient models (N2, N3); the review's corrections.

**Bearing on RH: none.** The note proves no zero-free region and gains no constraint on zeros. It maps what one method would need.
