# Prelude Derivation Log

A working log of attempts to derive the cascade's starting structure from
Definition 2.1 (`$0 \neq 1$`) alone, with each gap explicitly identified and
either bridged (with the argument) or left open (with the candidate bridges).

This is a working document tied to the conversation in which it was started.
Once the chain is settled, its content will be folded into the Prelude
(`src/cascade-series-prelude.tex`).

## Status

In progress. Four gaps closed; one (Gap 5) has a working bridge identified
but not yet fully closed — see Gap 5 entry below.

---

## Closed (with bridges)

### Gap 1 — Structural properties of `$\neq$` are not extra axioms

**Original concern.** The Prelude's Theorem 3.1 derives orthogonality from
the premise "states share no common component in `$\mathbb{R}^d$`." The
premise itself was the substantive bridge — an interpretive choice tagged
as Open Question 3(a) of the Prelude.

**Bridge.** The relation `$\neq$` has three structural properties that are
operational content of "`$\neq$` is a binary relation in standard logic,"
not additional axioms beyond Definition 2.1:

- **(B) Binary.** Distinguishability admits no gradations.
- **(S) Symmetric.** `$a \neq b \Leftrightarrow b \neq a$`.
- **(L) Local.** The relation between `$a$` and `$b$` depends on `$a$`,
  `$b$` alone, not on what other distinguishable elements exist.

These follow from the meaning of "binary relation" and require no
cascade-internal commitment.

### Gap 2 — Locality excludes the simplex realisation

**Original concern.** The simplex realisation embeds `$d$` states as vertices
of a regular `$(d{-}1)$`-simplex with pairwise inner product `$-1/(d{-}1)$`.
It is `$S_d$`-equivariant, parameter-free, and *not* excluded by the original
"no shared component" premise — its inner product is a fixed structural
value, not a free parameter.

**Bridge.** Property (L). The simplex's pairwise inner product depends
explicitly on `$d$`, so the relation between `$s_1$` and `$s_2$` would
change every time a new state appears in the universe. Locality forbids
this: distinguishability between two specific states is determined by
those states alone.

### Gap 3 — Inner product is not needed at Section 3

**Original concern.** A proposed rewrite of Section 3 introduced inner
product as a primitive in the proof of Theorem 3.1.

**Bridge.** Inner product is a downstream commitment — needed only when
the slicing recurrence (or another structurally demanding step) introduces
it. Section 3 can stay above the inner-product line. Orthogonality moves
to a later section as a one-line corollary once an inner product is
committed (the canonical inner product makes the basis orthonormal).

### Gap 4 — Section 3 needs no algebraic-combination axiom either

**Original concern.** Even without inner product, the rewrite of Section 3
imported "closure under linear combination" as a vector-space axiom — itself
a substantial structural commitment beyond `$0 \neq 1$`.

**Bridge.** "States combine in their cumulative distinction" — the
operational content of cumulation is the bookkeeping of pairwise `$\neq$`
on a `$d$`-element set, not an imported `$+$` operation. What we have at
this stage:

- A set `$S$` of distinct elements.
- Cardinality `$d \in \mathbb{N}$` (via Theorem 4.1's clause-(ii) argument).
- Full pairwise distinguishability — every pair `$(s_i, s_j)$` with
  `$i \neq j$` is distinct.
- Combinatorially: the vertex set of `$K_d$`, equivalently a `$d$`-element
  set with the antireflexive symmetric "`$\neq$`" relation.

This is given by `$0 \neq 1$` + (B, S, L) + clause (ii). No additive
structure is imported. The "combination" of states is the cumulation;
there is no `$s_1 \oplus s_2$` as a third entity at this stage.

---

## Open

### Gap 5 — Cumulation → continuum

**Statement.** From a `$d$`-element set with cumulative distinction
(combinatorial, `$K_d$`-shaped) to a structure supporting:

- Continuous interpolation between states.
- Norms and lengths.
- The slicing recurrence integral `$\int_{-1}^1 (1-x^2)^{d/2}\,dx$`.

**Why the gap exists.** `$0 \neq 1$` + (B, S, L) gives discrete relations.
Cumulation gives a `$d$`-element combinatorial structure. Nothing in this
structure forces a continuum. But the cascade's downstream content (volumes,
sphere areas, slicing recurrence, Gamma function) requires one.

**Candidate bridges (none cleanly closed).**

1. **Self-reference to clause (iii).** Clause (iii) of austerity quotients
   continuous symmetries, presupposing a continuum. The cascade's framework
   self-references the continuum.
   - *Concern:* internal consistency, not derivation.

2. **Foundational footprint.** The Prelude commits to WKL₀/ACA₀ for the
   classical-analysis content (Section 11, item 2). The continuum is
   derivable within WKL₀ via standard analytic coding (Cauchy sequences
   of rationals).
   - *Concern:* the choice of WKL₀/ACA₀ as the analytic base is itself a
     meta-commitment, parallel to "use real numbers for analysis."

3. **Free construction.** The free vector space on the `$d$`-element set
   is the universal additive structure containing it — canonical, no
   choices needed.
   - *Concern:* the field is still a choice. Free abelian group
     (`$\mathbb{Z}$`-coefficients) doesn't give a continuum; free
     `$\mathbb{R}$`-vector space does. The choice of `$\mathbb{R}$` over
     `$\mathbb{Z}$` is unbridged at this stage.

4. **Downstream-driven.** The slicing recurrence requires a continuum;
   therefore the continuum is required for the cascade to be meaningful.
   - *Concern:* circular at the foundational level — the cascade chose
     the recurrence and is now claiming it forces the continuum.

**Working assessment.** Bridge (2) is the cleanest in that it doesn't
introduce a *new* commitment — the continuum becomes derivable within an
already-declared foundational footprint. But it shifts the substantive
commitment to "WKL₀/ACA₀ as analytic base," which is a meta-mathematical
choice rather than a cascade-internal derivation.

#### Working bridge — Graded extension of binary distinguishability

A more cascade-native bridge, identified by working through what continuous
structure the cascade actually wants:

- **Construction.** Extend the discrete cumulation by introducing entities
  with *graded sharing* — a continuous parameter quantifying how much one
  state "shares" with another, ranging from "nothing shared" (extremal,
  fully distinct) to "everything shared" (extremal, identical).
  Geometrically this is the inner-product picture: each state is a unit
  vector, sharing = inner product, original states are the orthogonal
  extremal case (`$\langle s_i, s_j\rangle = 0$`), and non-original states
  populate the continuum.

- **Why this is the right shape.** The cascade's downstream content
  (`$\mathbb{R}^d$`, inner product, slicing recurrence, sphere areas) is
  exactly what the graded-sharing extension gives. This is the
  "in-between" continuum the cascade wants — not the probability simplex
  `$\Delta^{d-1}$` (which would also be a continuous extension, but a
  different one).

- **Compatibility with `$0 \neq 1$`.** The original `$d$` states retain
  their full binary distinguishability — they sit at the *extremal*
  end of the graded sharing scale (sharing = 0). Property (B) is
  preserved on the original states; the continuum extends the structure
  *around* the original binary distinguishability rather than replacing
  or contradicting it. The cascade's sole pre-mathematical input
  (Definition 2.1, `$0 \neq 1$`) remains intact: graded sharing is
  expressed *between additional states* that the extension introduces,
  not between the originals.

- **What this closes.** The "interpretive bridge" framing of the original
  Theorem 3.1 — "states share no common component" as an unstated leap —
  becomes purposeful: graded sharing is the natural structure for asking
  "how distinguishable, exactly?", and the binary case is its extremal
  endpoint. The inner product is no longer imported as a primitive; it
  is the continuous parameter required to support graded sharing across
  all magnitudes.

- **What remains.** The continuum-valued sharing parameter is still real-
  valued, and "real-valued" presupposes the continuum. So the bridge
  *uses* the continuum; it does not derive it from `$0 \neq 1$` alone.
  Gap 5 narrows further (next item).

- **Refinement — the natural parameter is angular.** The inner product
  value lives in `$[-1, 1]$` but is a cosine; the natural continuous
  parameter is the **angle** between unit vectors, ranging over
  `$[0, \pi]$`, with `$\pi/2$` as the orthogonal value. This is not a
  relabelling — it is the parameterisation the cascade *already* uses:

  - Prelude Section 7 (line 555): "*the angle between axis and equator
    is `$\pi/2$`, forcing the half-integer argument in `$B(1/2,\cdot)$`,
    giving `$\Gamma(1/2) = \sqrt{\pi}$`.*" The orthogonal angle `$\pi/2$`
    is the generator of the cascade's `$\sqrt{\pi}$` constant in the
    slicing recurrence.
  - So the parameter space the bridge needs is not generic real numbers,
    it is specifically the angular interval `$[0, \pi]$`. `$\pi$` enters
    as the *extent* of this angular space, not as an imported constant.
  - Original `$d$` states sit at pairwise angle `$\pi/2$` (the extremal
    "fully distinct" case); identical states sit at angle `$0$`; the
    continuum populates the rest of `$[0, \pi]$`.
  - This makes the continuum needed by Gap 5 *purposeful* in a tighter
    sense: it is the angular continuum, with `$\pi$` as its intrinsic
    extent, and the cascade's downstream `$\sqrt{\pi}$` machinery is the
    natural consequence rather than an additional import.

  Gap 5 narrows from "the parameter space `$[0,1]$` or `$[-1,1]$` must
  come from somewhere" to "the angular interval `$[0,\pi]$` must come
  from somewhere." Bridge 2 still supplies it via the foundational
  footprint, but the parameter is now visibly cascade-native rather
  than generic.

- **Net.** Combined with Bridge 2, this is a defensible closure of Gap 5:
  *the continuum is supplied by the foundational footprint and used to
  support the graded extension of binary distinguishability, with the
  original states preserved as the extremal case.* The Prelude's residual
  interpretive commitment narrows from "vector-space realisation" (the
  current Open Question 3(a)) to "the cascade's analytic content lives
  within standard mathematical foundations (WKL₀/ACA₀), and that footprint
  supplies the continuum used to extend binary distinguishability into
  the graded-sharing structure the cascade's downstream content rests on."

**Status:** Working bridge identified. Closure depends on accepting the
foundational-footprint route (Bridge 2) as the source of the continuum.

---

## Notes for next iteration

- If Gap 5 closes via the working bridge (graded extension + foundational
  footprint), the Prelude's residual interpretive commitment narrows to:
  "the cascade operates within standard mathematical foundations
  (WKL₀/ACA₀ for analytic content), and uses that footprint's continuum
  to support graded sharing as the continuous extension of binary
  distinguishability." This is materially weaker than the current item
  3(a) framing ("model `$d$` logical distinctions as `$d$` orthogonal
  directions in a `$d$`-dimensional Euclidean space"), because:

  - The vector-space structure is not imposed but derived as the natural
    home for graded sharing.
  - The inner product is not imposed but derived as the continuous
    sharing parameter.
  - `$\mathbb{R}^d$` is not imposed but emerges as the minimal continuous
    extension of cumulative `$d$`-element distinguishability under graded
    sharing.
  - The original `$d$` states retain full binary distinguishability as the
    extremal (orthogonal) case — `$0 \neq 1$` is preserved untouched.

- Once Gap 5 is accepted, the next gap is the choice of *field* among
  `$\{\mathbb{R}, \mathbb{C}, \mathbb{H}\}$` — handled by Hurwitz +
  clause (ii) in the existing Prelude (lines 756–787).

- After that: Section 3 rewrite (incorporating Gaps 1–4); Section 4
  reorganisation to introduce graded sharing (the inner product) where
  structurally needed; Open Question 3 collapses to either Gap 5's residual
  (foundational-footprint commitment) or a tighter form.
