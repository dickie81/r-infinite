# Prelude Derivation Log

A working log of attempts to derive the cascade's starting structure from
Definition 2.1 (`$0 \neq 1$`) alone, with each gap explicitly identified and
either bridged (with the argument) or left open (with the candidate bridges).

This is a working document tied to the conversation in which it was started.
Once the chain is settled, its content will be folded into the Prelude
(`src/cascade-series-prelude.tex`).

## Status

In progress. Four gaps closed; one currently open.

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

---

## Notes for next iteration

- If Gap 5 closes via Bridge 2, the Prelude's residual interpretive
  commitment narrows to: "the cascade operates within standard mathematical
  foundations (WKL₀/ACA₀ for analytic content)." This is weaker than the
  current item 3(a) framing.

- Once Gap 5 is closed (or accepted), the next gap is the choice of *field*
  among `$\{\mathbb{R}, \mathbb{C}, \mathbb{H}\}$` — handled by Hurwitz +
  clause (ii) in the existing Prelude (lines 756–787).

- After that: Section 3 rewrite (incorporating Gaps 1–4); Section 4
  reorganisation to introduce vector space and inner product where
  structurally needed; Open Question 3 collapses to either Gap 5's residual
  or a tighter form.
