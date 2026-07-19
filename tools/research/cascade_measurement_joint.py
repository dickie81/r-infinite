#!/usr/bin/env python3
"""
THE MEASUREMENT JOINT (S4) ATTACKED: what remains is one definition.

S4 as named in A25: 'measurement records the typical value' -- one
measured Gaussian mode contributes e^(-1/2) (inverse frames e^(+1/2));
rank-r structures e^(+-r/2); the colour atom e = e^(2/2).  The anchor
(mean action = s/2) was discharged arithmetically at T5-P4.  This
script reduces the JOINT itself to:

   (identity) + (identity) + (LLN theorem) + (one definitional clause)

P1 (Three notions of 'the recorded value' coincide EXACTLY -- Gaussian
   speciality).  For a mode with action S = pi x^2 under the forced
   Gaussian (T5-P2):
     (i)   the r.m.s. point x = sqrt(<x^2>),
     (ii)  the mean-action point S(x) = <S> = 1/2  (T5-P4),
     (iii) the AEP-typical point: surprisal -ln f(x) = entropy h
           (the definition of typicality in information theory)
   are the SAME point, exactly: -ln f(x) - h = S(x) - 1/2 identically,
   so (iii) <=> (ii) <=> x^2 = <x^2>.  'Typical value' is unambiguous
   for the forced Gaussian; the weight there is e^(-1/2) exactly.

P2 (Quenched vs annealed -- what kind of average a record is).
   The UNMEASURED mode contributes the annealed average <e^(-S)> =
   1/sqrt(2) (the partition ratio; T2's bookkeeping).  A RECORD
   contributes the quenched value e^(-<S>) = e^(-1/2).  Jensen's
   inequality separates them; both computed below.

P3 (The quenched value is forced by multiplicativity -- LLN).
   Records compound multiplicatively over independent realizations;
   the almost-sure multiplicative rate of prod_i e^(-S_i) is
       lim (prod e^(-S_i))^(1/n) = e^(-<S>) = e^(-1/2)   a.s.
   -- the geometric mean, EXACT as a rate (Kolmogorov LLN on logs),
   no finite-n asymptotics needed.  Verified by simulation, with the
   1/sqrt(2n) concentration of the mean action.

P4 (Consequences).  Rank-r measured structures: e^(-r/2) exact by
   linearity of T5-P4 (<S_r> = r/2); inverse frames e^(+r/2); the
   colour atom e = e^(2/2) (T8's two Cartan modes); the half-Cartan
   sqrt(e) (r = 1).  Coherence with A38: colourless crossings measure
   no modes -> no e-atoms, as the exclusion required.

P5 (What remains -- the definitional clause D1).  'A measurement is
   a repeatable record whose weight compounds multiplicatively over
   independent realizations.'  Given D1, the factor e^(-<S>) is
   FORCED (P3), and <S> = s/2 is arithmetic (T5-P4).  D1 has no
   tunable content -- it states what a record IS.  S4 thereby reduces
   from a physical lemma to: two exact identities + one LLN theorem
   + one definition.
"""

import math

import numpy as np

PI = math.pi


def P1():
    print("=" * 74)
    print("P1: three notions of 'recorded value' coincide exactly")
    print("=" * 74)
    for a in (1 / (2 * PI), 0.5, 2.0):        # variance choices
        xr = math.sqrt(a)                      # r.m.s. point
        S = xr ** 2 / (2 * a)                  # action at r.m.s.
        f = math.exp(-xr ** 2 / (2 * a)) / math.sqrt(2 * PI * a)
        h = 0.5 * math.log(2 * PI * math.e * a)      # entropy
        print(f"  var = {a:>7.4f}: S(x_rms) = {S:.6f} (= <S> = 1/2);"
              f"  -ln f(x_rms) - h = {-math.log(f)-h:+.2e}")
    print("  identity: -ln f(x) - h = S(x) - 1/2 for every Gaussian =>")
    print("  AEP-typical point == mean-action point == r.m.s. point.")
    print("  weight there: e^(-1/2) = %.6f, exactly." % math.exp(-0.5))


def P2():
    print()
    print("=" * 74)
    print("P2: annealed (unmeasured) vs quenched (recorded)")
    print("=" * 74)
    # x ~ e^(-pi x^2) (the forced Tate Gaussian), S = pi x^2, <S> = 1/2
    rng = np.random.default_rng(11)
    x = rng.normal(0, math.sqrt(1 / (2 * PI)), 2_000_000)
    S = PI * x * x
    ann = np.mean(np.exp(-S))
    print(f"  annealed <e^(-S)> = {ann:.6f}   analytic 1/sqrt(2)"
          f" = {1/math.sqrt(2):.6f}   (partition ratio: unmeasured)")
    print(f"  quenched e^(-<S>) = {math.exp(-np.mean(S)):.6f}   analytic"
          f" e^(-1/2) = {math.exp(-0.5):.6f}   (record)")
    print("  Jensen separates them; the dictionary's measured-mode factor")
    print("  is the QUENCHED value.")


def P3():
    print()
    print("=" * 74)
    print("P3: the quenched value is the a.s. multiplicative rate (LLN)")
    print("=" * 74)
    rng = np.random.default_rng(23)
    for n in (10, 1000, 100000):
        reps = 200
        xs = rng.normal(0, math.sqrt(1 / (2 * PI)), (reps, n))
        Ss = PI * xs * xs
        rates = np.exp(-Ss.mean(axis=1))       # (prod e^-S)^(1/n)
        print(f"  n = {n:>6}: rate = {rates.mean():.6f}"
              f" +/- {rates.std():.6f}   (e^(-1/2) = {math.exp(-0.5):.6f};"
              f" predicted spread ~ {math.exp(-0.5)/math.sqrt(2*n):.6f})")
    print("  => (prod e^(-S_i))^(1/n) -> e^(-1/2) a.s.; concentration")
    print("     1/sqrt(2n) as predicted (Var S = 1/2).  The per-record")
    print("     factor is exact as a rate -- no finite-n apology.")


def P4():
    print()
    print("=" * 74)
    print("P4: consequences at every rank (exact by linearity)")
    print("=" * 74)
    for r, name in [(1, "half-Cartan sqrt(e)"), (2, "colour atom e"),
                    (4, "e^2 (four modes)")]:
        print(f"  rank {r}: <S_r> = {r/2:.1f} -> factor e^(+-{r/2:.1f})"
              f" = {math.exp(r/2):.5f}  [{name}]")
    print("  coherence with A38: a colourless crossing measures no Cartan")
    print("  modes -> rank 0 -> factor 1: exactly the exclusion used.")


if __name__ == "__main__":
    P1()
    P2()
    P3()
    P4()
    print()
    print("=" * 74)
    print("P5: the residue is one definition (D1): 'a measurement is a")
    print("repeatable record whose weight compounds multiplicatively over")
    print("independent realizations.'  Given D1: geometric mean forced")
    print("(P3), mean action arithmetic (T5-P4), typicality unambiguous")
    print("(P1).  S4 = two identities + one LLN theorem + one definition.")
    print("=" * 74)
