#!/usr/bin/env python3
"""The sabotage copy of the odd Gram (round-329 sweep, F329-4): weil_prime_gram_odd.gram_odd transcribed with two switches
(the substrate's parts=True archimedean matrix, unused here, omitted), so that the verifier can show the odd form's signs are load-bearing without touching the keyed
substrate. gram_odd_mangled(delta, K, prec, mangle):
  mangle = None            the transcription itself -- the verifier gates it entry for entry (midpoint and radius)
                           against weil_prime_gram_odd.gram_odd at the self-test cell, so the copy cannot drift;
  mangle = "cosine_signs"  the sine-basis autocorrelations replaced by the cosine basis's (weil_prime_gram.gram):
                           off-diagonal om_j S_j - om_k S_k for om_k S_j - om_j S_k (the archimedean part and the
                           prime sums alike), the diagonal sine term's sign flipped;
  mangle = "pole_sign"     the pole term +2 p p^T (the even sector's sign) for -2 p p^T.
Either mangle misses the zero side by more than 1e-3 relative (the committed Gram agrees within 1e-12); the misses are
printed by the verifier's g0 label. Not imported by any producer: it enters no checkpoint key."""
import sys, os, math
from flint import arb, acb, arb_mat, ctx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from weil_prime_gram import prime_powers

MANGLES = (None, "cosine_signs", "pole_sign")

def gram_odd_mangled(delta, K, prec, mangle=None):
    assert mangle in MANGLES, mangle
    cos_signs = mangle == "cosine_signs"
    pole = 2 if mangle == "pole_sign" else -2
    with ctx.workprec(prec):
        a = arb(delta)/2; twoa = 2*a
        pi = arb.pi(); half = arb(1)/2; quarter = arb(1)/4
        om = [arb(k)*pi/a for k in range(K)]
        psi_q = quarter.digamma(); tri_q = acb(quarter).polygamma(1).real
        logpi = pi.log()
        z = [acb(quarter, o/2) for o in om]
        psi = [zz.digamma() for zz in z]
        tri = [zz.polygamma(1) for zz in z]
        M = int(prec*math.log(2)/(2*float(delta))) + 4
        T0 = arb(0)
        Tc = [arb(0)]*K; Tuc = [arb(0)]*K; Ts = [arb(0)]*K
        for m in range(M):
            s = arb(2*m) + half
            e = (-twoa*s).exp()
            T0 += 2*e/s
            for k in range(1, K):
                w = acb(s, -om[k]); ew = (-twoa*w).exp(); q = ew/w
                Tc[k] += 2*q.real; Ts[k] += 2*q.imag
                Tuc[k] += 2*(ew*(twoa/w + 1/(w*w))).real
        sM = arb(2*M) + half
        bound = (-twoa*sM).exp()*(twoa + 1)/(sM*(1 - (-2*twoa).exp()))*2
        err = arb(0, bound)
        T0 += err
        for k in range(1, K):
            Tc[k] += err; Ts[k] += err; Tuc[k] += err
        S = [arb(0)]*K; C1 = [arb(0)]*K; U = [arb(0)]*K
        for k in range(1, K):
            S[k] = psi[k].imag - Ts[k]
            C1[k] = (psi[k].real - psi_q) - (T0 - Tc[k])
            U[k] = tri[k].real/2 - Tuc[k]
        P = [arb(0)]*K
        for k in range(1, K):
            w = acb(half, om[k]); P[k] = (2*(w*a).sinh()/w).imag
        pp = prime_powers(int(math.floor(float(twoa.exp()) + 1e-9)))
        pp = [(n, p) for n, p in pp if arb(n).log() < twoa]
        lam = [(arb(n).log(), arb(p).log()/arb(n).sqrt()) for n, p in pp]
        sinl = [[(om[k]*u).sin() for k in range(K)] for u, _ in lam]
        cosl = [[(om[k]*u).cos() for k in range(K)] for u, _ in lam]
        const = psi_q - logpi
        n = K - 1
        G = arb_mat(n, n); N = [a]*n
        for j in range(1, K):
            for k in range(j, K):
                if j == k:
                    if cos_signs: A = a*C1[k] + U[k]/2 + S[k]/(2*om[k]) + a*T0
                    else:         A = a*C1[k] + U[k]/2 - S[k]/(2*om[k]) + a*T0
                    Pr = arb(0)
                    for i, (u, wgt) in enumerate(lam):
                        if cos_signs: Pr += 2*wgt*((twoa - u)*cosl[i][k] - sinl[i][k]/om[k])/2
                        else:         Pr += 2*wgt*((twoa - u)*cosl[i][k] + sinl[i][k]/om[k])/2
                    val = pole*P[k]*P[k] + const*a + A - Pr
                else:
                    sg = -1 if (j + k) % 2 else 1
                    den = om[j]*om[j] - om[k]*om[k]
                    if cos_signs: A = sg*(om[j]*S[j] - om[k]*S[k])/den
                    else:         A = sg*(om[k]*S[j] - om[j]*S[k])/den
                    Pr = arb(0)
                    for i, (u, wgt) in enumerate(lam):
                        if cos_signs: Pr += 2*wgt*sg*(om[k]*sinl[i][k] - om[j]*sinl[i][j])/den
                        else:         Pr += 2*wgt*sg*(om[j]*sinl[i][k] - om[k]*sinl[i][j])/den
                    val = pole*P[j]*P[k] + A - Pr
                G[j - 1, k - 1] = val; G[k - 1, j - 1] = val
        return G, N, [q for q, _ in pp]

def same_gram(G1, N1, G2, N2):
    """True when the two Grams and norm diagonals agree entry for entry in midpoint and radius (exactly)."""
    n = G1.nrows()
    if n != G2.nrows() or len(N1) != len(N2): return False
    for i in range(n):
        if float((N1[i] - N2[i]).mid()) != 0.0 or float(N1[i].rad() - N2[i].rad()) != 0.0: return False
        for j in range(n):
            if float((G1[i, j] - G2[i, j]).mid()) != 0.0 or float(G1[i, j].rad() - G2[i, j].rad()) != 0.0: return False
    return True
