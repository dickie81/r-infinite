"""The prolate rate function r(mu) = -ln(1 - lambda_k(c))/c at fill fraction
mu = k/(2c/pi), measured at c = 50, 100, 200 with the verified-prolate machinery
of slepian_arb_certificate.py (Slepian eigenvalues lambda_k = (c/2pi)|mu_k|^2 in
256-bit balls, so 1 - lambda_k is resolved far below double precision).
Even sector (k even) and odd sector (k odd) reported separately.
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, ctx
import slepian_arb_certificate as S

def lams(c, parity, NH):
    with ctx.workprec(256):
        cA = arb(c); c2 = cA*cA
        nmax = 2*(int(2*c/math.pi) + NH) + 80
        ns, pr = S.verified_pswf(parity, NH, nmax, c2, lambda *a: None)
        NF = [(arb(2*n + 1)/2).sqrt() for n in range(nmax)]
        P0, dP0 = S.P0_dP0(nmax)
        par0 = 0 if parity == "even" else 1
        out = []
        for k, p in enumerate(pr):
            v = p["v"]
            coefs = [arb(0)]*nmax
            for i, n in enumerate(ns): coefs[n] = v[i]
            if parity == "even":
                psi0 = sum((coefs[n]*NF[n]*P0[n] for n in range(0, nmax, 2)), arb(0))
                mk = arb(2).sqrt()*coefs[0]/psi0
            else:
                dpsi0 = sum((coefs[n]*NF[n]*dP0[n] for n in range(1, nmax, 2)), arb(0))
                mk = cA*(arb(2)/3).sqrt()*coefs[1]/dpsi0
            lk = cA*mk*mk/(2*arb.pi())
            out.append(float((1 - lk).mid()))
        return out

if __name__ == "__main__":
    for c in (50.0, 100.0, 200.0):
        shannon = 2*c/math.pi
        for parity in ("even", "odd"):
            NH = int(shannon*0.98/2)*2 + 2
            one_minus = lams(c, parity, NH)
            print(f"c {c:.0f} {parity}: Shannon {shannon:.1f}")
            for j, om in enumerate(one_minus):
                k = 2*j + (0 if parity == "even" else 1)      # prolate index within the parity sequence
                mu = k/shannon
                if om <= 0: continue
                print(f"   k {k:4d} mu {mu:6.3f} 1-lambda {om:10.3e} r=-ln(1-lambda)/c {-math.log(om)/c:8.4f}", flush=True)
