"""The prolate rate function in closed form (Addendum 439).

For the Slepian concentration eigenvalues lambda_k(c) in the exponentially
small regime k < 2c/pi, the WKB analysis of the prolate equation
((1-x^2) psi')' + (chi - c^2 x^2) psi = 0 gives, with x_t = sqrt(chi)/c the
classical turning point fixed by the quantisation

    (2c/pi) * int_0^{x_t} sqrt((x_t^2 - x^2)/(1 - x^2)) dx = k + 1/2,

the leakage exponent

    -ln(1 - lambda_k) = 2c * int_{x_t}^1 sqrt((x^2 - x_t^2)/(1 - x^2)) dx + O(1).

This script measures -ln(1 - lambda_k) with the verified-prolate machinery of
slepian_arb_certificate.py (256-bit balls, so 1 - lambda_k is resolved to
~1e-50) and compares with the WKB value at c = 50 and 100, both parities.
The fill fraction mu = k/(2c/pi) and x_t are related by
mu = int_{-x_t}^{x_t} sqrt((x_t^2 - x^2)/(1 - x^2)) dx, so the rate function
r(mu) = -ln(1 - lambda_k)/c of Addendum 438 is r = 2 * tunnel(x_t(mu)).
Research instrument: cited by no paper surface, keyed by nothing.
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scipy.integrate import quad
from scipy.optimize import brentq
from flint import arb, ctx
import slepian_arb_certificate as S

def count(xt):
    return 2*quad(lambda x: math.sqrt((xt*xt - x*x)/(1 - x*x)), 0, xt)[0]/math.pi

def tunnel(xt):
    return quad(lambda x: math.sqrt((x*x - xt*xt)/(1 - x*x)), xt, 1)[0]

def wkb_exponent(c, k):
    """2c * tunnel(x_t) with x_t from the quantisation c*count(x_t) = k + 1/2 (None past Shannon)."""
    if k + 0.5 >= c*count(1 - 1e-12): return None
    xt = brentq(lambda x: c*count(x) - (k + 0.5), 1e-9, 1 - 1e-12)
    return 2*c*tunnel(xt), xt

def measured(c, parity, NH):
    with ctx.workprec(256):
        cA = arb(c); c2 = cA*cA
        nmax = 2*(int(2*c/math.pi) + NH) + 80
        ns, pr = S.verified_pswf(parity, NH, nmax, c2, lambda *a: None)
        NF = [(arb(2*n + 1)/2).sqrt() for n in range(nmax)]
        P0, dP0 = S.P0_dP0(nmax)
        out = []
        for p in pr:
            v = p["v"]; coefs = [arb(0)]*nmax
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
    cs = [float(s) for s in sys.argv[1:]] or [50.0, 100.0]
    worst = 0.0
    for c in cs:
        shannon = 2*c/math.pi
        for parity in ("even", "odd"):
            NH = int(shannon*0.98/2)*2 + 2
            om = measured(c, parity, NH)
            print(f"c {c:.0f} {parity}: Shannon {shannon:.1f}")
            for j, o in enumerate(om):
                k = 2*j + (0 if parity == "even" else 1)
                if o <= 1e-48 or o >= 1: continue          # below the 256-bit floor / past Shannon
                w = wkb_exponent(c, k)
                if w is None: continue
                mln = -math.log(o)
                worst = max(worst, abs(mln - w[0]))
                print(f"   k {k:4d} mu {k/shannon:6.3f} x_t {w[1]:6.3f} -ln(1-lambda) {mln:9.3f} WKB {w[0]:9.3f} diff {mln - w[0]:+7.3f}", flush=True)
    print(f"largest |measured - WKB| over the table: {worst:.3f} (an O(1) constant; the exponents run to ~100)")
