"""Round 33: the constrained-equilibrium edge of the pinned region.

Model: the zero density mu of ghat equals the zeta-zero density sigma(t) = (1/2 pi) log(t/2 pi) on
the pinned (saturated) region (-T, T); outside it the envelope log|ghat| is flat (the Hilbert
transform of mu vanishes); and mu -> a/pi at infinity (exponential type a). With f = mu - a/pi and
Lambda = G/sqrt(z^2 - T^2) (G the Cauchy transform of f), Re Lambda is known on all of R, and
G = O(1/z) requires int_0^T sigma(t)/sqrt(T^2 - t^2) dt = a/2. Asymptotically
T_edge = 4 pi e^{2a}, and T_edge/T_B -> 2/e. Computed here with the smoothed
Riemann-von Mangoldt density N(T) = (T/2 pi) log(T/2 pi e) + 7/8 (zero below its root T0)."""
import math, json, sys
from scipy.integrate import quad
from scipy.optimize import brentq
Ns = lambda t: t/(2*math.pi)*math.log(t/(2*math.pi*math.e)) + 7/8
T0 = brentq(Ns, 5, 14)
sig = lambda t: math.log(t/(2*math.pi))/(2*math.pi)
def lhs(T):
    return quad(lambda th: sig(T*math.sin(th)), math.asin(T0/T), math.pi/2, limit=200)[0]
def t_edge(a): return brentq(lambda T: lhs(T) - a/2, T0*1.01, 1e9)
def t_budget(a): return brentq(lambda T: Ns(T) - a*T/math.pi, 20, 1e9)
if __name__ == "__main__":
    for d in map(float, sys.argv[1:]):
        a = d/2; te, tb = t_edge(a), t_budget(a)
        print(json.dumps(dict(delta=d, T_edge=te, T_edge_asym=4*math.pi*math.exp(2*a), T_B=tb, ratio=te/tb)))
