import numpy as np
from scipy.special import sici
Cin = lambda x: np.euler_gamma + np.log(x) - sici(x)[1]
P = np.pi
def Cin_lb(x, step=P/4):
    x0 = min(x, P/4); v = x0**2/4 - 5/96*x0**4/4
    lo = x0
    while lo < x - 1e-12:
        hi = min(lo+step, x); c = (lo+hi)/2
        F = lambda s: (2/c)*(s - np.sin(s)) - (1/c**2)*(s*s/2 - (np.cos(s) + s*np.sin(s)))
        v += F(hi) - F(lo); lo = hi
    return v
def bounds(a, N, step=P/4):
    C = [0]+[Cin_lb(P*n/2, step) for n in range(1, N+2)]
    d = lambda n: 1 - np.sin(P*n/2)/(P*n/2)
    # K >= 1/u + 1/2 - u/24 - u^2/16*(1+..) - u^3/1600 ; err <= int_0^{2a} 2(u/24 + 0.07 u^2 + u^3/1600)
    err = 2*((2*a)**2/48 + 0.07*(2*a)**3/3 + (2*a)**4/6400)
    phi = [0.0]+[C[n] + a*d(n) - err for n in range(1, N+1)]
    tau = C[N+1] + a*(1 - 2/(P*(N+1))) - err
    I2 = a**5/8   # (int g)^2 bound
    pb = [I2/(8*a)]
    for n in range(1, N+1):
        s2, s4 = np.sin(P*n/2), np.sin(P*n/4)
        beta = 4*s4/(P*n)
        cn = 1 + 2*s2/(P*n) - 16*beta*s4/(P*n) + 2*beta**2
        pb.append((np.sqrt(max(cn,0)*a) + abs(beta)*np.sqrt(I2))**2/(8*a))
    LB = tau + (phi[0]-tau)*pb[0] + 2*sum((phi[n]-tau)*pb[n] for n in range(1, N+1))
    UB = 1 + a/2 + 4*a + 1.5*a**3
    return LB, UB
if __name__ == "__main__":
    for step in [P/4, P/8]:
        for N in [2,3,4,5,6]:
            worst = min((bounds(a,N,step)[0]-bounds(a,N,step)[1], a) for a in np.linspace(1e-4, np.log(2)/2, 400))
            print("step", round(step,3), N, "min margin %.4f at a=%.4f" % worst, " top:", ["%.4f"%v for v in bounds(np.log(2)/2, N, step)])
