import numpy as np
from scipy.integrate import quad
from chain2 import Cin
exec(open('push.py').read().split("fams = ")[0])
P=np.pi; c2=np.sqrt(2)*np.log(2)
def diag_defect_LB(a, N=5):
    eps = max(2*a - np.log(2), 0)
    om = lambda k: np.pi*k/(4*a)
    err = a*a/6+a**3/3+a**4/200+a**5/48
    d = lambda k: 1 - np.sin(P*k/2)/(P*k/2)
    psi = lambda k: Cin(P*k/2) - 0.03 + a*d(k) - err - c2*min(om(k)*eps, 2)
    tau = min(psi(k) for k in range(N+1, 3000))
    I2 = a**5/30
    tot = 0
    for k in range(1, N+1):
        s2, s4 = np.sin(P*k/2), np.sin(P*k/4); beta = 4*s4/(P*k)
        cn = 1 + 2*s2/(P*k) - 16*beta*s4/(P*k) + 2*beta**2
        pb = (1.05*cn + 21*beta**2*I2/a)/8
        tot += 2*min(psi(k)-tau, 0)*pb
    return tau - tau*a**4/240 + tot
par = lambda t,p: 1 + p*(t/t[-1])**2
for a in [0.35, 0.36, 0.37, 0.38, 0.39, 0.40]:
    ub, p = trial_UB(a, par)
    print(a, "parabola UB %.4f" % ub, " diag-defect LB N=5 %.4f N=8 %.4f" % (diag_defect_LB(a,5), diag_defect_LB(a,8)))
