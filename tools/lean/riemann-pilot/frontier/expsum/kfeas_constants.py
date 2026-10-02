import math
def run(k, eta_target=0.25):
    # mirror VinoRec: eta, expo, C recursion (logs)
    eta = k*(k-1)/2
    logC = math.lgamma(k+1)  # k!
    m = 0
    while eta > eta_target:
        s = k + m*k
        E = 2*s - k*(k+1)/2 + eta
        c = 2*(k+2)
        Nn = 2*s + k*(k-1)//2
        logKmain = math.log(16) + 2*k*math.log(k+s) + math.lgamma(k+1) + Nn*math.log(c) + logC + E*math.log(2)
        logKbad = math.log(2) + 2*((k-1)*math.log(c) + (k+s)*math.log(max(2*(k-1),1)))
        logC = max(logKmain, logKbad) + math.log(2)
        eta = max((1-1/k)*eta, k*(k+1)/2 - 2*(s+1)/k)
        m += 1
    l = k*(m+1)
    return m, l, logC, logC/l**2
for k in [2,3,4,6,8,12,16,24,32,48]:
    m,l,lc,r = run(k)
    need = (2*lc + k*math.log(3) + 2*k*math.log(l))/0.5  # log M needed for Phi<1 with sigma-2eta=1/2
    print(f"k={k:3d} m*={m:5d} l={l:7d} logC={lc:12.1f} logC/l^2={r:.4f} logM_needed~{need:.3g}")
