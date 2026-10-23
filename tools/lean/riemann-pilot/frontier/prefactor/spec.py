import numpy as np, json, sys
from scipy.integrate import quad
Z = np.array(json.load(open("../../../../research/checkpoints/zeta_zeros_6700.json")),dtype=float)
def run(a):
    L=np.exp(a); eta=1/L; beta=2*np.pi*(L-4*eta)
    def H0s(w):  # scaled by e^{-beta L}
        v=w*w-L*L
        if v>=0: K=np.cos(beta*np.sqrt(v))*np.exp(-beta*L)
        else: K=0.5*(np.exp(beta*np.sqrt(-v)-beta*L)+np.exp(-beta*np.sqrt(-v)-beta*L))
        x=np.pi*eta*w; s=np.sin(x)/x if x!=0 else 1.0
        return K*s**8
    m2=quad(lambda w:w**2*H0s(w),0,L,limit=400,points=[1,2,4])[0]
    m4=quad(lambda w:w**4*H0s(w),0,L,limit=400,points=[1,2,4])[0]
    al=m4/m2
    # tail phi(v)=e^{v/2} sum_n H(n e^v), v>a (outside band: unscaled)
    def Hout(w):
        v=w*w-L*L; K=np.cos(beta*np.sqrt(np.maximum(v,0)))
        x=np.pi*eta*w; return w*w*(w*w-al)*K*(np.sin(x)/x)**8
    dv=1/(40*beta*L); V=np.arange(a, a+7, dv)
    x=np.exp(V); S=np.zeros_like(V)
    for n in range(1,400):
        y=n*x; S+=Hout(y)
    phi=np.exp(V/2)*S
    # norm (scaled by e^{-2 beta L}) of g on [-a,a]
    def Hin(w):
        return w*w*(w*w-al)*H0s(w)
    U=np.linspace(-a,a,2001)
    def EHs(xx):
        s=0; n=1
        while n*xx< 3*L:
            s+= Hin(n*xx) if n*xx<L else 0.0; n+=1
        return np.sqrt(xx)*s
    g=np.array([EHs(np.exp(u))+EHs(np.exp(-u)) for u in U])
    nrm=np.trapezoid(g*g,U)
    # T(t) = int phi e^{itv}; ghat = -(T(t)+T(-t)) = -2 int phi cos(tv)
    def gh(t): return -2*np.trapezoid(phi*np.cos(t*V),V)
    q=np.array([2*gh(t)**2 for t in Z]); Q=q.sum()
    c=2*np.pi*L*L; frac=q[Z>c/2].sum()/Q; tmed=Z[np.searchsorted(np.cumsum(q),Q/2)]
    zmax=Z[-1]
    return dict(a=a,L=L,alpha=al,c=2*np.pi*L*L,beta_L=beta*L,lnQ=np.log(Q),ln_nrm=np.log(nrm),
                lnR=np.log(Q)-np.log(nrm)-2*beta*L, X4=4*np.pi*L*L, zmax=zmax, frac_above_c2=frac, t_median=tmed)
for a in map(float,sys.argv[1:]):
    r=run(a); r['m']=-r['lnR']-r['X4']+9*a  # -lnR = 4X-9a-m ... m = const(+ln a?)
    print(json.dumps({k:round(v,4) if isinstance(v,float) else v for k,v in r.items()}),flush=True)
