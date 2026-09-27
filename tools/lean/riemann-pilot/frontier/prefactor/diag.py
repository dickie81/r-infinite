import numpy as np, json, sys
from scipy.integrate import quad
Z = np.array(json.load(open("../../../../research/checkpoints/zeta_zeros_6700.json")),dtype=float)
a=float(sys.argv[1]); L=np.exp(a); eta=1/L; beta=2*np.pi*(L-4*eta)
def H0s(w):
    v=w*w-L*L; K=0.5*(np.exp(beta*np.sqrt(-v)-beta*L)+np.exp(-beta*np.sqrt(-v)-beta*L)); x=np.pi*eta*w
    return K*(np.sin(x)/x if x else 1.0)**8
al=quad(lambda w:w**4*H0s(w),0,L,limit=400)[0]/quad(lambda w:w**2*H0s(w),0,L,limit=400)[0]
def Hout(w):
    v=w*w-L*L; K=np.cos(beta*np.sqrt(np.maximum(v,0))); x=np.pi*eta*w; return w*w*(w*w-al)*K*(np.sin(x)/x)**8
dv=1/(40*beta*L); V=np.arange(a,a+7,dv); x=np.exp(V); S=np.zeros_like(V)
for n in range(1,400): S+=Hout(n*x)
phi=np.exp(V/2)*S
I1=np.trapezoid(phi**2,V)
ts=np.linspace(1,6*2*np.pi*L*L,6000)
gh=np.array([-2*np.trapezoid(phi*np.cos(t*V),V) for t in ts])
dens=np.log(ts/(2*np.pi))/(2*np.pi)
Qpred=np.trapezoid(2*gh**2*dens,ts)
P=np.trapezoid(gh**2,ts)  # should be ~ 2*pi*I1*... check
tmean=np.trapezoid(gh**2*ts,ts)/P
q=np.array([2*(-2*np.trapezoid(phi*np.cos(t*V),V))**2 for t in Z])
print(json.dumps(dict(a=a,I1_over_L9=I1/L**9, plancherel=P/(2*np.pi*I1), Qzeros=q.sum(), Qpred=Qpred,
  logdens_at_tmean=np.log(tmean/2/np.pi)/(2*np.pi), tmean_over_c=tmean/(2*np.pi*L*L))))
