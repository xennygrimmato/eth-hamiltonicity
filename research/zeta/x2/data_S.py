"""[N] data: structure function of actual zeta zeros near t=1e5 (Riemann-Siegel zeros, rs_zeros.py).
Unfold x = theta(t)/pi; S(alpha) estimated by tapered periodogram averaged over alpha-bins; compare GUE min(|a|,1)."""
import numpy as np
g=np.load('/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/x2_zeros/z1e5.npy')
th=lambda t: t/2*np.log(t/(2*np.pi))-t/2-np.pi/8+1/(48*t)
x=th(g)/np.pi; x=x-x[0]; L=x[-1]
w=np.sin(np.pi*x/L)**2   # taper
al=np.linspace(0.025,1.975,40); S=[]
for a in al:
    aa=a+np.linspace(-0.025,0.025,400)
    P=np.abs(np.exp(2j*np.pi*np.outer(aa,x))@w)**2/(w**2).sum()
    S.append(P.mean())
S=np.array(S)
for a,s in zip(al[::2],S[::2]): print('alpha=%.2f S=%.3f GUE=%.3f'%(a,s,min(a,1)))
m=(al>1)&(al<=1.15); print('mean S on (1,1.15]: %.3f   (extremal crystal would need mass ~0.83/0.1 = 8.3)'%S[m].mean())
gaps=np.diff(x); print('gaps: mean %.4f, frac<0.5: %.4f, frac<0.9: %.4f (crystal extremal: ~0 distinct gaps below 0.9)'%(gaps.mean(),(gaps<0.5).mean(),(gaps<0.9).mean()))
