# Two-hub layout for D=2: hubs p=t(1,-1)/sqrt2, q=-p, terminals {e1,-e2}->p, {-e1,e2}->q, width m, bond b=beta*m.
# cost/m = min_t 4*sqrt(1-sqrt2 t+t^2) + 2*beta*t ; saving s(beta)=4-cost/m.
import numpy as np
t=np.linspace(0,1,200001)
def cost(beta): return np.min(4*np.sqrt(1-np.sqrt(2)*t+t*t)+2*beta*t)
print("beta  cost/m  saving/m   m needed (A=2): [A] 2.828/s   [O] 4/s")
for beta in [0,0.5,0.8284,1.0,1.2,1.3,1.4,np.sqrt(2)]:
    c=cost(beta); s=4-c
    print(f"{beta:.4f} {c:.5f} {s:.5f}  {2*np.sqrt(2)/s if s>1e-9 else float('inf'):.1f}  {4/s if s>1e-9 else float('inf'):.1f}")
