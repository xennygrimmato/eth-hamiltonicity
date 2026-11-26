"""[N] The three-angle family  F_c(theta) = sum_{i<j} cos((ti-tj)/2) sqrt(1 + c sin^2((ti+tj)/2))  on [-pi/2,pi/2]^3.
(I) is c = 9;  (I_w) is c = 9/w^2;  the sharp member is c = 8 (half-ellipse of axis ratio 3)."""
import numpy as np
def F(c, t1, t2, t3):
    T = lambda a, b: np.cos((a-b)/2)*np.sqrt(1 + c*np.sin((a+b)/2)**2)
    return T(t1, t2) + T(t1, t3) + T(t2, t3)
if __name__ == "__main__":
    n = 181
    g = np.linspace(-np.pi/2, np.pi/2, n)
    t1, t2, t3 = np.meshgrid(g, g, g, indexing='ij')
    r2 = t1**2 + t2**2 + t3**2
    for c in (9.0, 8.5, 8.0, 7.9, 7.5):
        f = F(c, t1, t2, t3)
        k = np.argmin(f); i = np.unravel_index(k, f.shape)
        far = f[r2 > 0.09]; corner = f[-1, -1, 0]
        print(f"c={c}: grid min={f.min():.6f} at theta/(pi/2)={[round(g[j]/(np.pi/2),3) for j in i]}; min outside |theta|<=0.3: {far.min():.6f}; value at corner (pi/2,pi/2,-pi/2): {corner:.6f}")
    # Hessian at 0 for general c:  F = 3 + theta^T Q theta,  Q = ((c-3)/8) Id + ((c+1)/8) J  (c=9: 3/4, 5/4)
    for c in (9.0, 8.0, 3.0, 2.0):
        e = 1e-3
        Q = np.zeros((3, 3))
        for a in range(3):
            for b in range(3):
                ea = np.eye(3)[a]*e; eb = np.eye(3)[b]*e
                Q[a, b] = (F(c, *(ea+eb)) - F(c, *(ea-eb)) - F(c, *(-ea+eb)) + F(c, *(-ea-eb)))/(8*e*e)
        print(f"c={c}: Hessian/2 at 0 eigenvalues {np.round(np.linalg.eigvalsh(Q), 4)}  predicted (c-3)/8={(c-3)/8:.4f} (x2), (c-3)/8+3(c+1)/8={(c-3)/8+3*(c+1)/8:.4f}")
