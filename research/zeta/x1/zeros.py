import mpmath, numpy as np, sys
from multiprocessing import Pool
def z(n):
    mpmath.mp.dps=20
    return float(mpmath.zetazero(n).imag)
if __name__=="__main__":
    N=int(sys.argv[1])
    with Pool() as p: g=p.map(z,range(1,N+1),chunksize=20)
    np.save("zeros.npy",np.array(g))
