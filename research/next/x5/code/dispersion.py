"""Idea 1: dispersion engineering. For a level spectrum (energies with multiplicity), fermionic or bosonic,
count symbols (I,J), |I|=|J|, energy <= N  ->  P(N). Report, for equal wires of energy E (|S| ~ P(E), optimistic):
  alpha_eff  = d ln lnP / d ln E
  flat(E)    = ln P(4E) / (2 ln P(E))          must be >= 1 for any identity with degree Theta = 4E (flattening)
  rho_cert   = max_N [lnP(N)+lnP(4E-N)] / (4 lnP(E))      the paper-type certified exponent with Theta = 4E
  rho_opt    = same with Theta reduced to the flattening minimum (hypothetical beta < 2)."""
import numpy as np, math, sys

def levels(name, Emax):
    L = []
    if name == 'lin':   L = [2*i+1 for i in range(Emax)]
    elif name == 'quad': L = [i*i + i + 1 for i in range(Emax)]          # ~ i^2
    elif name == 'cube': L = [i**3 + 1 for i in range(Emax)]
    elif name == 'osc2':  # 2D oscillator: energy 2k+2, multiplicity k+1
        for k in range(Emax): L += [2*k+2]*(k+1)
    elif name == 'osc3':
        for k in range(Emax): L += [2*k+3]*((k+1)*(k+2)//2)
    elif name == 'lac4':  # lacunary: energy 4^j, multiplicity 2^j
        j = 0
        while 4**j <= Emax: L += [4**j]*(2**j); j += 1
    elif name == 'lac2':  # energy 2^j, multiplicity 2^(j/2)
        j = 0
        while 2**j <= Emax: L += [2**j]*int(round(2**(j/2))); j += 1
    return [l for l in L if l <= Emax]

def symbol_counts(L, Emax, boson=False):
    """g[d][e]: number of (I,J) with |I|-|J| = d (offset), energy e; return counts with d=0 cumulated"""
    # generating function prod_l (1+z q^l)(1+z^-1 q^l)  [fermion] or 1/((1-z q^l)(1-z^-1 q^l)) [boson]
    D = 60  # max |size difference| tracked
    g = np.zeros((2*D+1, Emax+1)); g[D, 0] = 1.0
    for l in L:
        for sgn in (1, -1):
            if not boson:
                new = g.copy()
                if sgn == 1: new[1:, l:] += g[:-1, :-l] if l > 0 else 0
                else: new[:-1, l:] += g[1:, :-l]
                g = new
            else:
                # multiply by 1/(1 - z^sgn q^l): g[d][e] += g[d-sgn][e-l] processed in increasing e
                for e in range(l, Emax+1):
                    if sgn == 1: g[1:, e] += g[:-1, e-l]
                    else: g[:-1, e] += g[1:, e-l]
        m = g.max()
        if m > 1e250: raise OverflowError
    exact = g[D]
    return np.cumsum(exact)

def analyse(name, Es, boson=False):
    Emax = 4*max(Es)
    L = levels(name, Emax)
    P = symbol_counts(L, Emax, boson)
    lnP = np.log(P)
    rows = []
    for E in Es:
        Th = 4*E
        cert = max(lnP[N] + lnP[Th-N] for N in range(Th+1)) / (4*lnP[E])
        flat = lnP[Th] / (2*lnP[E])
        # minimal Theta with lnP(Theta) >= 2 lnP(E)
        Tm = next(T for T in range(Emax+1) if lnP[T] >= 2*lnP[E] - 1e-9) if lnP[Emax] >= 2*lnP[E] else None
        opt = (max(lnP[N] + lnP[Tm-N] for N in range(Tm+1)) / (4*lnP[E])) if Tm else float('nan')
        a = (math.log(lnP[2*E]) - math.log(lnP[E])) / math.log(2)
        rows.append((E, a, flat, cert, opt, Tm/E if Tm else float('nan')))
    return rows

if __name__ == '__main__':
    Es = [25, 50, 100, 200, 400]
    for boson in (False, True):
        for name in ['lin', 'quad', 'cube', 'osc2', 'osc3', 'lac4', 'lac2']:
            try:
                rows = analyse(name, Es, boson)
            except OverflowError:
                print(name, 'overflow'); continue
            print(f"--- {name} {'boson' if boson else 'fermion'}")
            print("   E  alpha_eff  flat(>=1?)  rho_cert(Th=4E)  rho_opt  Theta_min/E")
            for E, a, f, c, o, t in rows:
                print(f"{E:5d}  {a:.3f}     {f:.3f}       {c:.4f}          {o:.4f}   {t:.2f}")
