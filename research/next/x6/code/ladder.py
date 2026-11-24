"""Counting calculus for paper-type kernels over a general single-particle spectrum.
F(N) = ln #{(I,J) : sum of level energies <= N}  (|I|=|J| dropped: changes F by O(log N) only).
rho_cert(E) = max_N [F(N)+F(4E-N)] / (4F(E))   (Theta = 4E = total party energy, lambda <= F(E): optimistic)
flat(E) = F(4E)/(2F(E)) must be >= 1.   R2(E) = F(2E)/F(E): ladder theorem says R2 >= sqrt2 - o(1) if density nondecreasing."""
import math, random, sys

def fermi_counts(levels, Emax):
    f = [0] * (Emax + 1); f[0] = 1
    for l in levels:
        if l > Emax: continue
        for e in range(Emax, l - 1, -1):
            f[e] += f[e - l]
    return f

def Fcum(levels, Emax):
    f = fermi_counts(levels, Emax)
    # pairs (I,J) with total energy exactly e: convolution f*f
    g = [0] * (Emax + 1)
    for e1 in range(Emax + 1):
        if f[e1]:
            for e2 in range(Emax + 1 - e1):
                g[e1 + e2] += f[e1] * f[e2]
    out = []; c = 0
    for e in range(Emax + 1):
        c += g[e]; out.append(math.log(c))
    return out

def stats(F, E):
    Th = 4 * E
    cert = max(F[N] + F[Th - N] for N in range(Th + 1)) / (4 * F[E])
    return F[2 * E] / F[E], F[Th] / (2 * F[E]), cert

def ladders(offsets, Emax):
    L = []
    for o in offsets:
        L += [o + 2 * i + 1 for i in range(Emax) if o + 2 * i + 1 <= Emax]
    return L

if __name__ == '__main__':
    random.seed(1)
    Emax = 4 * 300
    print("=== (A) ladder class: unions of ladders o+1, o+3, o+5, ...  (density nondecreasing)")
    print(" spectrum                         E    R2=F(2E)/F(E)  flat   rho_cert")
    specs = {
        'one ladder (paper)': [0],
        '5 flavors': [0] * 5,
        'osc2 (offsets 0,1,2,3..)': list(range(0, Emax, 1)),
        'offsets k^2': [k * k for k in range(40)],
        'offsets 2^k': [2 ** k for k in range(11)],
        'random offsets': sorted(random.randrange(0, 600) for _ in range(30)),
    }
    for name, offs in specs.items():
        F = Fcum(ladders(offs, Emax), Emax)
        for E in (50, 150, 300):
            r2, fl, c = stats(F, E)
            print(f" {name:30s} {E:4d}   {r2:.4f}        {fl:.3f}   {c:.4f}")
    print("=== (B) non-monotone density: band A (gA modes at energy a), band C (gC modes at energy c)")
    best = []
    for E in (60, 120, 240):
        Em = 4 * E
        for gA in (4, 8, 16, 32):
            for a in (1, 2, 3, 5):
                for gC in (0, 8, 32, 128, 512):
                    for cf in (1.0, 1.5, 2.0, 2.5, 3.0):
                        c = max(1, int(cf * E / 4))
                        lev = [a] * gA + [c] * gC
                        F = Fcum(lev, Em)
                        r2, fl, cert = stats(F, E)
                        if fl >= 1:
                            best.append((cert, E, gA, a, gC, c, r2, fl))
    best.sort()
    print(" best (rho_cert, E, gA, a, gC, c, R2, flat):")
    for b in best[:8]:
        print("  ", tuple(round(x, 4) if isinstance(x, float) else x for x in b))
