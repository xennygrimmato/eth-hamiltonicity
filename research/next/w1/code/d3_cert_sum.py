# Sum the 8 inequalities of the S12H uniform certificate (weights all equal) and print the resulting inequality.
nodes = [(a, b, (-a - b) % 3) for a in range(3) for b in range(3)]
idx = {'n%d%d%d' % v: i for i, v in enumerate(nodes)}
FULL = 511
def S(*names): return sum(1 << idx[x] for x in names)
canon = lambda s: min(s, FULL ^ s)
def nm(s):
    s = canon(s)
    for k, lab in enumerate('RCD'):
        for g in range(3):
            if s == canon(sum(1 << i for i, v in enumerate(nodes) if v[k] == g)): return '%s%d' % (lab, g)
    return '{' + ','.join(x for x in idx if (s >> idx[x]) & 1) + '}'
L2 = [  # (A,B,C): h(BC) <= h(AB)+h(AC)
 (S('n000','n111','n201','n210'), S('n012','n102'), S('n021','n120')),
 (S('n000','n102'), S('n012','n120','n210','n222'), S('n201')),
 (S('n000','n120'), S('n021','n102','n201','n222'), S('n210')),
 (S('n000','n012','n102','n210'), S('n111','n201'), S('n120','n222')),
 (S('n000','n021','n120','n201'), S('n102','n222'), S('n111','n210')),
 (S('n000'), S('n102','n201'), S('n120','n210'))]
C2 = [  # 2h(A) <= h(AB)+h(AC)+h(BC)
 (S('n201','n210','n222'), S('n000','n111'), S('n012','n120')),
 (S('n000','n012','n021'), S('n102','n210'), S('n111','n222'))]
tot = {}
def add(s, c):
    s = canon(s); tot[s] = tot.get(s, 0) + c
for A, B, C in L2:
    add(B | C, 1); add(A | B, -1); add(A | C, -1)
    print('L2   h(%s) <= h(%s) + h(%s)' % (nm(B | C), nm(A | B), nm(A | C)))
for A, B, C in C2:
    add(A, 2); add(A | B, -1); add(A | C, -1); add(B | C, -1)
    print('CHLW2 2h(%s) <= h(%s) + h(%s) + h(%s)' % (nm(A), nm(A | B), nm(A | C), nm(B | C)))
print('SUM:', ' '.join('%+d h(%s)' % (c, nm(s)) for s, c in sorted(tot.items()) if c), '<= 0')
