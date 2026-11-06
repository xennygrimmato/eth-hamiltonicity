"""flat_coupled2.py -- more coupled families at N0 = 2 with V_tot < 9 (same exact test as flat_coupled.py)."""
from flat_coupled import test, cyc
for m in (2, 3, 4, 5):
    test(cyc((2, 2, 2), (2, 2, 2)) * m, f'T={3*m}  {m}x(R+C+D), every piece (2,2,2) under ALL three merges')
test(cyc((2, 2, 2), (2, 2, 4)) * 3, 'T=9  3x(R+C+D) own (2,2,2) others (2,2,4)')
test(cyc((2, 2, 2), (2, 4, 4)) * 3, 'T=9  3x(R+C+D) own (2,2,2) others (2,4,4)')
test(cyc((2, 2, 2), (2, 2, 4)) * 4, 'T=12 4x(R+C+D) own (2,2,2) others (2,2,4)')
test(cyc((2, 2, 2), (1, 8, 8)) * 2, 'T=6  2x(R+C+D) own (2,2,2) others (1,8,8)')
test(cyc((2, 2, 2), (2, 2, 16)) * 2, 'T=6  2x(R+C+D) own (2,2,2) others (2,2,16)')
test(cyc((2, 2, 1), (4, 4, 4)) * 2, 'T=6  2x(R+C+D) own (2,2,1) others (4,4,4)')
test(cyc((2, 2, 2), (4, 4, 4)) + cyc((2, 2, 2), (2, 2, 2)), 'T=6  R+C+D own (2,2,2) others (4,4,4) + R+C+D all (2,2,2)')
