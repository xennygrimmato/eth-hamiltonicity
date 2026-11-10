"""Driver: re-runs the fast certificates and checks that the (long) grid logs cover [0.02, 8.5] with every y-box ok.
Use `python3 run_all.py --regrid` to recompute the grid as well (about 1-2 hours on 3 cores)."""
import subprocess, sys, re, glob
def run(cmd):
    out = subprocess.run(cmd, shell=True, capture_output=True, text=True).stdout
    print(out.strip().splitlines()[-1]); return out
ok = True
for cmd in ['python3 check_closed_form.py', 'python3 cert_kernel.py', 'python3 small_y.py 0.02 15.5', 'python3 large_y.py 8']:
    print('$', cmd); o = run(cmd); ok &= ('FAIL' not in o)
if '--regrid' in sys.argv:
    for a, b, m in [('0.02', '0.06', 'geom'), ('0.06', '0.15', 'geom'), ('0.15', '0.5', 'geom'), ('0.5', '1', 'geom'), ('1', '8.5', 'lin')]:
        run(f'python3 grid.py {a} {b} {m} 0.05')
boxes = []
for f in glob.glob('grid_*.log'):
    for line in open(f):
        mm = re.match(r'Y=\[([0-9.e-]+),([0-9.e-]+)\] ratio<=([0-9.]+) (ok|FAIL)', line)
        if mm: boxes.append((float(mm[1]), float(mm[2]), float(mm[3]), mm[4]))
boxes.sort()
cover = 0.02; worst = 0; gok = True
for (a, b, rr, st) in boxes:
    if a > cover + 1e-12: gok = False; print('gap at', cover, a)
    cover = max(cover, b); worst = max(worst, rr); gok &= (st == 'ok')
gok &= cover >= 8.5 - 1e-12
print(f'grid logs: {len(boxes)} y-boxes covering [0.02,{cover}], worst ratio {worst:.4f} ->', 'PASS' if gok else 'FAIL')
ok &= gok
print('ALL PASS: (*) certified for all y>0' if ok else 'NOT ALL PASS')
