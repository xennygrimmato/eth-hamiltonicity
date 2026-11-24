#!/usr/bin/env python3
"""Minimal read-only-dependency builder: compiles local modules with `lean`
against the prebuilt oleans of /home/user/anth-build (never written to).
Usage: build.py Module.Name [...]"""
import os, re, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOTS = [os.path.join(HERE, 'src'), os.path.join(HERE, 'ni')]
OUT = os.path.join(HERE, 'build')
ANTH = '/home/user/anth-build/.lake'
LEAN = os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean')
PKGS = ['mathlib', 'batteries', 'aesop', 'Qq', 'proofwidgets', 'plausible',
        'LeanSearchClient', 'importGraph', 'Cli']
LP = [OUT, os.path.join(ANTH, 'build/lib/lean')] + \
     [os.path.join(ANTH, 'packages', p, '.lake/build/lib/lean') for p in PKGS]
ENV = dict(os.environ, LEAN_PATH=':'.join(LP))
OPTS = ['-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
        '-Dexponentiation.threshold=2048', '-Dpp.unicode.fun=true']

def src_of(mod):
    rel = mod.replace('.', '/') + '.lean'
    for r in ROOTS:
        p = os.path.join(r, rel)
        if os.path.isfile(p):
            return p
    return None

def imports(path):
    out = []
    for line in open(path):
        m = re.match(r'^\s*(public\s+)?import\s+(.+)$', line)
        if m:
            out += m.group(2).split()
    return out

deps, order = {}, []
def visit(mod):
    if mod in deps:
        return
    p = src_of(mod)
    deps[mod] = [d for d in imports(p) if src_of(d)] if p else None
    if p:
        for d in deps[mod]:
            visit(d)
        order.append(mod)

for m in sys.argv[1:]:
    visit(m)
local = order
olean = lambda m: os.path.join(OUT, m.replace('.', '/') + '.olean')
done, failed, lock = {}, set(), threading.Lock()
events = {m: threading.Event() for m in local}

def build(m):
    for d in deps[m]:
        events[d].wait()
    if any(d in failed for d in deps[m]):
        failed.add(m); events[m].set(); return
    src, o = src_of(m), olean(m)
    newest = max([os.path.getmtime(src)] + [os.path.getmtime(olean(d)) for d in deps[m]])
    if os.path.exists(o) and os.path.getmtime(o) >= newest:
        events[m].set(); return
    os.makedirs(os.path.dirname(o), exist_ok=True)
    t = time.time()
    r = subprocess.run([LEAN, *OPTS, '-o', o, '-i', o[:-6] + '.ilean', src],
                       env=ENV, capture_output=True, text=True)
    msg = (r.stdout + r.stderr).strip()
    with lock:
        print(f'[{"ok" if r.returncode == 0 else "FAIL"}] {m} ({time.time()-t:.0f}s)', flush=True)
        if msg:
            print(msg[:6000], flush=True)
    if r.returncode != 0:
        failed.add(m)
        if os.path.exists(o): os.remove(o)
    events[m].set()

with ThreadPoolExecutor(int(os.environ.get('JOBS', '4'))) as ex:
    list(ex.map(build, local))
print('FAILED:' if failed else 'ALL OK', ' '.join(sorted(failed)))
sys.exit(1 if failed else 0)
