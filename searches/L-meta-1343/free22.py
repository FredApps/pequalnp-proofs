# Sanity run for sat1343.py: the 22-gate case with no shard clause must be SAT.
# Shard k picks a solver from a portfolio.
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ['GATES'] = '22'
import sat1343 as m
names = ['cadical153', 'glucose4', 'maplechrono', 'lingeling']
k = int(os.environ.get('SHARD', sys.argv[1] if len(sys.argv) > 1 else '0'))
t0 = time.time()
r = m.solve_one((-1, names[k % len(names)]))
print('solver', names[k % len(names)], 'sat', r[1], 'sec', round(time.time() - t0))
if r[1]:
    with open(os.path.join(os.environ.get('OUT_DIR', '.'), 'model.txt'), 'w') as f:
        ms = set(l for l in r[3] if l > 0)
        for key, i in r[4].items():
            if i in ms and key[0] in ('s1', 's2', 'and', 'out'):
                f.write(repr(key) + '\n')
print('RESULT: SAT' if r[1] else 'RESULT: UNSAT')
