# Is there a monotone fan-in-2 AND/OR formula of depth <= D for f = C5-edge o MAJ3 (15 inputs)?
# Complete binary tree of depth D (x op x = x pads smaller depths). Monotone => checking all
# minterms (true) and all maximal false points (false) is equivalent to checking all 2^15 inputs.
import itertools, sys
from pysat.solvers import Solver
from pysat.card import CardEnc
from pysat.formula import IDPool
import os
CFG = [(6,'cadical153'),(6,'glucose4'),(6,'maplechrono'),(7,'cadical153')]
SH = os.environ.get('SHARD')
if SH is not None:
    D, SOLV = CFG[int(SH)]
else:
    D = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    SOLV = sys.argv[2] if len(sys.argv) > 2 else 'cadical153'
blocks = [(i, i+5, i+10) for i in range(5)]
f = lambda z: any(sum(z[q] for q in blocks[i]) >= 2 and sum(z[q] for q in blocks[(i+1) % 5]) >= 2 for i in range(5))
minterms = []
for i in range(5):
    j = (i+1) % 5
    for a in itertools.combinations(blocks[i], 2):
        for b in itertools.combinations(blocks[j], 2):
            minterms.append(set(a) | set(b))
maxfalse = []
for S in [(0,2),(1,3),(2,4),(3,0),(4,1)]:
    others = [k for k in range(5) if k not in S]
    for ch in itertools.product(range(3), repeat=3):
        x = set()
        for k in S: x |= set(blocks[k])
        for k, c in zip(others, ch): x.add(blocks[k][c])
        maxfalse.append(x)
rows = [(m, 1) for m in minterms] + [(m, 0) for m in maxfalse]
pool = IDPool(); cl = []
nleaf = 2**D
for l in range(nleaf):
    cl += CardEnc.equals([pool.id(('lab', l, v)) for v in range(15)], 1, vpool=pool).clauses
cl.append([pool.id(('lab', 0, 0))])  # symmetry: the group acts transitively on inputs, so WLOG leftmost leaf is x0
node = lambda k, r: pool.id(('val', k, r))
for r, (x, t) in enumerate(rows):
    for l in range(nleaf):
        for v in range(15):
            cl.append([-pool.id(('lab', l, v)), node(nleaf + l, r) if v in x else -node(nleaf + l, r)])
    for k in range(1, nleaf):
        a, b, o, z = node(2*k, r), node(2*k+1, r), node(k, r), pool.id(('and', k))
        cl += [[-z, -o, a], [-z, -o, b], [-z, o, -a, -b], [z, o, -a], [z, o, -b], [z, -o, a, b]]
    cl.append([node(1, r)] if t else [-node(1, r)])
s = Solver(name=SOLV, bootstrap_with=cl)
r = s.solve()
print('D', D, 'rows', len(rows), 'SAT' if r else 'UNSAT', flush=True)
if r:
    m = set(v for v in s.get_model() if v > 0)
    def ev(k, z):
        if k >= nleaf:
            return z[[v for v in range(15) if pool.id(('lab', k-nleaf, v)) in m][0]]
        a, b = ev(2*k, z), ev(2*k+1, z)
        return (a and b) if pool.id(('and', k)) in m else (a or b)
    def show(k):
        if k >= nleaf:
            return 'x%d' % [v for v in range(15) if pool.id(('lab', k-nleaf, v)) in m][0]
        return '(%s %s %s)' % (show(2*k), '&' if pool.id(('and', k)) in m else '|', show(2*k+1))
    print(show(1))
    open(os.path.join(os.environ.get('OUT_DIR','.'),'model.txt'),'w').write(show(1)+'\n')
    print('full check', all(bool(ev(1, [(n >> i) & 1 for i in range(15)])) == f([(n >> i) & 1 for i in range(15)]) for n in range(1 << 15)))

print('RESULT: SAT' if r else 'RESULT: UNSAT')
