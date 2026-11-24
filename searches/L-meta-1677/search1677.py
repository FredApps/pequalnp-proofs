# L-meta-1677: Petersen graph minus a vertex (9 inputs, edges below). Is there an AND/OR
# (fan-in two)/NOT circuit with at most 15 gates whose first gate is OR(x0, x6) that computes
# the edge function? Same encoding as search1672.py (CEGAR rows, CaDiCaL, NOT-of-NOT forbidden),
# with gate 0 pinned to OR(0,6); gate 0 is exempt from "every gate is read" and from the swap
# order (removing/moving it would change the first gate). k = 1..15; k >= 12 split into cubes
# on the last three gate kinds. Shards 0..3 split the cube list round-robin.
# Prints RESULT: SAT (circuit in $OUT_DIR/model.txt) or RESULT: UNSAT.
import sys, os, time, multiprocessing
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
N = 9
EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
ALL = list(range(1 << N))
def f(r): return any((r >> a) & 1 and (r >> b) & 1 for a, b in EDGES)

def evalc(circ, r):
    w = [bool((r >> i) & 1) for i in range(N)]
    for kind, a, b in circ:
        w.append((not w[a]) if kind == 'not' else (w[a] and w[b]) if kind == 'and' else (w[a] or w[b]))
    return w[-1]

def solve(k, cube=()):
    top = [0]
    def new():
        top[0] += 1; return top[0]
    S = Cadical153()
    choices = []
    for i in range(k):
        w = N + i; ch = []
        for a in range(w):
            ch.append((new(), 'not', a, None))
            for b in range(a + 1, w):
                ch.append((new(), 'and', a, b)); ch.append((new(), 'or', a, b))
        choices.append(ch)
    for i in range(k):
        enc = CardEnc.equals(lits=[c[0] for c in choices[i]], bound=1, top_id=top[0], encoding=EncType.seqcounter)
        top[0] = max(top[0], enc.nv); S.append_formula(enc.clauses)
    for d, kind0 in cube:
        S.add_clause([c for (c, kind, a, b) in choices[k - 1 - d] if kind == kind0])
    S.add_clause([c for (c, kind, a, b) in choices[0] if (kind, a, b) == ('or', 0, 6)])
    for i in range(1, k - 1):
        S.add_clause([c for j in range(i + 1, k) for (c, kind, a, b) in choices[j] if a == N + i or b == N + i])
    for i in range(k):
        for (c, kind, a, b) in choices[i]:
            if kind == 'not' and a >= N:
                for (c2, k2, a2, b2) in choices[a - N]:
                    if k2 == 'not': S.add_clause([-c, -c2])
    for i in range(1, k - 2):
        idx = {(kind, a, b): n for n, (c, kind, a, b) in enumerate(choices[i + 1])}
        for (c1, k1, a1, b1) in choices[i]:
            n1 = idx[(k1, a1, b1)]
            for (c2, k2, a2, b2) in choices[i + 1]:
                if a2 == N + i or b2 == N + i: continue
                if idx[(k2, a2, b2)] <= n1: S.add_clause([-c1, -c2])
    def add_row(r):
        val = {w: bool((r >> w) & 1) for w in range(N)}
        for i in range(k):
            w = N + i; g = new(); val[w] = g
            for (c, kind, a, b) in choices[i]:
                A = val[a]; B = val[b] if b is not None else None
                if kind == 'not':
                    if isinstance(A, bool): S.add_clause([-c, (g if not A else -g)])
                    else: S.add_clause([-c, -g, -A]); S.add_clause([-c, g, A])
                    continue
                ops = [A, B]
                if kind == 'and':
                    if any(o is False for o in ops): S.add_clause([-c, -g]); continue
                    vs = [o for o in ops if o is not True]
                    for o in vs: S.add_clause([-c, -g, o])
                    S.add_clause([-c, g] + [-o for o in vs])
                else:
                    if any(o is True for o in ops): S.add_clause([-c, g]); continue
                    vs = [o for o in ops if o is not False]
                    for o in vs: S.add_clause([-c, g, -o])
                    S.add_clause([-c, -g] + vs)
        S.add_clause([val[N + k - 1]] if f(r) else [-val[N + k - 1]])
    rows = [r for r in ALL if bin(r).count('1') == 2 and f(r)]
    rows += [r for r in ALL if not f(r) and all(f(r | (1 << i)) for i in range(N) if not (r >> i) & 1)]
    rows += [0, (1 << N) - 1]
    for r in rows: add_row(r)
    used = set(rows)
    while True:
        if not S.solve():
            S.delete(); return False, None, len(used)
        m = set(l for l in S.get_model() if l > 0)
        circ = [next((kind, a, b) for (c, kind, a, b) in choices[i] if c in m) for i in range(k)]
        bad = [r for r in ALL if evalc(circ, r) != f(r)]
        if not bad:
            S.delete(); return True, circ, len(used)
        for r in bad[:4]:
            add_row(r); used.add(r)

KINDS = ['and', 'or', 'not']
def cubes(only_small=False):
    out = [(k, ()) for k in range(1, 12)]
    if only_small:
        return out
    for k in (12, 13, 14, 15):
        out.append((k, ((0, 'not'),)))
        for o in ('and', 'or'):
            out.append((k, ((0, o), (1, 'not'))))
            for p in ('and', 'or'):
                for q in KINDS:
                    out.append((k, ((0, o), (1, p), (2, q))))
    return out

def work(item):
    k, cube = item
    t = time.time()
    sat, circ, nr = solve(k, cube)
    return k, cube, sat, circ, nr, time.time() - t

if __name__ == '__main__':
    argv = [a for a in sys.argv[1:] if a != '--only-small']
    only_small = '--only-small' in sys.argv[1:]
    shard = int(argv[0]) if argv else int(os.environ.get('SHARD', '0'))
    nsh = 4
    allc = cubes(only_small=only_small)
    mine = [c for i, c in enumerate(allc) if i % nsh == shard]
    procs = int(os.environ.get('PROCS', '2'))
    print('shard', shard, 'cubes', len(mine), 'of', len(allc), 'procs', procs, flush=True)
    found = None
    # Processes: at most `procs`. On the box this must stay <= 2.
    ctx = multiprocessing.get_context('fork')
    with ctx.Pool(processes=min(procs, max(1, len(mine)))) as pool:
        for k, cube, sat, circ, nr, dt in pool.imap_unordered(work, mine):
            print('k', k, 'cube', cube, 'SAT' if sat else 'UNSAT', 'rows', nr, '%.0fs' % dt, circ if sat else '', flush=True)
            if sat and found is None:
                found = (k, circ)
                pool.terminate()
                break
    if found:
        od = os.environ.get('OUT_DIR', '.')
        os.makedirs(od, exist_ok=True)
        with open(os.path.join(od, 'model.txt'), 'w') as fh:
            fh.write('k=%d circuit=%r\n' % found)
        print('RESULT: SAT')
    else:
        print('RESULT: UNSAT')
