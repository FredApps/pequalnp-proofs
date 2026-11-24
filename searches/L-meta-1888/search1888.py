# L-meta-1888 (refutation hunt): an AND/OR (fan-in two)/NOT circuit with at most 18 gates on 11
# inputs x0..x9 and w = x0 OR x2 (input 10) computing the Petersen edge function. Any circuit found
# refutes L-meta-1888 (take x2 = id); it is re-checked on all 1024 inputs before it is reported.
# Encoding as search982_s15.py (CEGAR rows, CaDiCaL, NOT-of-NOT forbidden, every non-output gate
# read later, adjacent independent gates ordered). Cubes: k in {18, 17} x kinds of the last two
# gates (not NOT/NOT) = 16 cubes; shard s (0..3) runs cubes s, s+4, s+8, s+12 on 4 processes.
# UNSAT on a cube proves nothing for the Lean step (no certificate); only SAT matters.
# Prints RESULT: SAT (circuit in $OUT_DIR/model.txt) or RESULT: UNSAT.
import sys, os, time, multiprocessing
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
N = 11
NV = 10
EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def ext(r): return r | ((((r >> 0) | (r >> 2)) & 1) << 10)
ALL = [ext(r) for r in range(1 << NV)]
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
    # cube: (d, kind) pins gate k-1-d to that kind; the cubes below cover every case
    for d, kind0 in cube:
        S.add_clause([c for (c, kind, a, b) in choices[k - 1 - d] if kind == kind0])
    for i in range(k - 1):
        S.add_clause([c for j in range(i + 1, k) for (c, kind, a, b) in choices[j] if a == N + i or b == N + i])
    for i in range(k):
        for (c, kind, a, b) in choices[i]:
            if kind == 'not' and a >= N:
                for (c2, k2, a2, b2) in choices[a - N]:
                    if k2 == 'not': S.add_clause([-c, -c2])
    for i in range(k - 2):
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
    rows = [r for r in ALL if bin(r & 1023).count('1') == 2 and f(r)]
    rows += [r for r in ALL if not f(r) and all(f(ext(r | (1 << i))) for i in range(NV) if not (r >> i) & 1)]
    rows += [ext(0), ext((1 << NV) - 1)]
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
def cubes():
    out = []
    for k in (18, 17):
        for o in KINDS:
            for p in KINDS:
                if o == 'not' and p == 'not': continue
                out.append((k, ((0, o), (1, p))))
    return out

def work(item):
    k, cube = item
    t = time.time()
    sat, circ, nr = solve(k, cube)
    return k, cube, sat, circ, nr, time.time() - t

if __name__ == '__main__':
    shard = int(sys.argv[1]) if len(sys.argv) > 1 else int(os.environ.get('SHARD', '0'))
    mine = [c for i, c in enumerate(cubes()) if i % 4 == shard]
    print('shard', shard, 'cubes', mine, flush=True)
    found = None
    with multiprocessing.Pool(len(mine)) as pool:
        for k, cube, sat, circ, nr, dt in pool.imap_unordered(work, mine):
            print('k', k, 'cube', cube, 'SAT' if sat else 'UNSAT', 'rows', nr, '%.0fs' % dt, circ if sat else '', flush=True)
            if sat:
                assert all(evalc(circ, r) == f(r) for r in ALL)
                found = (k, circ); pool.terminate(); break
    if found:
        od = os.environ.get('OUT_DIR', '.'); os.makedirs(od, exist_ok=True)
        with open(os.path.join(od, 'model.txt'), 'w') as fh: fh.write('k=%d circuit=%r\n' % found)
        print('RESULT: SAT')
    else:
        print('RESULT: UNSAT')
