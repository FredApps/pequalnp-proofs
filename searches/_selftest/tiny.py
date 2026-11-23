# Self-test for the compute offload. Shard k: pigeonhole PHP(n+1 -> n) with n = 3 + k is UNSAT;
# odd shards instead solve PHP(n -> n), which is SAT, and write the model to $OUT_DIR/model.txt.
import os, sys
from pysat.solvers import Solver
shard, solver = int(sys.argv[1]), sys.argv[2]
n = 3 + shard
pigeons = n if shard % 2 else n + 1
v = lambda p, h: p * n + h + 1
cnf = [[v(p, h) for h in range(n)] for p in range(pigeons)]
cnf += [[-v(p, h), -v(q, h)] for h in range(n) for p in range(pigeons) for q in range(p + 1, pigeons)]
with Solver(name=solver, bootstrap_with=cnf) as s:
    if s.solve():
        m = s.get_model()
        open(os.path.join(os.environ.get('OUT_DIR', '.'), 'model.txt'), 'w').write(' '.join(map(str, m)) + '\n')
        print('RESULT: SAT')
    else:
        print('RESULT: UNSAT')
print(f'shard={shard} pigeons={pigeons} holes={n} solver={solver}')
