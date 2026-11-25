import os, subprocess, sys, time
s = sys.argv[1]; mask = '4397'
out = os.environ.get('OUT_DIR', '.')
here = os.path.dirname(os.path.abspath(__file__))
t0 = time.time()
subprocess.run('git clone -q --depth 1 https://github.com/arminbiere/cadical /tmp/cadical && cd /tmp/cadical && ./configure >/dev/null && make -j4 >/dev/null 2>&1', shell=True, check=True)
print('cadical built', time.time() - t0, flush=True)
cnf = f'{out}/p_{s}.cnf'; lrat = f'{out}/p_{s}.lrat'
subprocess.run([sys.executable, f'{here}/genprom.py', '8', s, mask, cnf], check=True)
r = subprocess.run(['/tmp/cadical/build/cadical', '-q', '--unsat', '--seed=2', '--lrat', '--no-binary', cnf, lrat], capture_output=True, text=True)
print('cadical exit', r.returncode, 'time', time.time() - t0, flush=True)
print(r.stdout[-300:])
