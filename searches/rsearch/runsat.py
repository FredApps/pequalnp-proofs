# runsat.py <problem.json> <shard> <seconds> : one solver process per core
import subprocess,sys,os
here=os.path.dirname(os.path.abspath(__file__))
procs=[subprocess.Popen([sys.executable,os.path.join(here,'sat.py'),sys.argv[1],str(int(sys.argv[2])*4+k),sys.argv[3]]) for k in range(os.cpu_count() or 4)]
rc=[q.wait() for q in procs]
sys.exit(1 if any(rc) else 0)
