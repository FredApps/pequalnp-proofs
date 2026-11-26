# run.py <graph file name in this dir> <shard> <seconds>
import subprocess,sys,os
here=os.path.dirname(os.path.abspath(__file__))
subprocess.check_call(['g++','-O3','-march=native','-std=c++17','-o','/tmp/n',os.path.join(here,'n.cpp')])
procs=[subprocess.Popen(['/tmp/n',os.path.join(here,sys.argv[1]),str(int(sys.argv[2])*4+k),sys.argv[3]]) for k in range(os.cpu_count() or 4)]
rc=[p.wait() for p in procs]
sys.exit(1 if any(rc) else 0)
