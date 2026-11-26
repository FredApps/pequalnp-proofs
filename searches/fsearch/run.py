import subprocess,sys,os
here=os.path.dirname(os.path.abspath(__file__))
subprocess.check_call(['g++','-O3','-march=native','-std=c++17','-o','/tmp/c',os.path.join(here,'cmp.cpp')])
ps=[subprocess.Popen(['/tmp/c',str(int(sys.argv[1])*4+k),sys.argv[2]]) for k in range(os.cpu_count() or 4)]
rc=[p.wait() for p in ps]
sys.exit(1 if any(rc) else 0)
