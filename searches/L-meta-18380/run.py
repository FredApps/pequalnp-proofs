import subprocess,sys,os
here=os.path.dirname(os.path.abspath(__file__))
subprocess.check_call(['g++','-O3','-march=native','-std=c++17','-o','/tmp/cgp',os.path.join(here,'cgp.cpp')])
procs=[subprocess.Popen(['/tmp/cgp',str(int(sys.argv[1])*4+k),sys.argv[2]]) for k in range(os.cpu_count() or 4)]
for p in procs: p.wait()
