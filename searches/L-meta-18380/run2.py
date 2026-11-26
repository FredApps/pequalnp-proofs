import subprocess,sys,os
here=os.path.dirname(os.path.abspath(__file__))
subprocess.check_call(['g++','-O3','-march=native','-std=c++17','-o','/tmp/cgp2',os.path.join(here,'cgp2.cpp')])
procs=[subprocess.Popen(['/tmp/cgp2',str(int(sys.argv[1])*4+k),sys.argv[2]]) for k in range(os.cpu_count() or 4)]
for p in procs: p.wait()
