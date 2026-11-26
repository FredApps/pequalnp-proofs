#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <ctime>
#include <set>
#include <string>
typedef uint64_t u64;
const int NI=6,N=40,W=NI+N;
struct G{int op,a,b;};            // 0 and, 1 or, 2 not
struct C{G g[N];int out;};
static u64 st;
static inline u64 rnd(){st^=st<<13;st^=st>>7;st^=st<<17;return st;}
u64 IN[NI][2],T[2];
static void eval(const C&c,int&err,int&act,bool&notg){
  bool use[W]={0};use[c.out]=1;act=0;notg=0;bool bad=0;
  for(int i=N-1;i>=0;i--)if(use[NI+i]){act++;const G&g=c.g[i];use[g.a]=1;
    if(g.op!=2)use[g.b]=1; else if(g.a>=NI){ if(c.g[g.a-NI].op==2)bad=1; else notg=1;}}
  u64 v[W][2];
  for(int i=0;i<NI;i++){v[i][0]=IN[i][0];v[i][1]=IN[i][1];}
  for(int i=0;i<N;i++)if(use[NI+i]){const G&g=c.g[i];
    for(int k=0;k<2;k++)v[NI+i][k]= g.op==0?(v[g.a][k]&v[g.b][k]):g.op==1?(v[g.a][k]|v[g.b][k]):~v[g.a][k];}
  err=__builtin_popcountll(v[c.out][0]^T[0]);
  if(bad)err+=1000;
}
static G rg(int i){int o=rnd()%16; o=o<7?0:o<14?1:2; return G{o,(int)(rnd()%(NI+i)),(int)(rnd()%(NI+i))};}
static void mutate(C&c){
  int k=1+rnd()%4;
  while(k--){
    int r=rnd()%100;
    if(r<3){c.out=NI+rnd()%N;continue;}
    int i=rnd()%N;
    if(r<45){ if(rnd()&1)c.g[i].a=rnd()%(NI+i);else c.g[i].b=rnd()%(NI+i);}
    else if(r<60){int o=rnd()%16;c.g[i].op=o<7?0:o<14?1:2;}
    else if(r<75){c.g[i]=rg(i);}
    else if(r<90){ // redirect one use of a wire to another earlier wire
      if(i==0)continue; int j=rnd()%i; int w=NI+j;
      for(int t=j+1;t<N;t++){ if(c.g[t].a==NI+i && w<NI+t && (rnd()&1))c.g[t].a=w; }
    } else { // splice: new node feeding an existing use
      int t=rnd()%N; if(t<=i)continue; if(rnd()&1){c.g[i].a=c.g[t].a<NI+i?c.g[t].a:c.g[i].a;c.g[t].a=NI+i;}else{c.g[i].b=c.g[t].b<NI+i?c.g[t].b:c.g[i].b;c.g[t].b=NI+i;}
    }
  }
}
static C seeded(){
  // 22-gate hand circuit, spread over the N slots
  int L[22][3]={{1,0,1},{0,0,1},{1,100,2},{0,100,2},{1,101,103},{0,101,2},
   {1,3,4},{0,3,4},{1,5,6},{0,5,6},{1,106,108},{1,107,109},{0,106,108},{1,111,112},{0,111,112},{0,107,109},
   {0,102,114},{0,104,113},{0,105,110},{1,115,116},{1,119,117},{1,120,118}};
  C c;int pos[22];int used=0;
  for(int i=0;i<N;i++)c.g[i]=rg(i);
  int slot=0;for(int k=0;k<22;k++){int left=22-k,room=N-slot;int skip=rnd()%(room-left+1); if(skip>2)skip=rnd()%3; slot+=skip;pos[k]=slot++;}
  auto w=[&](int x){return x<100?x:NI+pos[x-100];};
  for(int k=0;k<22;k++)c.g[pos[k]]=G{L[k][0],w(L[k][1]),w(L[k][2])};
  c.out=NI+pos[21];return c;
}
static void dump(const C&c,int act,bool notg){
  bool use[W]={0};use[c.out]=1;for(int i=N-1;i>=0;i--)if(use[NI+i]){use[c.g[i].a]=1;if(c.g[i].op!=2)use[c.g[i].b]=1;}
  int id[W];for(int i=0;i<NI;i++)id[i]=i;int n=0;std::string s;char buf[64];
  for(int i=0;i<N;i++)if(use[NI+i]){id[NI+i]=NI+n++;const G&g=c.g[i];
    if(g.op==2)snprintf(buf,64,"not %d;",id[g.a]);else snprintf(buf,64,"%s %d %d;",g.op?"or":"and",id[g.a],id[g.b]);s+=buf;}
  printf("FOUND size=%d notgate=%d out=%d : %s\n",act,(int)notg,id[c.out],s.c_str());fflush(stdout);
}
int main(int argc,char**argv){
  int shard=atoi(argv[1]);double secs=atof(argv[2]);
  st=0x9E3779B97F4A7C15ULL*(shard+1)^(u64)time(0);for(int i=0;i<20;i++)rnd();
  for(int x=0;x<64;x++){for(int i=0;i<NI;i++)if(x>>i&1)IN[i][x/64]|=1ULL<<(x%64);if((x>>3&7)<(x&7))T[x/64]|=1ULL<<(x%64);}
  bool seed=false;
  time_t t0=time(0);int found=0,best=99,bestm=99,printed=0;long long it=0,restarts=0;
  while(difftime(time(0),t0)<secs){
    C p=seed?seeded():C(); if(!seed){for(int i=0;i<N;i++)p.g[i]=rg(i);p.out=NI+N-1;}
    int pe,pa;bool pn;eval(p,pe,pa,pn);
    if(seed&&restarts==0)printf("seed err=%d act=%d\n",pe,pa),fflush(stdout);
    long long since=0;int lim=22+(shard%3==2);long long budget=20000000LL<<(shard%4);
    for(long long j=0;j<budget;j++,it++){
      C c=p;mutate(c);int e,a;bool n;eval(c,e,a,n);
      bool acc;
      if(pe==0){ int cap = (rnd()%20000==0)?lim+1:(pa>lim?pa:lim); acc = e==0 && a<=cap && (a<=pa || rnd()%(shard%2?200:2000)==0);
                 if(!seed) acc = e==0 && (a<=pa || (rnd()%3000==0&&a<=pa+1)); }
      else { acc = e<pe || (e==pe && a<=pa+1); if(!acc && rnd()%100000==0 && e<=pe+2)acc=1; }
      if(acc){p=c;pe=e;pa=a;pn=n;}
      if(e==0){
        if(a<best){best=a;printf("best correct=%d notgate=%d it=%lld\n",a,(int)n,it);fflush(stdout);}
        if(a<=11){dump(c,a,n);return 0;}
      }
      if((j&0xfffff)==0 && difftime(time(0),t0)>=secs)break;
    }
    restarts++;
  }
  printf("done it=%lld restarts=%lld best=%d\n",it,restarts,best);
}
