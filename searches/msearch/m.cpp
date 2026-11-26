// monotone fan-in-2 circuit search for a graph's edge function.
// Rows: each edge (must be 1), each maximal independent set (must be 0).
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <ctime>
#include <string>
#include <vector>
typedef uint64_t u64;
const int K=4;                       // 256 rows max
struct V{u64 w[K];};
static int NI,BOUND,NE,NM,NW,ROWS;static const int N=56;
static V IN[32],T;static std::vector<std::pair<int,int>>ED;
struct G{int op,a,b;};struct C{G g[N];int out;};
static u64 st;static inline u64 rnd(){st^=st<<13;st^=st>>7;st^=st<<17;return st;}
static int act_of(const C&c,bool*use){for(int i=0;i<NI+N;i++)use[i]=0;use[c.out]=1;int a=0;
  for(int i=N-1;i>=0;i--)if(use[NI+i]){a++;use[c.g[i].a]=1;use[c.g[i].b]=1;}return a;}
static V eval(const C&c,int&act){
  bool use[32+N];act=act_of(c,use);static V v[32+N];
  for(int i=0;i<NI;i++)v[i]=IN[i];
  for(int i=0;i<N;i++)if(use[NI+i]){const G&g=c.g[i];V&o=v[NI+i];
    for(int k=0;k<NW;k++)o.w[k]=g.op==0?(v[g.a].w[k]&v[g.b].w[k]):(v[g.a].w[k]|v[g.b].w[k]);}
  V r;for(int k=0;k<K;k++)r.w[k]=k<NW?(v[c.out].w[k]^T.w[k]):0;return r;}
static int pop(const V&x){int s=0;for(int k=0;k<NW;k++)s+=__builtin_popcountll(x.w[k]);return s;}
static G rg(int i){return G{(int)(rnd()&1),(int)(rnd()%(NI+i)),(int)(rnd()%(NI+i))};}
static void mutate(C&c){
  int k=1+rnd()%4;
  while(k--){
    int r=rnd()%100;
    if(r<3){c.out=NI+rnd()%N;continue;}
    int i=rnd()%N;
    if(r<45){if(rnd()&1)c.g[i].a=rnd()%(NI+i);else c.g[i].b=rnd()%(NI+i);}
    else if(r<58)c.g[i].op^=1;
    else if(r<72)c.g[i]=rg(i);
    else if(r<90){if(i==0)continue;int j=rnd()%i;for(int t=j+1;t<N;t++)if(c.g[t].a==NI+i&&(rnd()&1))c.g[t].a=NI+j;}
    else{int t=rnd()%N;if(t<=i)continue;
      if(rnd()&1){if(c.g[t].a<NI+i)c.g[i].a=c.g[t].a;c.g[t].a=NI+i;}
      else{if(c.g[t].b<NI+i)c.g[i].b=c.g[t].b;c.g[t].b=NI+i;}}
  }
}
static std::vector<G>SG;
static bool seeded(C&c){                // the given circuit, spread over the slots
  int n=SG.size();if(n>N)return false;int pos[128];for(int i=0;i<N;i++)c.g[i]=rg(i);
  int slot=0;for(int k=0;k<n;k++){int left=n-k,room=N-slot;int skip=rnd()%(room-left+1);if(skip>2)skip=rnd()%3;slot+=skip;pos[k]=slot++;}
  auto w=[&](int x){return x<NI?x:NI+pos[x-NI];};
  for(int k=0;k<n;k++)c.g[pos[k]]=G{SG[k].op,w(SG[k].a),w(SG[k].b)};c.out=NI+pos[n-1];return true;
}
static void dump(const C&c){
  bool use[32+N];int a=act_of(c,use);std::vector<int>id(NI+N);for(int i=0;i<NI;i++)id[i]=i;
  int n=0;std::string s;char buf[64];
  for(int i=0;i<N;i++)if(use[NI+i]){id[NI+i]=NI+n++;const G&g=c.g[i];
    snprintf(buf,64,"%s %d %d;",g.op?"or":"and",id[g.a],id[g.b]);s+=buf;}
  printf("FOUND size=%d out=%d : %s\n",a,id[c.out],s.c_str());fflush(stdout);
}
static C fresh(bool useSeed){C p;if(useSeed&&seeded(p))return p;for(int i=0;i<N;i++)p.g[i]=rg(i);p.out=NI+N-1;return p;}
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r");
  int NS;if(!f||fscanf(f,"%d %d %d %d %d",&NI,&BOUND,&NE,&NM,&NS)!=5)return 2;
  ROWS=NE+NM;NW=(ROWS+63)/64;if(NW>K||NI>32){printf("too large rows=%d\n",ROWS);return 3;}
  for(int r=0;r<ROWS;r++){unsigned long long m;if(fscanf(f,"%llu",&m)!=1)return 2;
    for(int i=0;i<NI;i++)if(m>>i&1)IN[i].w[r/64]|=1ULL<<(r%64);if(r<NE)T.w[r/64]|=1ULL<<(r%64);}
  for(int k=0;k<NS;k++){G g;if(fscanf(f,"%d %d %d",&g.op,&g.a,&g.b)!=3)return 2;SG.push_back(g);}
  int shard=atoi(argv[2]);double secs=atof(argv[3]);
  st=0x9E3779B97F4A7C15ULL*(shard+1)^(u64)time(0);for(int i=0;i<20;i++)rnd();
  {C p;if(seeded(p)){int a;V x=eval(p,a);printf("seed rows=%d wrong=%d size=%d\n",ROWS,pop(x),a);fflush(stdout);}}
  time_t t0=time(0);int best=999,bs=999;long long restarts=0;
  while(difftime(time(0),t0)<secs){
    C p=fresh(rnd()%2);int pa;V px=eval(p,pa);
    if(shard%2==0){                     // weighted rows, size capped at BOUND
      std::vector<long long>w(ROWS,1);
      auto sc=[&](const V&x,int a){long long s=0;
        for(int k=0;k<NW;k++){u64 y=x.w[k];while(y){s+=w[k*64+__builtin_ctzll(y)];y&=y-1;}}
        s*=4;if(a>BOUND)s+=(a-BOUND)*40;return s;};
      long long ps=sc(px,pa);int bump=shard%4?1023:255;
      for(long long j=0;j<150000000LL;j++){
        C c=p;mutate(c);int a;V x=eval(c,a);
        if(a<=BOUND+2){long long s=sc(x,a);if(s<=ps){p=c;px=x;pa=a;ps=s;}}
        if((j&bump)==bump){
          for(int k=0;k<NW;k++){u64 y=px.w[k];while(y){w[k*64+__builtin_ctzll(y)]++;y&=y-1;}}
          if((j&0x3ffff)==0x3ffff)for(auto&z:w)z=1+z/2;
          ps=sc(px,pa);
        }
        if(pa<=BOUND){
          int e=pop(px);
          if(e<best){best=e;printf("best wrong=%d at size<=%d\n",e,BOUND);fflush(stdout);}
          if(!e){dump(p);return 0;}
        }
        if((j&0xfffff)==0&&difftime(time(0),t0)>=secs)break;
      }
    }else{                              // neutral drift among correct circuits, shrinking
      int pe=pop(px);long long budget=20000000LL<<(shard%5);
      for(long long j=0;j<budget;j++){
        C c=p;mutate(c);int a;V x=eval(c,a);int e=pop(x);bool acc;
        if(pe==0)acc=!e&&(a<=pa||(rnd()%((shard%4==1)?3000:100000)==0&&a<=pa+1));
        else{acc=e<pe||(e==pe&&a<=pa+1);if(!acc&&rnd()%100000==0&&e<=pe+2)acc=true;}
        if(acc){p=c;pe=e;pa=a;}
        if(!e&&a<bs){bs=a;printf("correct size=%d\n",a);fflush(stdout);if(a<=BOUND){dump(c);return 0;}}
        if((j&0xfffff)==0&&difftime(time(0),t0)>=secs)break;
      }
    }
    restarts++;
  }
  printf("done restarts=%lld bestwrong=%d smallest=%d\n",restarts,best,bs);
}
