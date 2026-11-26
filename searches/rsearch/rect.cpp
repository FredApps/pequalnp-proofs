// weighted local search: cover all 0-cells with <=K maximal all-0 rectangles.
// input: R C K nrects, then per rect: rowmask colmask
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <ctime>
#include <vector>
#include <cstring>
typedef uint64_t u64;
static u64 st;static inline u64 rnd(){st^=st<<13;st^=st>>7;st^=st<<17;return st;}
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r");int R,C,K,NR;if(!f||fscanf(f,"%d %d %d %d",&R,&C,&K,&NR)!=4)return 2;
  std::vector<u64>rm(NR),cm(NR);for(int i=0;i<NR;i++)if(fscanf(f,"%llu %llu",(unsigned long long*)&rm[i],(unsigned long long*)&cm[i])!=2)return 2;
  st=0x9E3779B97F4A7C15ULL*(atoi(argv[2])+1)^(u64)time(0);for(int i=0;i<20;i++)rnd();
  double secs=atof(argv[3]);int shard=atoi(argv[2]);
  std::vector<std::vector<int>>cells(NR),by(R*C);std::vector<char>target(R*C,0);
  for(int n=0;n<NR;n++)for(int i=0;i<R;i++)if(rm[n]>>i&1)for(int j=0;j<C;j++)if(cm[n]>>j&1){cells[n].push_back(i*C+j);by[i*C+j].push_back(n);target[i*C+j]=1;}
  std::vector<int>T;for(int b=0;b<R*C;b++)if(target[b])T.push_back(b);
  time_t t0=time(0);int best=1000000;long long restarts=0;
  int smooth=1<<(12+shard%6),sample=64<<(shard%5),ten=3+shard%13;
  while(difftime(time(0),t0)<secs){
    std::vector<long long>w(R*C,1),tabu(NR,0);std::vector<int>cnt(R*C,0),sel;int unc=T.size();
    auto add=[&](int n){for(int b:cells[n])if(cnt[b]++==0)unc--;sel.push_back(n);};
    auto del=[&](int s){int n=sel[s];for(int b:cells[n])if(--cnt[b]==0)unc++;sel[s]=sel.back();sel.pop_back();return n;};
    for(long long it=0;it<3000000;it++){
      if(unc<best){best=unc;printf("uncovered %d restart %lld it %lld\n",unc,restarts,it);fflush(stdout);}
      if(!unc){printf("FOUND");for(int n:sel)printf(" %llu:%llu",(unsigned long long)rm[n],(unsigned long long)cm[n]);printf("\n");return 0;}
      if((int)sel.size()>=K){
        int bs=-1;long long bv=0;int ties=0;
        for(int s=0;s<(int)sel.size();s++){long long v=0;for(int b:cells[sel[s]])if(cnt[b]==1)v+=w[b];
          if(bs<0||v<bv){bs=s;bv=v;ties=1;}else if(v==bv&&rnd()%(++ties)==0)bs=s;}
        if(rnd()%1000<5)bs=rnd()%sel.size();
        int g=del(bs);tabu[g]=it+ten+rnd()%4;
      }
      int nu=0;static std::vector<int>U;U.clear();for(int b:T)if(!cnt[b]){w[b]++;U.push_back(b);}
      nu=U.size();if(!nu)continue;
      // prefer a heavy uncovered cell
      int pick=U[rnd()%nu];for(int k=0;k<(shard%4);k++){int q=U[rnd()%nu];if(w[q]>w[pick])pick=q;}
      auto&cand=by[pick];int bn=-1;long long bg=-1;int ties=0;int m=cand.size();bool all=m<=sample;
      for(int k=0;k<(all?m:sample);k++){int n=cand[all?k:rnd()%m];if(tabu[n]>it)continue;long long v=0;for(int b:cells[n])if(!cnt[b])v+=w[b];
        if(v>bg){bg=v;bn=n;ties=1;}else if(v==bg&&rnd()%(++ties)==0)bn=n;}
      if(bn<0)bn=cand[rnd()%m];
      add(bn);
      if(it%smooth==smooth-1)for(auto&z:w)z=1+z*3/4;
      if((it&1023)==0&&difftime(time(0),t0)>=secs)break;
    }
    restarts++;
  }
  printf("not found; best uncovered %d restarts %lld\n",best,restarts);
}
