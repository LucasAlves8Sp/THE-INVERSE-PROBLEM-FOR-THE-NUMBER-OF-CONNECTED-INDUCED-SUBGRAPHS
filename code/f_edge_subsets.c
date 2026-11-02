/* For each line "n m u1 v1 ... um vm": print c(G) and F(G).
   c by vertex subsets (BFS closure); F = n + #{nonempty edge sets whose edge-induced graph is connected} by DSU. */
#include <stdio.h>
#include <stdlib.h>
int main(){int n,m;static int U[64],V[64];
 while(scanf("%d %d",&n,&m)==2){for(int i=0;i<m;i++) if(scanf("%d %d",&U[i],&V[i])!=2) return 1;
  if(m>26){printf("-1 -1\n");continue;}
  long F=n;
  for(long E=1;E<(1L<<m);E++){int par[32];for(int i=0;i<n;i++)par[i]=i;
   int verts=0;for(int i=0;i<m;i++)if(E>>i&1){verts|=1<<U[i]|1<<V[i];
     int a=U[i],b=V[i];while(par[a]!=a)a=par[a];while(par[b]!=b)b=par[b];if(a!=b)par[a]=b;}
   int root=-1,ok=1;for(int i=0;i<n;i++)if(verts>>i&1){int a=i;while(par[a]!=a)a=par[a];if(root<0)root=a;else if(a!=root){ok=0;break;}}
   F+=ok;}
  int adj[32]={0};for(int i=0;i<m;i++){adj[U[i]]|=1<<V[i];adj[V[i]]|=1<<U[i];}
  long c=0;for(long S=1;S<(1L<<n);S++){long seen=S&-S,fr=seen;while(fr){int i=__builtin_ctzl(fr);fr&=fr-1;long nb=adj[i]&S&~seen;seen|=nb;fr|=nb;}c+=(seen==S);}
  printf("%ld %ld\n",c,F);}
 return 0;}
