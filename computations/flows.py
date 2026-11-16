import json, networkx as nx
from fractions import Fraction as Fr
rows=json.load(open('rows.json'))
def flowpoly(G):
    E=list(G.edges()); m=len(E); n=G.number_of_nodes()
    idx={v:i for i,v in enumerate(G.nodes())}
    coeff={}
    for S in range(1<<m):
        par=list(range(n)); 
        def f(x):
            while par[x]!=x: par[x]=par[par[x]]; x=par[x]
            return x
        rk=0
        for i in range(m):
            if S>>i&1:
                a,b=f(idx[E[i][0]]),f(idx[E[i][1]])
                if a!=b: par[a]=b; rk+=1
        k=bin(S).count('1'); null=k-rk
        coeff[null]=coeff.get(null,0)+(-1)**(m-k)
    b=m-n+1
    return [coeff.get(i,0) for i in range(b+1)]
bad=0;tot=0;eqc=0;worst=0
for r in rows:
    if not r['twoconn'] or r['m']>13: continue
    G=nx.from_graph6_bytes(r['g6'].encode()); F=flowpoly(G); b=len(F)-1
    if b<2: continue
    a=[abs(x) for x in F]   # ascending powers of q; w_k = |coeff of q^{b-k}|
    h=Fr(a[1],a[0]) if a[0] else None
    tot+=1
    if h> Fr(b+1,2): bad+=1
    if h==Fr(b+1,2): eqc+=1
    worst=max(worst,float(h)/((b+1)/2))
print('cographic tested',tot,'violations of h<=(b+1)/2:',bad,'equalities',eqc,'max ratio',worst)
