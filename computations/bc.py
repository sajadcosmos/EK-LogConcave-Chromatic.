import json, networkx as nx, itertools, random
rows=json.load(open('rows.json'))
def ridge_stats(G, order):
    E=[tuple(e) for e in order]; pos={frozenset(e):i for i,e in enumerate(E)}
    n=G.number_of_nodes()
    bcs=[]
    for cyc in nx.simple_cycles(G):
        cyc=list(cyc); es=[pos[frozenset((cyc[i],cyc[(i+1)%len(cyc)]))] for i in range(len(cyc))]
        mn=min(es); bcs.append(frozenset(es)-{mn})
    def nbc(S):
        return not any(b<=S for b in bcs)
    m=len(E)
    # NBC sets are forests automatically
    def forest(S):
        par=list(range(n))
        def f(x):
            while par[x]!=x: par[x]=par[par[x]]; x=par[x]
            return x
        for i in S:
            a,b=f(E[i][0]),f(E[i][1])
            if a==b: return False
            par[a]=b
        return True
    ridges=[S for S in itertools.combinations(range(1,m),n-3) if nbc(frozenset(S)|{0}) and forest(set(S)|{0})]
    mins=9; tot=0
    for S in ridges:
        S=frozenset(S)|{0}; c=0
        for f in range(1,m):
            if f in S: continue
            T=S|{f}
            if forest(T) and nbc(T): c+=1
        mins=min(mins,c); tot+=c
    return mins, len(ridges)
random.seed(0)
bad=0; cnt=0
for r in rows:
    if not r['twoconn'] or r['n']>7 or r['n']<4: continue
    G=nx.from_graph6_bytes(r['g6'].encode())
    for trial in range(3):
        order=list(G.edges()); random.shuffle(order)
        mn,nr=ridge_stats(G,order); cnt+=1
        if mn<2: bad+=1; print('ridge in <2 facets', r['g6'], mn); break
print('checked',cnt,'bad',bad)
