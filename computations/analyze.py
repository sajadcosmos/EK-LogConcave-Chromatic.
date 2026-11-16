import pickle, math, numpy as np, networkx as nx, json, time
from fractions import Fraction as Fr
from chrom import chrom
graphs=pickle.load(open('graphs.pkl','rb'))
def roots_of(coeff):
    # coeff ascending ints, strip zero low coefficients
    c=coeff[:]
    while c and c[0]==0: c=c[1:]
    if len(c)<=1: return np.array([])
    return np.roots(c[::-1])
rows=[]
t=time.time()
for n in range(3,9):
    for G in graphs[n]:
        P=chrom(G); a=[abs(x) for x in P]
        h=Fr(a[2],a[1])
        c=P[:]
        while c[0]==0: c=c[1:]
        k1=0
        while sum(c)==0:   # divide by (q-1) exactly
            d=c[::-1]; out=[]; acc=0
            for x in d: acc=acc+x; out.append(acc)
            assert out[-1]==0; c=out[:-1][::-1]; k1+=1
        R=np.roots(c[::-1]) if len(c)>1 else np.array([])
        mods=np.abs(R)
        minall=min([1.0]+list(mods))
        min01=float(mods.min()) if len(R) else None
        # blocks
        blocks=[G.subgraph(b).copy() for b in nx.biconnected_components(G)]
        hb=[]; 
        for B in blocks:
            if B.number_of_nodes()>=3:
                Pb=chrom(nx.convert_node_labels_to_integers(B)); ab=[abs(x) for x in Pb]
                hb.append((B.number_of_nodes(),Fr(ab[2],ab[1])))
        bound2=min(1/(float(x)-1) for _,x in hb) if hb else None
        bmax=max(nb for nb,_ in hb) if hb else None
        twoconn=nx.is_biconnected(G)
        rows.append(dict(n=n,m=G.number_of_edges(),h=float(h),hnum=h.numerator,hden=h.denominator,
            minall=float(minall),min01=None if min01 is None else float(min01),bound2=bound2,bmax=bmax,
            twoconn=twoconn,hblocks=[(nb,float(x)) for nb,x in hb],
            maxmod=float(mods.max()) if len(R) else 1.0, g6=nx.to_graph6_bytes(G,header=False).decode().strip()))
print('time',time.time()-t, len(rows))
json.dump(rows,open('rows.json','w'))
