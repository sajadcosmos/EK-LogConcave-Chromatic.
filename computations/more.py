import json, networkx as nx, itertools
from fractions import Fraction as Fr
from chrom import chrom
import pickle
graphs=pickle.load(open('graphs.pkl','rb'))
rows=json.load(open('rows.json'))
def hval(G):
    a=[abs(x) for x in chrom(nx.convert_node_labels_to_integers(G))]; return Fr(a[2],a[1])
def edge_glued_cycles(G):
    G=nx.Graph(G)
    while G.number_of_nodes()>2:
        found=False
        deg2=[v for v in G if G.degree(v)==2]
        for v in deg2:
            # extend maximal path of degree-2 vertices
            path=[v]; ends=[]
            for nb in G.neighbors(v):
                prev=v; cur=nb; seg=[]
                while G.degree(cur)==2 and cur!=v:
                    seg.append(cur); nxt=[w for w in G.neighbors(cur) if w!=prev][0]; prev,cur=cur,nxt
                ends.append((cur,seg))
            (a,s1),(b,s2)=ends
            if a==v: # whole graph a cycle
                return True
            if a!=b and G.has_edge(a,b):
                for w in [v]+s1+s2: G.remove_node(w)
                found=True; break
        if not found: return False
    return True
mism=0; cnt=0
for r in rows:
    if not r['twoconn']: continue
    G=nx.from_graph6_bytes(r['g6'].encode()); eq=abs(r['h']-r['n']/2)<1e-9
    eg=edge_glued_cycles(G); cnt+=1
    if eq!=eg: mism+=1; 
print('edge-glued-cycle characterization mismatches:',mism,'of',cnt)
# monotonicity under edge addition, n<=7
viol=0; tot=0; strict=0
for n in range(3,8):
    for G in graphs[n]:
        hG=hval(G)
        for u,v in itertools.combinations(range(n),2):
            if not G.has_edge(u,v):
                H=G.copy(); H.add_edge(u,v); hH=hval(H); tot+=1
                if hH>hG: viol+=1
                if hH==hG: strict+=1
print('edge-addition monotonicity: tested',tot,'violations',viol,'ties',strict)
