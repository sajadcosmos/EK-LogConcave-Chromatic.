import json, networkx as nx, random
from fractions import Fraction as Fr
from chrom import chrom
def h(G):
    a=[abs(x) for x in chrom(nx.convert_node_labels_to_integers(G))]; return Fr(a[2],a[1])
def sp_reducible(G):
    # treewidth<=2 test via multigraph reductions
    M=nx.MultiGraph(G)
    changed=True
    while changed and M.number_of_nodes()>0:
        changed=False
        for v in list(M.nodes()):
            nb=list(M.neighbors(v))
            if len(set(nb))<=1:
                M.remove_node(v); changed=True; break
            if len(set(nb))==2:
                a,b=set(nb); M.remove_node(v); M.add_edge(a,b); changed=True; break
    return M.number_of_nodes()==0
rows=json.load(open('rows.json'))
bad=0;tot=0
for r in rows:
    if not r['twoconn']: continue
    G=nx.from_graph6_bytes(r['g6'].encode())
    eq=abs(r['h']-r['n']/2)<1e-9; sp=sp_reducible(G); tot+=1
    if eq!=sp: bad+=1; print('mismatch',r['g6'],eq,sp)
print('2-connected checked',tot,'mismatches',bad)
# 2-sum test
def two_sum(G1,e1,G2,e2):
    G=nx.disjoint_union(G1,G2); n1=G1.number_of_nodes()
    u1,v1=e1; u2,v2=e2
    G=nx.contracted_nodes(G,u1,u2+n1,self_loops=False); G=nx.contracted_nodes(G,v1,v2+n1,self_loops=False)
    G=nx.Graph(G); G.remove_edge(u1,v1); return G
random.seed(1)
cands=[nx.complete_graph(4),nx.complete_graph(5),nx.petersen_graph(),nx.wheel_graph(6),nx.cycle_graph(5),nx.complete_bipartite_graph(3,3)]
for t in range(8):
    G1=random.choice(cands); G2=random.choice(cands)
    e1=random.choice(list(G1.edges())); e2=random.choice(list(G2.edges()))
    G=two_sum(G1,e1,G2,e2)
    if G.number_of_nodes()>12: continue
    print(G1.number_of_nodes(),G2.number_of_nodes(),'h(G)=',float(h(G)),' h1+h2-1=',float(h(G1)+h(G2)-1))
