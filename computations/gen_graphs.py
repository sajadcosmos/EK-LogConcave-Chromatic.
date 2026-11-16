import networkx as nx, pickle, time
from networkx.generators.atlas import graph_atlas_g
from pynauty import Graph as NG, certificate
def cert(G):
    n=G.number_of_nodes(); nodes=list(G.nodes()); idx={v:i for i,v in enumerate(nodes)}
    ad={i:[] for i in range(n)}
    for u,v in G.edges(): ad[idx[u]].append(idx[v]); ad[idx[v]].append(idx[u])
    return certificate(NG(n,adjacency_dict=ad))
graphs={}
for G in graph_atlas_g():
    n=G.number_of_nodes()
    if n>=2 and nx.is_connected(G): graphs.setdefault(n,[]).append(nx.convert_node_labels_to_integers(G))
t=time.time(); seen=set(); g8=[]
for G in graphs[7]:
    for mask in range(1,128):
        H=G.copy(); H.add_node(7)
        for i in range(7):
            if mask>>i&1: H.add_edge(7,i)
        c=cert(H)
        if c not in seen: seen.add(c); g8.append(H)
graphs[8]=g8
print({n:len(v) for n,v in graphs.items()}, time.time()-t)
pickle.dump(graphs,open('graphs.pkl','wb'))
