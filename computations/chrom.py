import itertools, math, sys, json, time
import numpy as np, networkx as nx
from pynauty import Graph as NG, certificate

def falling_to_mono(n):
    # returns list F[j] = coefficients (ascending) of (q)_j
    F=[[1]]
    for j in range(1,n+1):
        prev=F[-1]; new=[0]*(j+1)
        for i,c in enumerate(prev):
            new[i+1]+=c; new[i]-= (j-1)*c
        F.append(new)
    return F
FF=falling_to_mono(12)

def chrom_coeffs(n, adj):
    """adj: list of bitmasks. returns ascending integer coefficients of P(G,q)."""
    N=1<<n
    indep=[False]*N; indep[0]=True
    for S in range(1,N):
        v=(S&-S).bit_length()-1; R=S&~(1<<v)
        indep[S]=indep[R] and not (adj[v]&R)
    p=[None]*N; p[0]={0:1}
    for S in range(1,N):
        low=S&-S; rest=S^low; d={}
        T=rest
        while True:
            B=T|low
            if indep[B]:
                for j,c in p[S^B].items(): d[j+1]=d.get(j+1,0)+c
            if T==0: break
            T=(T-1)&rest
        p[S]=d
    coeff=[0]*(n+1)
    for j,c in p[N-1].items():
        for i,f in enumerate(FF[j]): coeff[i]+=c*f
    return coeff

def nx_to_adj(G):
    nodes=list(G.nodes()); idx={v:i for i,v in enumerate(nodes)}
    adj=[0]*len(nodes)
    for u,v in G.edges():
        adj[idx[u]]|=1<<idx[v]; adj[idx[v]]|=1<<idx[u]
    return len(nodes),adj

def chrom(G):
    n,adj=nx_to_adj(G); return chrom_coeffs(n,adj)
