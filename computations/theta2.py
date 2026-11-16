import math, itertools, json, numpy as np, mpmath as mp
# polynomials as ascending int lists
def mul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]+=x*y
    return r
def add(a,b):
    r=[0]*max(len(a),len(b))
    for i,x in enumerate(a): r[i]+=x
    for i,x in enumerate(b): r[i]+=x
    while len(r)>1 and r[-1]==0: r.pop()
    return r
def pw(a,k):
    r=[1]
    for _ in range(k): r=mul(r,a)
    return r
def divq(a):  # divide by q exactly
    assert a[0]==0; return a[1:]
def divq1(a): # divide by (q-1)
    d=a[::-1]; out=[]; acc=0
    for x in d: acc+=x; out.append(acc)
    assert out[-1]==0; return out[:-1][::-1]
qm1=[-1,1]
def E(s): return divq(add(pw(qm1,s),[(-1)**s*c for c in qm1]))
def D(s): return divq(add(pw(qm1,s),[-(-1)**s]))
def theta(ss):
    A=[0,1]; B=[0,-1,1]   # q, q(q-1)
    for s in ss: A=mul(A,E(s)); B=mul(B,D(s))
    return add(A,B)
def stats(P):
    a=[abs(x) for x in P]; h=a[2]/a[1]
    Q=divq(P); k=0
    while sum(Q)==0: Q=divq1(Q); k+=1
    if len(Q)>1:
        r=np.roots(np.array([float(x) for x in Q[::-1]]))
        mn=float(np.min(np.abs(r)))
    else: mn=None
    return h,mn,k
best={}
for p in [3,4,5,6]:
    for ss in itertools.combinations_with_replacement(range(2,16),p):
        n=2+sum(s-1 for s in ss)
        if n<9 or n>30: continue
        P=theta(list(ss)); h,mn,k=stats(P)
        if mn is None: continue
        c=(n-1)*min(mn,1.0)
        if n not in best or c<best[n][0]: best[n]=(c,ss,h,mn)
res=[]
for n in sorted(best):
    c,ss,h,mn=best[n]; cyc=(n-1)*2*math.sin(math.pi/(n-1))
    res.append((n,ss,round(mn,5),round(c,4),round(cyc,4),round(h,4)))
    print(n,ss,'min|q|',round(mn,5),'r*min',round(c,4),'cycle',round(cyc,4),'h',round(h,4))
json.dump(res,open('theta_best.json','w'))
