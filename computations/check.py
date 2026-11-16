import json, math
rows=json.load(open('rows.json'))
H=lambda k: sum(1/j for j in range(1,k+1))
viol=dict(thm1=0,thm2=0,lowH=0,up2c=0,uptree=0)
best={}
for r in rows:
    n=r['n']
    if r['minall'] < 1/r['h'] - 1e-9: viol['thm1']+=1
    if r['min01'] is not None and r['min01'] < r['bound2']-1e-9: viol['thm2']+=1
    if r['h'] < H(n-1)-1e-9: viol['lowH']+=1
    if r['twoconn'] and r['h'] > n/2+1e-9: viol['up2c']+=1
    if r['h']>n-1+1e-9: viol['uptree']+=1
    # constants
    b=best.setdefault(n,dict(c1=9e9,c2=9e9,ratio1=9e9,ratio2=9e9))
    c1=(n-1)*r['minall']
    if c1<b['c1']: b['c1']=c1; b['g1']=r['g6']
    if r['min01'] is not None:
        c2=(r['bmax']-2)*r['min01']
        if c2<b['c2']: b['c2']=c2; b['g2']=r['g6']
    rt=r['minall']*r['h']
    if rt<b['ratio1']: b['ratio1']=rt; b['gr']=r['g6']
print(viol)
for n,b in best.items(): print(n, {k:(round(v,4) if isinstance(v,float) else v) for k,v in b.items()})
# 2-connected max h/(n) and which
for n in range(3,9):
    two=[r for r in rows if r['n']==n and r['twoconn']]
    mx=max(two,key=lambda r:r['h']); mn=min([r for r in rows if r['n']==n],key=lambda r:r['h'])
    print(n,len(two),'max h 2conn',round(mx['h'],4),'n/2',n/2,mx['g6'],'| min h',round(mn['h'],4),'H',round(H(n-1),4),mn['g6'])
