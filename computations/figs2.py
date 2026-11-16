import json, math, numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
plt.rcParams.update({'font.size':10,'font.family':'serif'})
rows=json.load(open('rows.json'))
fig,ax=plt.subplots(figsize=(5.4,4.2))
cols={3:'#1b9e77',4:'#d95f02',5:'#7570b3',6:'#e7298a',7:'#66a61e',8:'#386cb0'}
cnt=0; ratios=[]
for n in range(8,2,-1):
    R=[r for r in rows if r['n']==n and r['min01'] is not None]
    cnt+=len(R)
    ratios+= [r['min01']/r['bound2'] for r in R]
    ax.scatter([r['bound2'] for r in R],[r['min01'] for r in R],s=5,alpha=.5,color=cols[n],label=f'$n={n}$',rasterized=True)
x=np.linspace(0,2.2,10); ax.plot(x,x,'k--',lw=1,label='$y=x$')
ax.set_xlabel(r'$\min_B\,1/(h(B)-1)$'); ax.set_ylabel(r'$\min\{|q|:P(G,q)=0,\ q\notin\{0,1\}\}$')
ax.set_xlim(0,2.2); ax.set_ylim(0,2.3); ax.legend(fontsize=7,markerscale=3,loc='lower right')
fig.tight_layout(); fig.savefig('figures/fig_scatter.pdf'); fig.savefig('figures/fig_scatter.png',dpi=200)
print('graphs with a root outside {0,1}:',cnt,'min ratio',min(ratios),'median',np.median(ratios))
# cycle roots figure
fig,axs=plt.subplots(1,2,figsize=(7.2,3.5))
for ax,n in zip(axs,[13,25]):
    r=n-1; k=np.arange(r)
    ys=np.exp(1j*np.pi*(2*k+(0 if n%2 else 1))/r)
    qs=np.append(1+ys,1.0); qs=qs[np.abs(qs)>1e-9]
    t=np.linspace(0,2*np.pi,400)
    h=n/2
    ax.plot(np.cos(t)/h,np.sin(t)/h,color='#d95f02',lw=1.2,label=r'$|q|=1/h$')
    ax.plot(np.cos(t)/(h-1),np.sin(t)/(h-1),color='#7570b3',lw=1.2,ls='-.',label=r'$|q|=1/(h-1)$')
    ax.plot(np.cos(t)/r,np.sin(t)/r,color='#1b9e77',lw=1,ls=':',label=r'$|q|=1/r$')
    ax.scatter(qs.real,qs.imag,s=12,color='#386cb0',zorder=3,label='chromatic roots $\\neq 0$')
    ax.scatter([0],[0],marker='x',color='k',s=20)
    ax.set_xlim(-0.5,2.1); ax.set_ylim(-1.15,1.15); ax.set_aspect('equal')
    ax.set_title(f'Nonzero chromatic roots of $C_{{{n}}}$',fontsize=10)
axs[0].legend(fontsize=6.5,loc='lower left')
fig.tight_layout(); fig.savefig('figures/fig_cycles.pdf'); fig.savefig('figures/fig_cycles.png',dpi=200)
# constants vs n for cycles
fig,ax=plt.subplots(figsize=(5.4,3.4))
ns=np.arange(4,200)
r=ns-1
ax.plot(ns,r*2*np.sin(np.pi/r),color='#386cb0',label=r'$r\cdot\min|q|$ for $C_n$ (exact)')
ax.plot(ns,r*2/(ns-2),color='#7570b3',ls='-.',label=r'$r/(h(C_n)-1)$ (reduced radius)')
ax.plot(ns,r*2/ns,color='#d95f02',label=r'$r/h(C_n)$ (inner radius)')
ax.axhline(2*np.pi,color='gray',ls=':',lw=1); ax.axhline(1,color='#1b9e77',ls=':',lw=1)
ax.text(150,2*np.pi+0.15,r'$2\pi$',fontsize=9); ax.text(150,1.12,r'universal bound $1$',fontsize=8)
ax.set_xlabel('$n$'); ax.set_ylim(0,7.2); ax.legend(fontsize=7,loc='center right')
fig.tight_layout(); fig.savefig('figures/fig_constants.pdf'); fig.savefig('figures/fig_constants.png',dpi=200)
