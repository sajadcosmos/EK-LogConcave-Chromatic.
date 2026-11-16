import json, math, numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
plt.rcParams.update({'font.size':10,'font.family':'serif'})
rows=json.load(open('rows.json'))
# Fig 1
fig,ax=plt.subplots(figsize=(5.4,4.2))
cols={3:'#1b9e77',4:'#d95f02',5:'#7570b3',6:'#e7298a',7:'#66a61e',8:'#386cb0'}
for n in range(3,9):
    R=[r for r in rows if r['n']==n]
    ax.scatter([1/r['h'] for r in R],[r['minall'] for r in R],s=4,alpha=.5,color=cols[n],label=f'$n={n}$',rasterized=True)
x=np.linspace(0.1,0.75,10); ax.plot(x,x,'k--',lw=1,label='$y=x$')
ax.set_xlabel(r'inner radius $1/h(G)=a_1/a_2$'); ax.set_ylabel(r'$\min\{|q|:P(G,q)=0,\ q\neq0\}$')
ax.set_xscale('log'); ax.set_yscale('log'); ax.legend(fontsize=7,markerscale=3,loc='lower right')
ax.set_title('All 12111 connected graphs with $3\\leq n\\leq 8$',fontsize=10)
fig.tight_layout(); fig.savefig('figures/fig_scatter.pdf'); fig.savefig('figures/fig_scatter.png',dpi=200)
# Fig 3: 2-connected h/(n/2) histogram n=8
fig,ax=plt.subplots(figsize=(5.4,3.4))
R=[r['h']/(r['n']/2) for r in rows if r['n']==8 and r['twoconn']]
ax.hist(R,bins=60,color='#386cb0')
ax.axvline(1,color='k',ls='--',lw=1)
ax.set_xlabel(r'$h(G)/(n/2)$ for the 7123 two-connected graphs with $n=8$'); ax.set_ylabel('count')
fig.tight_layout(); fig.savefig('figures/fig_hist.pdf'); fig.savefig('figures/fig_hist.png',dpi=200)
print('ok', min(R), max(R))
