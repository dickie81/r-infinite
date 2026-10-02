import numpy as np, matplotlib
matplotlib.use('Agg'); import matplotlib.pyplot as plt
d = np.load('kgrind_series.npz'); u, E, om, S, gam = d['u'], d['E'], d['om'], d['S'], d['gam']
SURF, INK, INK2, MUTED, BLUE = '#fcfcfb', '#0b0b0b', '#52514e', '#898781', '#2a78d6'
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 11, 'axes.edgecolor': MUTED, 'axes.labelcolor': INK2,
                     'xtick.color': MUTED, 'ytick.color': MUTED, 'text.color': INK})
fig, (a1, a2) = plt.subplots(2, 1, figsize=(10, 7.2), facecolor=SURF, gridspec_kw=dict(hspace=0.55))
for a in (a1, a2):
    a.set_facecolor(SURF); a.spines[['top', 'right']].set_visible(False); a.grid(axis='y', color='#e6e5e1', lw=0.8)
x = np.exp(u)
a1.plot(x, E, color=BLUE, lw=1.0)
a1.set_xscale('log'); a1.set_xlim(100, 1e8); a1.set_ylim(-1.05, 1.05)
a1.set_title('The grinding: prime-count error ÷ √x, up to 10⁸', loc='left', fontsize=13, color=INK)
a1.set_xlabel('x (log scale)'); a1.set_ylabel('(ψ(x) − x) / √x')
a1.text(1.3e2, 0.88, 'looks like noise, but its size never grows (≤ 0.8 in every decade): the RH "volume"', color=INK2, fontsize=10)
a2.plot(om, S/S.max(), color=BLUE, lw=1.4)
for g in gam[gam < 60]:
    a2.axvline(g, color=MUTED, lw=0.8, ls=(0, (3, 3)), zorder=0)
a2.set_xlim(0, 60); a2.set_ylim(0, 1.12)
a2.set_title('Its hidden tones: spectrum on the log scale', loc='left', fontsize=13, color=INK)
a2.set_xlabel('frequency in log x'); a2.set_ylabel('relative strength')
a2.text(14.4, 1.04, 'dashed lines = heights of ζ\'s zeros (14.13, 21.02, 25.01, …)', color=INK2, fontsize=10)
fig.savefig('grinding.png', dpi=150, facecolor=SURF, bbox_inches='tight')
