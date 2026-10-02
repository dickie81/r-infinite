import numpy as np, matplotlib
matplotlib.use('Agg'); import matplotlib.pyplot as plt
d = np.load('kslip_series.npz'); u, E, om, S, gam, pred = d['u'], d['E'], d['om'], d['S'], d['gam'], d['pred']
SURF, INK, INK2, MUTED, BLUE, ORANGE = '#fcfcfb', '#0b0b0b', '#52514e', '#898781', '#2a78d6', '#eb6834'
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 11, 'axes.edgecolor': MUTED, 'axes.labelcolor': INK2,
                     'xtick.color': MUTED, 'ytick.color': MUTED, 'text.color': INK})
fig, (a1, a2) = plt.subplots(2, 1, figsize=(10, 7.2), facecolor=SURF, gridspec_kw=dict(hspace=0.55))
for a in (a1, a2):
    a.set_facecolor(SURF); a.spines[['top', 'right']].set_visible(False); a.grid(axis='y', color='#e6e5e1', lw=0.8)
x = np.exp(u)
a1.plot(x, E, color=BLUE, lw=1.0)
a1.set_xscale('log'); a1.set_xlim(100, 1e8); a1.set_ylim(-0.75, 0.75)
a1.set_title('Gear slippage: Mertens function M(x) ÷ √x, up to 10⁸', loc='left', fontsize=13, color=INK)
a1.set_xlabel('x (log scale)'); a1.set_ylabel('M(x) / √x')
a1.text(1.3e2, 0.63, 'net parity of gear contacts; stays at random-walk size (≤ 0.57 in every decade)', color=INK2, fontsize=10)
Sn = S/S[np.argmin(abs(om - gam[0]))]
a2.plot(om, Sn, color=BLUE, lw=1.4, label='measured spectrum of the slippage')
a2.plot(gam, pred, 'o', ms=8, mfc=ORANGE, mec=SURF, mew=2, label='predicted from ζ alone: 2/|ρ ζ′(ρ)|', zorder=3)
a2.set_xlim(0, 60); a2.set_ylim(0, 1.15)
a2.set_title('Its tones: same pitches as the grinding, volumes set by ζ′ at each zero', loc='left', fontsize=13, color=INK)
a2.set_xlabel('frequency in log x'); a2.set_ylabel('relative strength')
leg = a2.legend(frameon=False, loc='upper right', fontsize=10)
for t in leg.get_texts(): t.set_color(INK2)
fig.savefig('slippage.png', dpi=150, facecolor=SURF, bbox_inches='tight')
