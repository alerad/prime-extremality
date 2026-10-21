"""Publication figure.

fig_exchange.pdf : E_T(v) and its running integral for T={2,3}, {2,3,5}
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams.update({
    "font.family": "serif",
    "mathtext.fontset": "cm",
    "font.size": 9,
    "axes.labelsize": 9,
    "axes.titlesize": 9,
    "legend.fontsize": 8,
    "xtick.labelsize": 8,
    "ytick.labelsize": 8,
    "axes.linewidth": 0.6,
    "lines.linewidth": 1.2,
})

# ----------------------------------------------------------------------
# Figure 1: the exchange mechanism
# ----------------------------------------------------------------------
def E(T, v):
    out = np.ones_like(v)
    for t in T:
        out = out * (1.0 - v**t)
    return out - (1.0 - v)


v = np.linspace(0.0, 1.0, 801)
fig, axes = plt.subplots(1, 2, figsize=(6.6, 2.5), sharey=True)
for ax, T in zip(axes, [(2, 3), (2, 3, 5)]):
    e = E(T, v)
    G = np.concatenate([[0.0], np.cumsum((e[1:] + e[:-1]) / 2) * (v[1] - v[0])])
    ax.axhline(0.0, color="0.6", lw=0.5)
    ax.plot(v, e, "-", color="C0", label=r"$E_T(v)$")
    ax.plot(v, G, "--", color="C3", label=r"$\int_0^v E_T(u)\,du$")
    ax.set_title(r"$T=\{" + ",".join(str(t) for t in T) + r"\}$")
    ax.set_xlabel(r"$v$")
    ax.set_xlim(0, 1)
axes[0].legend(frameon=False, loc="upper left")
fig.tight_layout(pad=0.4)
fig.savefig("fig_exchange.pdf")
fig.savefig("fig_exchange.png", dpi=160)
plt.close(fig)
print("fig_exchange written")
