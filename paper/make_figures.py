"""Generate the figures included by main.tex.

Run from anywhere:  python3 make_figures.py   (needs matplotlib)
Writes figures/*.pdf next to this file.
"""
from itertools import permutations
from math import factorial as F
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = Path(__file__).parent / "figures"
OUT.mkdir(exist_ok=True)

# Palette: reference categorical slots 1-3 (validated all-pairs), ink and greys.
BLUE, ORANGE = "#2a78d6", "#eb6834"
INK, INK2, MUTED, GRID = "#0b0b0b", "#52514e", "#8a8984", "#e4e3df"

plt.rcParams.update({
    "font.family": "serif", "mathtext.fontset": "cm", "font.size": 9,
    "axes.edgecolor": MUTED, "axes.linewidth": 0.6, "axes.labelcolor": INK2,
    "xtick.color": INK2, "ytick.color": INK2, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.axisbelow": True,
    "axes.spines.top": False, "axes.spines.right": False,
    "legend.frameon": False, "savefig.bbox": "tight", "savefig.pad_inches": 0.03,
})


# ---------------------------------------------------------------------------
# Figure 1: the lexicographic tree of S_4, cut at the prefix reversal w_m.
# ---------------------------------------------------------------------------
def tree_panel(ax, n, m):
    w = tuple(list(range(m, 0, -1)) + list(range(m + 1, n + 1)))
    perms = sorted(permutations(range(1, n + 1)))
    cut = perms.index(w)
    status = lambda leaves: ("below" if max(leaves) < cut else
                             "above" if min(leaves) >= cut else "path")
    color = {"below": ORANGE, "above": BLUE, "path": INK}
    depth = n - 1                      # the last letter is forced
    nodes = {}
    for r, p in enumerate(perms):
        for d in range(depth + 1):
            nodes.setdefault(p[:d], []).append(r)
    xy = {pre: (sum(ls) / len(ls), depth - len(pre)) for pre, ls in nodes.items()}
    for pre, ls in nodes.items():
        if len(pre) == 0:
            continue
        st = "path" if w[:len(pre)] == pre else status(ls)
        (x0, y0), (x1, y1) = xy[pre[:-1]], xy[pre]
        ax.plot([x0, x1], [y0, y1], color=color[st],
                lw=2.2 if st == "path" else 1.1, solid_capstyle="round", zorder=2)
        if len(pre) < depth:
            ax.text(x1, y1 + 0.13, str(pre[-1]), ha="center", va="bottom",
                    fontsize=8, color=INK2, zorder=4,
                    bbox=dict(boxstyle="round,pad=0.12", fc="white", ec="none"))
    for r, p in enumerate(perms):
        st = "path" if r == cut else ("below" if r < cut else "above")
        ax.scatter([r], [0], s=26 if r == cut else 14, color=color[st],
                   edgecolors="white", linewidths=1.0, zorder=3)
        ax.text(r, -0.22, "".join(map(str, p)), rotation=90, ha="center", va="top",
                fontsize=7.5, color=INK if r == cut else INK2,
                fontweight="bold" if r == cut else "normal")
    ax.scatter([xy[()][0]], [depth], s=14, color=INK, zorder=3)
    ax.set_xlim(-0.8, len(perms) - 0.2)
    ax.set_ylim(-1.35, depth + 0.45)
    ax.axis("off")
    ax.set_title(rf"$n={n}$, $m={m}$, $w_{m}={''.join(map(str, w))}$: "
                 rf"{cut} below, {len(perms) - cut} at or above",
                 fontsize=9, color=INK, loc="left")


fig, ax = plt.subplots(figsize=(6.4, 2.45))
tree_panel(ax, 4, 3)
fig.tight_layout()
fig.savefig(OUT / "lex_tree.pdf")
plt.close(fig)

# ---------------------------------------------------------------------------
# Figure 2: choices at each step along w_m (n = 8, m = 5): the staircase below,
# the constant multiplier above.
# ---------------------------------------------------------------------------
n, m = 8, 5
steps = list(range(1, m + 1))
below = [m - i for i in steps]
above = [n - m] * m
fig, ax = plt.subplots(figsize=(4.6, 2.6))
ax.bar(steps, below, width=0.5, color=ORANGE, edgecolor="white", linewidth=1.5,
       label=r"smaller unused values: $m-i$")
ax.bar(steps, above, width=0.5, bottom=below, color=BLUE, edgecolor="white",
       linewidth=1.5, label=r"larger unused values: $n-m$")
ax.set_xticks(steps)
ax.set_xticklabels([f"step {i}\nletter {m - i + 1}" for i in steps], fontsize=7.5)
ax.set_ylabel("number of choices")
ax.set_yticks(range(0, n))
ax.grid(axis="x", visible=False)
ax.legend(loc="upper right", fontsize=7.5, handlelength=1.2)
ax.set_ylim(0, n + 1.6)
fig.savefig(OUT / "choices.pdf")
plt.close(fig)

# ---------------------------------------------------------------------------
# Figure 3: where p = 11 divides P_m(n) = L_m(n)/(n-m-1)!  (Proposition 5.2).
# The stripes are the diagonals m - n = j (mod 11) with 11 | d_j, j in {1,5,9}.
# ---------------------------------------------------------------------------
import numpy as np
from matplotlib.colors import ListedColormap
p, N = 11, 56
grid = np.full((N, N + 1), np.nan)          # rows m = 0..N-1, columns n = 0..N
for n in range(1, N + 1):
    for m in range(0, n):
        P = sum(F(n - i) for i in range(1, m + 2)) // F(n - m - 1)
        grid[m, n] = 1.0 if P % p == 0 else 0.0
fig, ax = plt.subplots(figsize=(5.0, 3.6))
cmap = ListedColormap(["#e9ecf1", BLUE])
cmap.set_bad("white")
ax.imshow(np.ma.masked_invalid(grid), origin="lower", cmap=cmap, vmin=0, vmax=1,
          interpolation="nearest", aspect="auto", extent=(-0.5, N + 0.5, -0.5, N - 0.5))
ax.grid(False)
ax.set_xlabel(r"$n$")
ax.set_ylabel(r"$m$")
ax.set_xlim(0.5, N + 0.5)
ax.set_ylim(-0.5, N - 0.5)
ax.text(2, N - 3, r"stripes: $m-n\equiv 1,5,9\ (\mathrm{mod}\ 11)$" "\n" r"since $11\mid d_1,\,d_5,\,d_9$",
        ha="left", va="top", fontsize=7.5, color=INK2,
        bbox=dict(boxstyle="round,pad=0.25", fc="white", ec=GRID))
fig.savefig(OUT / "periodicity.pdf")
plt.close(fig)

print("wrote", *sorted(p.name for p in OUT.iterdir()))
