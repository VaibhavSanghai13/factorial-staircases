"""Generate the data tables included by main.tex.

Run from the paper/ folder:  python3 make_tables.py
Writes tables/lex_example.tex and tables/dm_values.tex.
"""
from itertools import permutations
from math import factorial as F
from pathlib import Path

OUT = Path(__file__).parent / "tables"
OUT.mkdir(exist_ok=True)


def remainder(n, m):
    """R_m(n) = n! - (n-m) * [(n-1)! + ... + (n-m-1)!]."""
    return F(n) - (n - m) * sum(F(n - i) for i in range(1, m + 2))


# Worked example: all permutations of {1,2,3,4} in lexicographic order,
# with the prefix reversal w_3 = 3214 marked.
n, m = 4, 3
w = tuple(list(range(m, 0, -1)) + list(range(m + 1, n + 1)))
perms = sorted(permutations(range(1, n + 1)))
cells = []
for r, p in enumerate(perms):
    word = "".join(map(str, p))
    if p == w:
        word = r"\mathbf{" + word + "}"
    cells.append(f"${r}$ & ${word}$")
cols = 4
rows = len(cells) // cols
lines = [r"\begin{tabular}{" + "|".join(["rl"] * cols) + "}"]
for row in range(rows):
    lines.append(" & ".join(cells[row + k * rows] for k in range(cols)) + r" \\")
lines.append(r"\end{tabular}")
(OUT / "lex_example.tex").write_text("\n".join(lines) + "\n")
assert perms.index(w) == remainder(n, m) == 14

# Table of R_m(n) for small m and n.
ms = range(1, 7)
ns = range(2, 11)
lines = [r"\begin{tabular}{r|" + "r" * len(ms) + "}",
         "$n$ & " + " & ".join(f"$m={m}$" for m in ms) + r" \\ \hline"]
for n in ns:
    row = [f"${remainder(n, m)}$" if m <= n - 1 else "" for m in ms]
    lines.append(f"${n}$ & " + " & ".join(row) + r" \\")
lines.append(r"\end{tabular}")
(OUT / "dm_values.tex").write_text("\n".join(lines) + "\n")
print("wrote", *sorted(p.name for p in OUT.iterdir()))
