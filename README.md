# Factorial staircases

Source files for the expository note *Factorial staircases: a pattern in factorials, explained* by Vaibhav Sanghai.

The note starts from an experimental pattern:

n! = (n − m)·[(n−1)! + … + (n−m−1)!] + [(m−1)(n−1)! + (m−2)(n−2)! + … + 1·(n−m+1)!].

It explains the pattern with the factorial number system, follows it to Kurepa's left factorial, and studies the bracket modulo a prime.

## Contents

| Folder | What it holds |
|---|---|
| `paper/` | LaTeX source (`main.tex`, `references.bib`), the built `main.pdf`, and the scripts that make its figures and tables |
| `verification/` | `verify.py`, which checks every identity and congruence by computer; `near_kurepa.c` and `near_kurepa.py` for the near-Kurepa prime table |
| `lean/` | Lean 4 + Mathlib proofs of the algebraic and number-theoretic results (no `sorry`); see `lean/README.md` |

Appendix B of the paper (Table 4) maps each result to its computer check and its Lean theorem.

## Reproducing

```bash
python3 verification/verify.py
```

`verify.py` needs `sympy` and `mpmath`. Every line it prints should end in `True`.

```bash
cc -O2 -o near_kurepa verification/near_kurepa.c
```
```bash
./near_kurepa 2000000
```

To build the Lean proofs, install [elan](https://github.com/leanprover/elan), then run these from `lean/`:

```bash
lake exe cache get
```
```bash
lake build
```

To build the paper, run these from `paper/`:

```bash
python3 make_figures.py
```
```bash
latexmk -pdf main.tex
```

## Licence

- **Code** (`verification/`, `lean/`, and the scripts `paper/make_figures.py` and `paper/make_tables.py`): MIT License; see `LICENSE`.
- **Paper** (`paper/main.tex`, `paper/references.bib`, `paper/main.pdf`, and the figures and tables): [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); see `paper/LICENSE`.
