# Lean formalization: factorial staircases

Lean 4 proofs of the main algebraic and number-theoretic results of the paper. They are written in Lean 4 (v4.35.0) using Mathlib (v4.35.0).

- `lake build` completes with no errors.
- There are **no `sorry`s**.
- Every theorem depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`); see `axioms_output.txt`.

## Building it

This folder holds the source files only. The first build downloads a compiled Mathlib of about 7 GB.

To rebuild from this folder on any machine, first install elan (https://github.com/leanprover/elan). Then, from this folder:

```bash
lake exe cache get
```
```bash
lake build
```
```bash
lake env lean FactorialStaircases/Axioms.lean
```

The last command prints the axioms each theorem uses.

## Convention

To avoid Lean's truncated subtraction on natural numbers, the files write **n = k + m + 1**:

- `(n − i)!` for i = 1, …, m+1 becomes `(k + j)!` for j = m+1−i = 0, …, m.
- The multiplier n − m becomes k + 1.
- The bracket L_m(n) becomes `bracket k m = Σ_{j ≤ m} (k+j)!`.

So `staircase_identity k m` is the staircase identity for n = k + m + 1, which covers every 0 ≤ m ≤ n − 1.

## Paper results and their Lean names

The paper is still being revised, so results are named by their LaTeX label in `paper/main.tex`, not by number.

| Paper result (label) | Lean name | File |
|---|---|---|
| Staircase identity (`thm:identity`) | `staircase_identity` (with a `decide` check of n = 7, m = 3) | `Basic.lean` |
| Other multipliers, identity part (`thm:family`) | `family_identity`; the extreme case c = n − m is `family_extremal` | `Basic.lean` |
| Left factorial endpoint (`cor:kurepa`) | `left_factorial_endpoint` | `Basic.lean` |
| Mixed-radix identity, over ℤ (`thm:mixed`) | `mixed_radix_identity`; `prodR_id` shows factorials are the case r_k = k | `Basic.lean` |
| Equally spaced coefficients for affine r_k (`cor:affine`, forward direction) | `affine_coefficients` | `Basic.lean` |
| L_m(n) = (n−m−1)! · P_m(n) (section `sec:arith`, "Removing the obvious factor") | `bracket_eq_factorial_mul_cofactor` | `Basic.lean` |
| Rising factorials mod p (`lem:rising`) | `ascFactorial_modEq` | `Basic.lean` |
| Periodicity theorem, general form (`thm:period`) | `cofactor_modEq` | `Basic.lean` |
| Periodicity theorem, derangement form: j ≤ m gives (−1)^j d_j (`thm:period`) | `cofactor_derangement`, using `desc_alt_sum` | `Arithmetic.lean` |
| Kellner's congruence m! · L_m(p) ≡ −d_m (`cor:kellner`) | `kellner` | `Arithmetic.lean` |
| !p ≡ d_{p−1} mod p (`cor:kellner`) | `left_factorial_mod_prime` | `Arithmetic.lean` |
| Kurepa reformulation p ∣ !p ⇔ p ∣ d_{p−1} (`cor:kellner`) | `kurepa_iff` | `Arithmetic.lean` |
| (n − m + 1) ∣ P_m(n) for m ≥ 1 (`cor:gcd`, last claim) | `succ_dvd_cofactor` | `Arithmetic.lean` |
| Gamma-function version, over ℂ (remark `prop:gamma`) | `gamma_staircase` | `Arithmetic.lean` |

`gamma_staircase` assumes y + j + 1 ≠ 0 for j ≤ m, where x = y + m + 1. Those are the only points where Γ(s+1) = sΓ(s) is used.

Derangement numbers come from Mathlib (`numDerangements`), and Wilson's theorem from Mathlib (`ZMod.wilsons_lemma`).

## Not formalized

- **The lexicographic-rank statements.** This covers:
  - `thm:lex` (the remainder is the rank of the prefix reversal);
  - the ranking lemma in `sec:prelim`;
  - the rank part of `thm:family` (the permutation w_{m,c});
  - the rank part of `thm:mixed` (digit strings).

  Mathlib has no ready-made lexicographic ranking of permutations, so these remain checked only by brute-force enumeration (`verification/verify.py`, n ≤ 7).
- **The q-analogue (`thm:q`)**, which counts inversions over a lexicographic interval.
- **`cor:gcd` in full**, which identifies the primes dividing G_m(n). Only the divisibility by n − m + 1 is formalized.
- **The near-Kurepa prime table (odd primes) and the 11563 check.** These are computations, done in `verification/near_kurepa.c` and `verification/near_kurepa.py`.
