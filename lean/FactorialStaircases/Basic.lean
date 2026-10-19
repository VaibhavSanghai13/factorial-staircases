import Mathlib

/-!
# Factorial staircases

Machine-checked statements from the note "Factorial staircases: a pattern in factorials,
explained". Results are cited by their LaTeX label in `paper/main.tex`.

To avoid truncated subtraction we write `n = k + m + 1`. Then `n - i` for `i = 1, ..., m + 1`
becomes `k + j` for `j = m + 1 - i = 0, ..., m`, the multiplier `n - m` becomes `k + 1`, and
the bracket `L_m(n) = Σ_{i=1}^{m+1} (n-i)!` becomes `Σ_{j ≤ m} (k+j)!`.
-/

open Finset Nat

namespace FactorialStaircases

/-! ## 1. The staircase identity (`thm:identity`) -/

/-- The bracket `L_m(n)` with `n = k + m + 1`: `k! + (k+1)! + ... + (k+m)!`. -/
def bracket (k m : ℕ) : ℕ := ∑ j ∈ range (m + 1), (k + j)!

/-- The staircase remainder with `n = k + m + 1`: `Σ_j (j-1)(k+j)!`.
The terms `j = 0, 1` vanish (truncated subtraction makes `0 - 1 = 0`), which matches
`Σ_{i=1}^{m-1} (m-i)(n-i)!` after the substitution `j = m + 1 - i`. -/
def staircase (k m : ℕ) : ℕ := ∑ j ∈ range (m + 1), (j - 1) * (k + j)!

/-- **Staircase identity (`thm:identity`).** `n! = (n-m)·L_m(n) + Σ_{i=1}^{m-1}(m-i)(n-i)!`, with `n = k + m + 1`. -/
theorem staircase_identity (k m : ℕ) :
    (k + m + 1)! = (k + 1) * bracket k m + staircase k m := by
  induction m with
  | zero => simp [bracket, staircase, Nat.factorial_succ]
  | succ m ih =>
    have hF : (k + (m + 1) + 1)! = (k + m + 2) * (k + m + 1)! := by
      rw [show k + (m + 1) + 1 = (k + m + 1) + 1 by omega, Nat.factorial_succ]
    have hB : bracket k (m + 1) = bracket k m + (k + m + 1)! := by
      rw [bracket, Finset.sum_range_succ, ← bracket, show k + (m + 1) = k + m + 1 by omega]
    have hS : staircase k (m + 1) = staircase k m + m * (k + m + 1)! := by
      rw [staircase, Finset.sum_range_succ, ← staircase,
        show k + (m + 1) = k + m + 1 by omega, show m + 1 - 1 = m by omega]
    rw [hF, hB, hS]
    nlinarith [ih]

/-- Sanity check against Table 1: `7! = 4·(3!+4!+5!+6!) + (2·6! + 1·5!)` (n = 7, m = 3). -/
example : (7 : ℕ)! = 4 * bracket 3 3 + staircase 3 3 := by decide

/-! ## 2. The two-parameter family (`thm:family`) -/

/-- **Other multipliers (`thm:family`).** For any multiplier `c ≤ n - m = k + 1`,
`n! = c·L_m(n) + Σ_{j=1}^{m}(k+j-c)(k+j)! + (k+1-c)·k!`. -/
theorem family_identity (k m c : ℕ) (hc : c ≤ k + 1) :
    (k + m + 1)! = c * bracket k m
      + ∑ j ∈ Finset.Ico 1 (m + 1), (k + j - c) * (k + j)! + (k + 1 - c) * k ! := by
  induction m with
  | zero =>
    have h0 : c * k ! + (k + 1 - c) * k ! = (k + 1) * k ! := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' hc]
    simp only [bracket, zero_add, Finset.sum_range_one, add_zero, Finset.Ico_self,
      Finset.sum_empty, Nat.factorial_succ]
    exact h0.symm
  | succ m ih =>
    have hF : (k + (m + 1) + 1)! = (k + m + 2) * (k + m + 1)! := by
      rw [show k + (m + 1) + 1 = (k + m + 1) + 1 by omega, Nat.factorial_succ]
    have hB : bracket k (m + 1) = bracket k m + (k + m + 1)! := by
      rw [bracket, Finset.sum_range_succ, ← bracket, show k + (m + 1) = k + m + 1 by omega]
    have hI : ∑ j ∈ Finset.Ico 1 (m + 1 + 1), (k + j - c) * (k + j)!
        = ∑ j ∈ Finset.Ico 1 (m + 1), (k + j - c) * (k + j)!
          + (k + m + 1 - c) * (k + m + 1)! := by
      rw [Finset.sum_Ico_succ_top (by omega), show k + (m + 1) = k + m + 1 by omega]
    have hsplit : c * (k + m + 1)! + (k + m + 1 - c) * (k + m + 1)!
        = (k + m + 1) * (k + m + 1)! := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' (by omega)]
    rw [hF, hB, hI]
    nlinarith [ih, hsplit]

/-- The original staircase is the extreme case `c = n - m = k + 1` of the family. -/
theorem family_extremal (k m : ℕ) :
    (k + m + 1)! = (k + 1) * bracket k m
      + ∑ j ∈ Finset.Ico 1 (m + 1), (j - 1) * (k + j)! := by
  have h := family_identity k m (k + 1) le_rfl
  rw [Nat.sub_self, zero_mul, add_zero] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  omega

/-- **Left factorial endpoint (`cor:kurepa`).** `n! = !n + Σ_{j=1}^{n-1} (j-1)·j!`,
where `!n = Σ_{j<n} j!` (here `n = m + 1`, i.e. `k = 0`). -/
theorem left_factorial_endpoint (m : ℕ) :
    (m + 1)! = ∑ j ∈ range (m + 1), j ! + ∑ j ∈ Finset.Ico 1 (m + 1), (j - 1) * j ! := by
  have h := family_extremal 0 m
  simpa [bracket] using h

/-! ## 3. Mixed-radix staircases (`thm:mixed`) -/

/-- The product `a_k = r_1 r_2 ⋯ r_k` of growth factors. -/
def prodR (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => r (k + 1) * prodR r k

theorem prodR_succ (r : ℕ → ℕ) (k : ℕ) : prodR r (k + 1) = r (k + 1) * prodR r k := rfl

/-- Factorials are the mixed-radix product with growth factors `r_k = k`. -/
theorem prodR_id (n : ℕ) : prodR (fun k => k) n = n ! := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prodR_succ, ih, Nat.factorial_succ]

/-- **Mixed-radix identity (`thm:mixed`)** (over `ℤ`, so negative coefficients such as for `r_k = b` are allowed).
With `n = k + m + 1`:
`a_n = r_{k+1}·Σ_{j=0}^{m} a_{k+j} + Σ_{j=1}^{m} (r_{k+j+1} - r_{k+1} - 1)·a_{k+j}`. -/
theorem mixed_radix_identity (r : ℕ → ℕ) (k m : ℕ) :
    (prodR r (k + m + 1) : ℤ) = (r (k + 1) : ℤ) * ∑ j ∈ range (m + 1), (prodR r (k + j) : ℤ)
      + ∑ j ∈ Finset.Ico 1 (m + 1),
          ((r (k + j + 1) : ℤ) - r (k + 1) - 1) * (prodR r (k + j) : ℤ) := by
  induction m with
  | zero => simp [prodR_succ]
  | succ m ih =>
    have hP : prodR r (k + (m + 1) + 1) = r (k + m + 2) * prodR r (k + m + 1) := by
      rw [show k + (m + 1) + 1 = (k + m + 1) + 1 by omega, prodR_succ]
    have e1 : k + (m + 1) = k + m + 1 := by omega
    have e2 : k + m + 1 + 1 = k + m + 2 := by omega
    rw [hP, Finset.sum_range_succ, Finset.sum_Ico_succ_top (by omega)]
    simp only [e1, e2]
    push_cast
    linear_combination ih

/-- **Equally spaced coefficients (`cor:affine`)** (affine growth factors `r_k = α k + β`): the staircase coefficients are
`α j - 1`, independent of `n` (here `j = m + 1 - i`). -/
theorem affine_coefficients (α β k j : ℕ) :
    ((α * (k + j + 1) + β : ℕ) : ℤ) - ((α * (k + 1) + β : ℕ) : ℤ) - 1 = (α : ℤ) * j - 1 := by
  push_cast; ring

/-! ## 4. Congruences modulo primes (`sec:arith`) -/

/-- **Rising factorials mod p (`lem:rising`).** If `a ≡ -j (mod p)` then `a(a+1)⋯(a+i-1) ≡ (-1)^i · j(j-1)⋯(j-i+1) (mod p)`. -/
theorem ascFactorial_modEq (p : ℕ) (a j : ℕ) (h : ((a + j : ℕ) : ZMod p) = 0) (i : ℕ) :
    ((a.ascFactorial i : ℕ) : ZMod p) = (-1) ^ i * ((j.descFactorial i : ℕ) : ZMod p) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.ascFactorial_succ, Nat.descFactorial_succ]
    push_cast
    rw [ih]
    rcases Nat.lt_or_ge j i with hij | hij
    · have hd : j.descFactorial i = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hij
      simp [hd]
    · have h1 : ((a + i : ℕ) : ZMod p) = -((j - i : ℕ) : ZMod p) := by
        have : ((a + i : ℕ) : ZMod p) + ((j - i : ℕ) : ZMod p) = ((a + j : ℕ) : ZMod p) := by
          rw [← Nat.cast_add]; congr 1; omega
        rw [h] at this
        exact eq_neg_of_add_eq_zero_left this
      push_cast at h1
      rw [h1]
      ring

/-- The cofactor `P_m(n) = Σ_{t=0}^{m} (n-m)(n-m+1)⋯(n-m+t-1)`, written with `a = n - m`. -/
def cofactor (a m : ℕ) : ℕ := ∑ t ∈ range (m + 1), a.ascFactorial t

/-- `L_m(n) = (n-m-1)! · P_m(n)`. With `n = k + m + 1`:
`Σ_{j≤m} (k+j)! = k! · Σ_{j≤m} (k+1)(k+2)⋯(k+j)`. -/
theorem bracket_eq_factorial_mul_cofactor (k m : ℕ) :
    bracket k m = k ! * cofactor (k + 1) m := by
  rw [bracket, cofactor, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (Nat.factorial_mul_ascFactorial k j).symm

/-- **Periodicity (`thm:period`), general form.** If `a + j ≡ 0 (mod p)` then
`P ≡ Σ_{t ≤ m} (-1)^t j(j-1)⋯(j-t+1) (mod p)`; terms with `t > j` vanish. -/
theorem cofactor_modEq (p a j m : ℕ) (h : ((a + j : ℕ) : ZMod p) = 0) :
    ((cofactor a m : ℕ) : ZMod p) =
      ∑ t ∈ range (m + 1), (-1) ^ t * ((j.descFactorial t : ℕ) : ZMod p) := by
  rw [cofactor, Nat.cast_sum]
  exact Finset.sum_congr rfl fun t _ => ascFactorial_modEq p a j h t

end FactorialStaircases
