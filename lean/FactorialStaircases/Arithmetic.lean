import FactorialStaircases.Basic

/-!
# Factorial staircases: congruences modulo primes and the Gamma function

Derangement numbers, Kellner's congruence and Kurepa's reformulation (section `sec:arith` of the
paper), the divisibility of the cofactor by `n - m + 1`, and the Gamma-function version of the
staircase identity (remark `prop:gamma`). Convention as in `Basic.lean`: `n = k + m + 1`.
-/

open Finset Nat

namespace FactorialStaircases

/-- `j(j-1)⋯(k+1) = (k+1)(k+2)⋯j`: both equal `j!/k!`. -/
theorem descFactorial_sub_eq_ascFactorial (j k : ℕ) (hk : k ≤ j) :
    j.descFactorial (j - k) = (k + 1).ascFactorial (j - k) := by
  have h1 : (j - (j - k))! * j.descFactorial (j - k) = j ! :=
    Nat.factorial_mul_descFactorial (Nat.sub_le j k)
  have h2 : k ! * (k + 1).ascFactorial (j - k) = (k + (j - k))! :=
    Nat.factorial_mul_ascFactorial k (j - k)
  rw [show j - (j - k) = k by omega] at h1
  rw [show k + (j - k) = j by omega] at h2
  exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k) (h1.trans h2.symm)

theorem neg_one_pow_sub (j k : ℕ) (hk : k ≤ j) :
    (-1 : ℤ) ^ (j - k) = (-1) ^ j * (-1) ^ k := by
  have h : (-1 : ℤ) ^ j = (-1) ^ (j - k) * (-1) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [h, mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- The alternating sum of falling factorials is a signed derangement number:
`Σ_{t ≤ j} (-1)^t j(j-1)⋯(j-t+1) = (-1)^j d_j`. -/
theorem desc_alt_sum (j : ℕ) :
    ∑ t ∈ range (j + 1), (-1 : ℤ) ^ t * (j.descFactorial t : ℤ)
      = (-1) ^ j * (numDerangements j : ℤ) := by
  rw [numDerangements_sum, Finset.mul_sum,
    ← Finset.sum_range_reflect (fun t => (-1 : ℤ) ^ t * (j.descFactorial t : ℤ)) (j + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ j := by
    rw [Finset.mem_range] at hk
    omega
  rw [show j + 1 - 1 - k = j - k by omega, neg_one_pow_sub j k hk',
    descFactorial_sub_eq_ascFactorial j k hk']
  ring

/-- **Periodicity (`thm:period`), derangement form.** If `a + j ≡ 0 (mod p)` and `j ≤ m`, then
the cofactor `P = Σ_{t ≤ m} a(a+1)⋯(a+t-1)` satisfies `P ≡ (-1)^j d_j (mod p)`. -/
theorem cofactor_derangement (p a j m : ℕ) (h : ((a + j : ℕ) : ZMod p) = 0) (hj : j ≤ m) :
    ((cofactor a m : ℕ) : ZMod p) = (-1) ^ j * (numDerangements j : ZMod p) := by
  rw [cofactor_modEq p a j m h]
  have hsub : ∑ t ∈ range (m + 1), (-1 : ZMod p) ^ t * ((j.descFactorial t : ℕ) : ZMod p)
      = ∑ t ∈ range (j + 1), (-1 : ZMod p) ^ t * ((j.descFactorial t : ℕ) : ZMod p) := by
    symm
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro t ht hnot
    rw [Finset.mem_range] at ht hnot
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp
  rw [hsub]
  have := congrArg (Int.cast : ℤ → ZMod p) (desc_alt_sum j)
  push_cast at this
  exact this

/-- **Kellner's congruence (`cor:kellner`).** For a prime `p` and `m < p`,
`m! · ((p-1)! + (p-2)! + ⋯ + (p-m-1)!) ≡ -d_m (mod p)`, i.e. `L_m(p) ≡ -d_m / m!`. -/
theorem kellner (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m < p) :
    ((m ! * bracket (p - m - 1) m : ℕ) : ZMod p) = -(numDerangements m : ZMod p) := by
  have hkm : p - m - 1 + 1 + m = p := by omega
  have h0 : ((p - m - 1 + 1 + m : ℕ) : ZMod p) = 0 := by
    rw [hkm]
    exact ZMod.natCast_self p
  have hcof := cofactor_derangement p (p - m - 1 + 1) m m h0 le_rfl
  have hasc := ascFactorial_modEq p (p - m - 1 + 1) m h0 m
  rw [Nat.descFactorial_self] at hasc
  have hw : (((p - m - 1)! * (p - m - 1 + 1).ascFactorial m : ℕ) : ZMod p) = -1 := by
    rw [Nat.factorial_mul_ascFactorial, show p - m - 1 + m = p - 1 by omega]
    exact ZMod.wilsons_lemma p
  rw [bracket_eq_factorial_mul_cofactor]
  push_cast at hw hcof hasc ⊢
  rw [hcof]
  rw [hasc] at hw
  linear_combination (numDerangements m : ZMod p) * hw

/-- **Left factorial mod p (`cor:kellner`).** `!p = 0! + 1! + ⋯ + (p-1)! ≡ d_{p-1} (mod p)`. -/
theorem left_factorial_mod_prime (p : ℕ) [hp : Fact p.Prime] :
    ((∑ j ∈ range p, j ! : ℕ) : ZMod p) = (numDerangements (p - 1) : ZMod p) := by
  have h2 := hp.out.two_le
  have h := kellner p (p - 1) (by omega)
  have hb : bracket (p - (p - 1) - 1) (p - 1) = ∑ j ∈ range p, j ! := by
    rw [show p - (p - 1) - 1 = 0 by omega, bracket, show p - 1 + 1 = p by omega]
    simp
  rw [hb] at h
  push_cast at h
  rw [ZMod.wilsons_lemma p] at h
  push_cast
  linear_combination -h

/-- **Kurepa's conjecture, reformulated.** `p ∣ !p` if and only if `p ∣ d_{p-1}`. -/
theorem kurepa_iff (p : ℕ) [Fact p.Prime] :
    p ∣ ∑ j ∈ range p, j ! ↔ p ∣ numDerangements (p - 1) := by
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, left_factorial_mod_prime]

/-- `k+2` divides `(k+1)(k+2)⋯(k+t)` once `t ≥ 2`. -/
theorem succ_succ_dvd_ascFactorial (k t : ℕ) (ht : 2 ≤ t) : (k + 2) ∣ (k + 1).ascFactorial t := by
  induction t, ht using Nat.le_induction with
  | base =>
    rw [Nat.ascFactorial_succ]
    exact ⟨(k + 1).ascFactorial 1, by ring⟩
  | succ t ht ih =>
    rw [Nat.ascFactorial_succ]
    exact Dvd.dvd.mul_left ih _

/-- **Divisibility by n - m + 1 (`cor:gcd`, last claim).** For `m ≥ 1`, `n - m + 1 = k + 2` divides the cofactor
`P_m(n) = L_m(n) / (n-m-1)!`. -/
theorem succ_dvd_cofactor (k m : ℕ) (hm : 1 ≤ m) : (k + 2) ∣ cofactor (k + 1) m := by
  induction m, hm using Nat.le_induction with
  | base =>
    have : cofactor (k + 1) 1 = k + 2 := by
      rw [cofactor, Finset.sum_range_succ, Finset.sum_range_one, Nat.ascFactorial_zero,
        Nat.ascFactorial_succ, Nat.ascFactorial_zero]
      omega
    rw [this]
  | succ m hm ih =>
    rw [cofactor, Finset.sum_range_succ, ← cofactor]
    exact Nat.dvd_add ih (succ_succ_dvd_ascFactorial k (m + 1) (by omega))

/-- **Gamma-function version (remark `prop:gamma`).** With `x = y + m + 1`,
`Γ(x+1) = (x-m)·Σ_{i=1}^{m+1} Γ(x-i+1) + Σ_{i=1}^{m-1} (m-i)·Γ(x-i+1)`,
provided `Γ(s+1) = sΓ(s)` may be used at `s = y+1, …, y+m+1`. -/
theorem gamma_staircase (y : ℂ) (m : ℕ) (h : ∀ j ≤ m, y + j + 1 ≠ 0) :
    Complex.Gamma (y + m + 2) = (y + 1) * ∑ j ∈ range (m + 1), Complex.Gamma (y + j + 1)
      + ∑ j ∈ Finset.Ico 1 (m + 1), ((j : ℂ) - 1) * Complex.Gamma (y + j + 1) := by
  induction m with
  | zero =>
    have h0 := h 0 le_rfl
    simp only [Nat.cast_zero, add_zero] at h0
    simp only [Nat.cast_zero, add_zero, zero_add, Finset.sum_range_one, Finset.Ico_self,
      Finset.sum_empty]
    rw [show y + 2 = (y + 1) + 1 by ring, Complex.Gamma_add_one _ h0]
  | succ m ih =>
    have ih' := ih (fun j hj => h j (by omega))
    have hs := h (m + 1) le_rfl
    have e1 : y + ((m + 1 : ℕ) : ℂ) + 2 = (y + m + 2) + 1 := by push_cast; ring
    have e2 : y + ((m + 1 : ℕ) : ℂ) + 1 = y + m + 2 := by push_cast; ring
    have hs' : y + (m : ℂ) + 2 ≠ 0 := by
      rw [← e2]
      exact hs
    rw [Finset.sum_range_succ, Finset.sum_Ico_succ_top (by omega), e1, e2,
      Complex.Gamma_add_one _ hs']
    push_cast
    linear_combination ih'

end FactorialStaircases
