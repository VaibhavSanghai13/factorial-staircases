import FactorialStaircases.Basic
import FactorialStaircases.Arithmetic

/-!
# Axiom audit

Each theorem below should depend only on Lean's standard axioms
`propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`).
-/

open FactorialStaircases

#print axioms staircase_identity
#print axioms family_identity
#print axioms family_extremal
#print axioms left_factorial_endpoint
#print axioms mixed_radix_identity
#print axioms affine_coefficients
#print axioms ascFactorial_modEq
#print axioms bracket_eq_factorial_mul_cofactor
#print axioms cofactor_modEq
#print axioms desc_alt_sum
#print axioms cofactor_derangement
#print axioms kellner
#print axioms left_factorial_mod_prime
#print axioms kurepa_iff
#print axioms succ_dvd_cofactor
#print axioms gamma_staircase
