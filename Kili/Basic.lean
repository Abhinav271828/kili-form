import Mathlib

/-
Write and prove the following theorem in Lean 4:
Sum of numbers from i = 0 to n is n*(n+1)/2)
-/

open Finset BigOperators

#check Nat.mul_right_inj

#check Nat.mul_div_assoc

--  Nat.even_mul_succ_self

example (n : ℕ) : ∑ i in (Finset.range (n + 1)), i = n * (n + 1) / 2 :=
  by induction n with
  | zero => simp
  | succ n ih =>
  rw [Finset.sum_range_succ]
  rw [ih]
  apply (Nat.mul_right_inj two_ne_zero).1
  rw [← Nat.mul_div_assoc _ (even_iff_two_dvd.1 (Nat.even_mul_succ_self (n+1)))]
  rw [mul_add]
  rw [← Nat.mul_div_assoc _ (even_iff_two_dvd.1 (Nat.even_mul_succ_self (n)))]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
  ring
