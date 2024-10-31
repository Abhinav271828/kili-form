import Mathlib
open Finset

/- Write and prove the following theorem in Lean 4:
If $a$ and $r$ are real numbers and $r \neq 1$, then
(1.1)
$$
\sum_{j=0}^{n} a r^{j}=a+a r+a r^{2}+\cdots+a r^{n}=\frac{a r^{n+1}-a}{r-1} .
$$
-/

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) :
    ∑ i ∈ range (n+1), a * r^i = (a * r^(n+1) - a) / (r-1) := by
  induction n with
  | zero =>
      rw [sum_range_one, pow_zero, pow_one, mul_one]
      nth_rewrite 3 [←mul_one a]
      rw [←mul_sub a r 1]
      rw [mul_div_assoc, div_self (sub_ne_zero.mpr h), mul_one]
  | succ n ih =>
      rw [sum_range_succ, ih]
      -- Take a out in LHS
      nth_rewrite 2 [←mul_one a]
      rw [←mul_sub]
      rw [mul_div_assoc]
      rw [←mul_add]
      -- Take a out in RHS
      nth_rewrite 3 [←mul_one a]
      rw [←mul_sub]
      rw [mul_div_assoc]
      -- Cancel a
      have mul_cancel (x y z : ℝ) (heq : x = y) : (z * x = z * y) := by
        rw [heq]
      apply mul_cancel ((r ^ (n + 1) - 1) / (r - 1) + r ^ (n + 1)) ((r ^ (n + 1 + 1) - 1) / (r - 1)) a
      -- Take (r - 1) out in LHS
      have mul_div (x y : ℝ) (h : y ≠ 0) : x = x * y / y := by
        rw [mul_div_assoc, div_self h, mul_one]
      rw [mul_div (r ^ (n + 1)) (r - 1) (sub_ne_zero.mpr h)]
      rw [←add_div]
      -- Cancel (r-1)
      have div_cancel (x y z : ℝ) (heq : x = y) : (x / z = y / z) := by
        rw [heq]
      apply div_cancel
      rw [←mul_div (r ^ (n + 1)) (r - 1) (sub_ne_zero.mpr h)]
      -- Simplify
      rw [mul_sub]
      simp
      rw [←pow_succ]
