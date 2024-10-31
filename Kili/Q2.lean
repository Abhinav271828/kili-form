import Mathlib.Order.Nat
import Mathlib.Data.Nat.Choose.Basic

open Nat

/-
Let $n$ and $k$ be nonnegative integers with $k \leqslant n$. Then
(i ) $\binom{n}{0}=\binom{n}{n}=1$
(ii) $\binom{n}{k}=\binom{n}{n-k}$.
-/

example {n : ℕ} : choose n 0 = 1 := by
  simp
example {n : ℕ} : choose n n = 1 := by
  simp

example {n k : ℕ} (h : k ≤ n) : choose n k = choose n (n - k) := by
  rw [choose_eq_factorial_div_factorial h, choose_eq_factorial_div_factorial (sub_le n k)]
  -- Cancel n! from numerator
  have {x y z : ℕ} (h : x = y) : (z / x = z / y) := by
    rw [h]
  apply this; case h =>
  -- Cancel (n-k)!
  rw [Nat.mul_comm]
  have mul_cancel (x y z : ℕ) (heq : x = y) : (z * x = z * y) := by
        rw [heq]
  apply mul_cancel
  -- Simplify
  rw [Nat.sub_sub_self h]
