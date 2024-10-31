import Mathlib.Data.PNat.Basic
open Nat

/-
We define a function recursively for all positive integers $n$
by $f(1)=1$, $f(2)=5$, and
for $n>2, f(n+1)=f(n)+2 f(n-1)$.

Show that $f(n)=$ $2^{n}+(-1)^{n}$,
using the second principle of mathematical induction.
-/


def f : PNat → Int
  | ⟨1, _⟩ => 1
  | n@⟨v@(k+2), h⟩ =>
    have hn : n = ⟨k+2, h⟩ := by assumption
    have hv : v = k + 2 := by assumption
    have h' : k + 2 ≥ 2 := by
      apply Nat.succ_le_succ
      apply Nat.succ_le_succ
      exact Nat.zero_le k
    match k with
      | 0 => 5
      | k@(k' + 1) =>
          have hk : k = k' + 1 := by assumption
          have h_k_gt_zero : k > 0 := by
            rw [hk]
            exact Nat.succ_pos k'
          have h_lt : n > ⟨k + 1, Nat.succ_pos k⟩ := by
            rw [hn]
            apply Nat.succ_lt_succ; simp
            rw [hk]
            apply Nat.succ_lt_succ; simp
          have h_lt' : n > ⟨k, h_k_gt_zero⟩ := by
            rw [hn]; simp
            rw [PNat.mk_lt_mk, hk]; simp
          f ⟨k + 1, Nat.succ_pos k⟩ + 2 * f ⟨k, h_k_gt_zero⟩
  termination_by n => n.val
  decreasing_by simp_wf; simp_all; simp; rw [hk]; simp

theorem f_one_eq : f ⟨1, Nat.succ_pos 0⟩ = 1 := by rw [f]
theorem f_one_eq' : f 1 = 1 := by apply f_one_eq

theorem f_two_eq : f ⟨2, Nat.succ_pos 1⟩ = 5 := by rw [f]
theorem f_two_eq' : f 2 = 5 := by apply f_two_eq

theorem f_rec : ∀ n, f ⟨n.val + 2, Nat.succ_pos (n.val + 1)⟩ = f ⟨n.val + 1, Nat.succ_pos n.val⟩ + 2 * f n := by
  sorry

theorem f_ih (n : PNat) (ih : ∀ m, m < n + 2 → f m = 2 ^ m.val + (-1) ^ m.val)
  : f ⟨n.val + 2, Nat.succ_pos (n.val + 1)⟩ = 2 ^ n.val + (-1) ^ n.val := by
  rw [f_rec n]
  have h' : n.val + 1 < n.val + 2 := by
    apply Nat.succ_lt_succ
    simp
  rw [ih ⟨n.val + 1, Nat.succ_pos n.val⟩ h']
  have h'' : n.val < n.val + 2 := by
    simp
  rw [ih n h'']
  simp
  rw [←Nat.succ_eq_add_one]
  sorry
