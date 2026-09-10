import Mathlib
open scoped BigOperators

example (x : ℝ) : x = x := by --proof x=x
  rfl   -- rfl is a tactic that proves goals of the form a = a

example (x y : ℝ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]

example (P : Prop) : P → P := by --proof p implies p
  intro w -- w is a variable that represents the proof of P
  exact w -- exact is a tactic that proves the goal by using the proof w

example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  · exact p
  · exact q

example (P Q : Prop) (p : P) : P ∨ Q := by
  · left
    exact p

example (P Q : Prop) (h : P ∧ Q) : P := by
  /-cases h with
  | intro p q => exact p-/
  /-obtain ⟨ p,q⟩ := h
  exact p-/
  rcases h with ⟨ p, q⟩
  exact p

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  /-cases h with
  | inl p => --exact Or.inr p
      right
      exact p
  | inr q => --exact Or.inl q
      left
      exact q-/
  /-obtain p | q := h
  · right
    exact p
  · left
    exact q-/
  rcases h with p | q
  · right
    exact p
  · left
    exact q

-- Every proposition is either true or not true.
example (P : Prop) : P ∨ ¬P := by
  by_cases h : P
  · left
    exact h
  · right
    exact h

/-
Proof that if P implies Q, then not Q implies not P

proof.
Assume P implies Q, Q is false, and P is true.
We want to show that these assumption are not coherent (False).
A.  If we can get Q, then we have false
    This is eactly the consequence of P implies Q when P is true.
B.  Since P is true, so Q is true, we have false.
C.  We have Q because P is true and P implies Q.
    We then arrive contradiction because we have Q and not Q.
-/
example (P Q : Prop) : ( P → Q) → (¬Q → ¬P) := by
  unfold Not --We don't need to unfold Not, but it is good to know that it is defined as P → False
  intro h1 h2 p -- assume P implies Q, Q implies false (not Q), and P
  apply h2      -- Give the proof of Q to h2: Q → False, which will give us a proof of False
  exact h1 p
  --exact h2 (h1 p)    -- Q is true because P is true and P implies Q


example (P Q : Prop) : ( P → Q) → (¬Q → ¬P) := by
  intro h1 h2 p  -- assume P implies Q, not Q, and P
  have q : Q := h1 p -- We have Q because P is true and P implies Q
  contradiction -- We have a contradiction because we have Q and not Q

example (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  intro h1 p -- assume not Q and P
  apply h1   -- Give the proof of Q to h1: Q → False, which will give us a proof of False
  exact h p  -- Q is true because P is true and P implies Q

example (P Q : Prop) : (P ∧ ¬P) → Q := by
  intro h
  obtain ⟨p, notp⟩ := h
  --rcases h with ⟨p, notp⟩
  --contradiction
  exfalso
  exact notp p --p notp
  /-cases h with
  | intro p notp =>
      exfalso
      exact notp p-/
  /-
  cases h with
  | intro p notp => contradiction -- We have a contradiction because we have P and not P
  -/

example (x y a b : ℝ) (h1 : x < y) (h2 : a < b) : x + a < y + b := by
  linarith [h1, h2] -- linarith is a tactic that solves linear inequalities
  -- apply add_lt_add h1 h2

example (G : Type) (hg : Group G) (a b c : G) : a * a⁻¹ * 1 * b = b * c * c⁻¹ := by
  simp

/-
Assume x is a natural number.
Proof that x ≤ 1 + x.

proof. We have a theorem which says that a≤b with a and b ∈ ℝ
if and only if there is a c ∈ ℝ such that a+c=b.
So, instead of proving x ≤ 1+x, we can show that there exists a such c ∈ ℝ.
Let c=1. We have the desired equality with some linear arithmetics.
-/
example (x : Nat) : x ≤ 1 + x := by
  rw[le_iff_exists_add]
  -- le_iff_exists_add is a theorem that states that x ≤ y if and only if there exists a natural number z such that x + z = y
  use 1  -- use 1 as the natural number z
  linarith  -- 1+X = X+1 is a simple arithmetic fact that can be proved by linarith

example (x : Nat) : x ≤ 1 + x := by
  induction x with
  | zero => simp --linarith
  | succ x ih => linarith

example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => linarith
  | succ n ih => linarith

-- The sum of the first n odd numbers is n^2.
example (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
