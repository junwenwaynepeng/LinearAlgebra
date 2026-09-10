import Mathlib

open scoped BigOperators


/-!
# Homework 1
-/
/-!
Exercise 1 — Composition of implications

Assume P implies Q and Q implies R.
Prove that P implies R.
-/

example (P Q R : Prop) :
    (P → Q) → (Q → R) → (P → R) := by
  sorry


/-!
Exercise 2 — Proof by cases and contradiction

Assume P or Q.
Prove that if P is false, then Q must be true.
-/

example (P Q : Prop) :
    (P ∨ Q) → (¬P → Q) := by
  sorry


/-!
Exercise 3 — Extracting information from a conjunction

Suppose that whenever P is true, both Q and R are true.
Prove separately that P implies Q and P implies R.
-/

example (P Q R : Prop) :
    (P → Q ∧ R) → ((P → Q) ∧ (P → R)) := by
  sorry


/-!
Exercise 4 — Solving a system of linear equations

Use the hypotheses to prove both values of x and y.
-/

example (x y : ℝ)
    (h1 : 2 * x + y = 11)
    (h2 : x - y = 1) :
    x = 4 ∧ y = 3 := by
  sorry


/-!
Exercise 5 — Induction and finite sums

Prove the identity

1 + 7 + 19 + ... = n^3,

where the kth summand is 3k² + 3k + 1.

Notice that

3k² + 3k + 1 = (k + 1)^3 - k^3.
-/

example (n : ℕ) :
    Finset.sum (Finset.range n)
      (fun k => 3 * k^2 + 3 * k + 1)
      = n^3 := by
  sorry
