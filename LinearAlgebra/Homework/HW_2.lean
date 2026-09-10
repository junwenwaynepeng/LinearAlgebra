import Mathlib

/-!
# Homework 2 — Solving Systems of Linear Equations
-/


/-!
Exercise 1 — A 2 × 2 system

Solve the system and prove both values.
-/

example (x y : ℝ)
    (h1 : 3 * x + 2 * y = 13)
    (h2 : x - y = 1) :
    x = 3 ∧ y = 2 := by
  sorry


/-!
Exercise 2 — A 3 × 3 system

Solve the system for `x`, `y`, and `z`.
-/

example (x y z : ℝ)
    (h1 : x + 2 * y + z = 7)
    (h2 : 2 * x - y + 3 * z = 6)
    (h3 : 3 * x + y - z = 3) :
    x = 1 ∧ y = 2 ∧ z = 2 := by
  sorry


/-!
Exercise 3 — No solution

Show that these two equations are inconsistent.
-/

example (x y : ℝ)
    (h1 : 2 * x - y = 3)
    (h2 : 4 * x - 2 * y = 8) :
    False := by
  sorry


/-!
Exercise 4 — One step of Gaussian elimination

Prove that the two systems have exactly the same solutions.

Hint: three times the first equation minus the second equation gives
`7y = 11`.
-/

example (x y : ℝ) :
    (x + 2 * y = 5 ∧ 3 * x - y = 4) ↔
    (x + 2 * y = 5 ∧ 7 * y = 11) := by
  sorry


/-!
Exercise 5 — Uniqueness without first finding the solution

Suppose `(x,y)` and `(u,v)` are both solutions of the same system.
Prove that the two solutions are equal.
-/

example (x y u v : ℝ)
    (hxy1 : 4 * x + y = 9)
    (hxy2 : x - 2 * y = -3)
    (huv1 : 4 * u + v = 9)
    (huv2 : u - 2 * v = -3) :
    x = u ∧ y = v := by
  sorry


/-!
Exercise 6 — A free variable

The system has three unknowns but only two independent equations.
Determine `y`, and express `x` in terms of the free variable `z`.
-/

example (x y z : ℝ)
    (h1 : x + y + z = 5)
    (h2 : x - y + z = 1) :
    y = 2 ∧ x = 3 - z := by
  sorry
