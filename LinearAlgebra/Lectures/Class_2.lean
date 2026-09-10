import Mathlib

/-!
# Class 2 — Solving Systems of Linear Equations in Lean

The main idea is simple:

* each equation is a hypothesis;
* `rw` can be used for substitution;
* `linarith` can perform linear elimination;
* a system with no solution can be proved by deriving `False`;
* row operations can be expressed as logical equivalences;
* Lean can also prove uniqueness or describe a free variable.
-/


/-!
## 1. Rearranging one linear equation

`linarith` can rearrange a linear equation for us.
-/

example (x y : ℝ)
    (h : x + y = 7) :
    y = 7 - x := by
  linarith [h]


/-!
## 2. Solving a 2 × 2 system by substitution

We first solve the first equation for `y`, substitute it into the second
with `rw`, and then recover `y`.
-/

example (x y : ℝ)
    (h1 : 2 * x + y = 11)
    (h2 : x - y = 1) :
    x = 4 ∧ y = 3 := by
  have hy : y = 11 - 2 * x := by
    linarith [h1]

  rw [hy] at h2

  have hx : x = 4 := by
    linarith [h2]

  rw [hx] at hy
  norm_num at hy

  exact ⟨hx, hy⟩


/-!
## 3. Letting `linarith` do the elimination

For a linear system over `ℝ`, `linarith` can often eliminate the variables
directly.
-/

example (x y : ℝ)
    (h1 : 3 * x + 2 * y = 16)
    (h2 : x - y = 2) :
    x = 4 ∧ y = 2 := by
  constructor
  · linarith [h1, h2]
  · linarith [h1, h2]


/-!
## 4. A system with three variables
-/

example (x y z : ℝ)
    (h1 : x + y + z = 6)
    (h2 : 2 * x - y + z = 3)
    (h3 : x + 2 * y - z = 2) :
    x = 1 ∧ y = 2 ∧ z = 3 := by
  constructor
  · linarith [h1, h2, h3]
  · constructor
    · linarith [h1, h2, h3]
    · linarith [h1, h2, h3]


/-!
## 5. An inconsistent system

If two equations contradict each other, there is no solution.
In Lean, "there is a contradiction" means that we can prove `False`.
-/

example (x y : ℝ)
    (h1 : x + y = 3)
    (h2 : 2 * x + 2 * y = 7) :
    False := by
  linarith [h1, h2]


/-!
## 6. Row operations preserve the solution set

A row operation should not change which values solve the system.
We can express "the two systems have exactly the same solutions" using `↔`.

### Multiplying an equation by a nonzero scalar
-/

example (x y : ℝ) :
    (x - 2 * y = 3) ↔ (3 * x - 6 * y = 9) := by
  constructor
  · intro h
    linarith [h]
  · intro h
    linarith [h]


/-!
### Replacing one row by the sum of two rows

From

    x + y = 5
    2x - y = 1

adding the two equations gives `3x = 6`.
-/

example (x y : ℝ) :
    (x + y = 5 ∧ 2 * x - y = 1) ↔
    (x + y = 5 ∧ 3 * x = 6) := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · exact h1
    · linarith [h1, h2]
  · rintro ⟨h1, h2⟩
    constructor
    · exact h1
    · linarith [h1, h2]


/-!
## 7. A redundant equation

The second equation below contains no new information: it is just three
times the first equation.
-/

example (x y : ℝ) :
    (x - 2 * y = 4 ∧ 3 * x - 6 * y = 12) ↔
    (x - 2 * y = 4) := by
  constructor
  · intro h
    exact h.1
  · intro h
    constructor
    · exact h
    · linarith [h]


/-!
## 8. Uniqueness of a solution

If `(x,y)` and `(u,v)` both solve a system with a unique solution,
then the two pairs must be equal.
-/

example (x y u v : ℝ)
    (hxy1 : 2 * x + y = 7)
    (hxy2 : x - y = 2)
    (huv1 : 2 * u + v = 7)
    (huv2 : u - v = 2) :
    x = u ∧ y = v := by
  constructor
  · linarith [hxy1, hxy2, huv1, huv2]
  · linarith [hxy1, hxy2, huv1, huv2]


/-!
## 9. A free variable

This system has two equations and three unknowns.  It does not determine
all three variables.  Lean can still tell us exactly what is forced by
the equations.
-/

example (x y z : ℝ)
    (h1 : x + y + z = 6)
    (h2 : x - y + z = 2) :
    y = 2 ∧ x = 4 - z := by
  constructor
  · linarith [h1, h2]
  · linarith [h1, h2]
