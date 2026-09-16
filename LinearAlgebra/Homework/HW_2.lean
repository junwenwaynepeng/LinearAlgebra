import Mathlib
import LinearAlgebra.CourseTools
/-! -/
open scoped BigOperators

/-!
# Homework 2 — Proof Language in Lean

This homework is based on the new Class 2 lecture note.
The goal is to practice recognizing the logical structure of a statement
and choosing an appropriate Lean proof style.

You may use tactics and ideas from Class 2, including
`intro`, `exact`, `apply`, `assumption`, `constructor`, `refine`,
`cases`, `rcases`, `rintro`, `left`, `right`, `use`, `rw`, `subst`,
`congrArg`, `by_cases`, `contradiction`, `have`, `suffices`,
`simp`, `norm_num`, `ring`, `linarith`, `funext`, `ext`, and `fin_cases`.
-/


/-!
## Exercise 1 — Equality in two proof styles

Assume `x = y`. Prove that applying the same expression to `x` and `y`
gives the same result.

Prove the statement twice:

* in (a), use `rw`;
* in (b), use `congrArg`.

The mathematical statement is the same, but the proof styles are different.
-/

-- (a) Use `rw`.
example (x y z : ℝ) (h : x = y) :
    (x + z) ^ 2 = (y + z) ^ 2 := by
  sorry


-- (b) Use `congrArg`.
example (x y z : ℝ) (h : x = y) :
    (x + z) ^ 2 = (y + z) ^ 2 := by
  sorry


/-!
## Exercise 2 — Conjunction and disjunction

Prove the distributive implication

    P ∧ (Q ∨ R)  →  (P ∧ Q) ∨ (P ∧ R).

Try to expose the structure of the hypothesis using `rintro` or `rcases`,
then split into the two possible cases of `Q ∨ R`.
-/

example (P Q R : Prop) :
    P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  sorry


/-!
## Exercise 3 — Extracting an existential witness

Suppose there exists an object satisfying both `P` and `Q`.
Show that there exists an object satisfying `P`, and there exists
an object satisfying `Q`.

The same witness may be used for both existential statements.
-/

example {α : Type*} (P Q : α → Prop) :
    (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  sorry


/-!
## Exercise 4 — Proof by cases

Prove

    P ∨ (P → Q).

Hint: use `by_cases h : P`.

* If `P` is true, prove the left side of the disjunction.
* If `P` is false, prove `P → Q` by assuming `P` and obtaining a
  contradiction.
-/

example (P Q : Prop) :
    P ∨ (P → Q) := by
  sorry


/-!
## Exercise 5 — Equality of concrete matrices

The two matrices below are written using different expressions,
but they define the same matrix.

Prove that they are equal.

Suggested strategy:

1. use `ext row col`;
2. use `fin_cases` on the row and column indices;
3. finish each scalar identity with `ring` or another suitable tactic.
-/

def M₁ (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(x + 1) ^ 2, 2 * x + 2;
     x - x,         3]


def M₂ (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x ^ 2 + 2 * x + 1, 2 * (x + 1);
     0,                 3]


example (x : ℝ) : M₁ x = M₂ x := by
  sorry


/-!
## Exercise 6 — Induction and finite sums

Prove the identity

    1 + 7 + 19 + ... = n^3,

where the `k`th summand is

    3k² + 3k + 1.

This is similar in structure to the induction example from class,
but it is a different identity.

Useful observation:

    3k² + 3k + 1 = (k + 1)^3 - k^3.

You may want to use `Finset.sum_range_succ` in the induction step.
-/

example (n : ℕ) :
    Finset.sum (Finset.range n)
      (fun k => 3 * k^2 + 3 * k + 1)
      = n^3 := by
  sorry
