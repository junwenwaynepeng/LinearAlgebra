import Mathlib
import LinearAlgebra.CourseTools

open scoped BigOperators

/-!
# Homework 2 — Proof Language in Lean

This homework is based on the Class 2 lecture note.
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
  rw [h]

/-
**Statement:** If x = y, then (x + z)^2 = (y + z)^2.

*proof:* We can rewrite (x + z)^2 using the equality x = y.
-/

-- (b) Use `congrArg`.
example (x y z : ℝ) (h : x = y) :
    (x + z) ^ 2 = (y + z) ^ 2 := by
  exact congrArg (fun t => (t + z) ^ 2) h

/-
*proof:* We can apply the function t↦(t+z)^2 to both sides of the equality x = y.
-/

/-
Other proof styles are possible. For example,
The following tactics solve the goal.
  `subst h`
  `simp`
-/

/-!
## Exercise 2 — Conjunction and disjunction

Prove the distributive implication

    P ∧ (Q ∨ R)  →  (P ∧ Q) ∨ (P ∧ R).

Try to expose the structure of the hypothesis using `rintro` or `rcases`,
then split into the two possible cases of `Q ∨ R`.
-/

example (P Q R : Prop) :
    P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro h
  rcases h with ⟨hP, hQR⟩
  rcases hQR with hQ | hR
  · left
    exact ⟨hP, hQ⟩
  · right
    exact ⟨hP, hR⟩

/-
**Statement:** Let P, Q, and R be propositions.
If P is true and either Q or R is true, then either (P and Q) is true or (P and R) is true.

*proof:* Let assume (`h`:) P ∧ (Q ∨ R) is true.
Then we have P is true (`hP`) and either Q or R is true (`hQR`).
Since Q ∨ R is true, we have two cases: either Q is true (`hQ`) or R is true (`hR`).
* If Q is true, we claim that (P ∧ Q) is true. Indeed, we have P is true (`hP`) and Q is true (`hQ`).
  Therefore, (P ∧ Q) is true.
* If R is true, we claim that (P ∧ R) is true. Indeed, we have P is true (`hP`) and R is true (`hR`).
  Therefore, (P ∧ R) is true.
-/

/-!
## Exercise 3 — Extracting an existential witness

Suppose there exists an object satisfying both `P` and `Q`.
Show that there exists an object satisfying `P`, and there exists
an object satisfying `Q`.

The same witness may be used for both existential statements.
-/

example {α : Type*} (P Q : α → Prop) :
    (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  intro h
  obtain ⟨x, hPx, hQx⟩ := h
  refine ⟨?_, ?_⟩
  · use x
  · use x

/-
**Statement:** Let α be a type, and let P and Q be properties on α.
If there exists an object x of type α such that P x and Q x are both true,
then there exists an object y of type α such that P y is true,
and there exists an object z of type α such that Q z is true.

*proof:* Let assume (`h`:) there exists an object x of type α such that P x and Q x are both true.
Then we have an object `x` such that P x is true (`hPx`) and Q x is true (`hQx`).
To show the goal, we need to show that there exists an object y of type α such that P y is true (the first `?_`),
and there exists an object z of type α such that Q z is true (the second `?_`).
We can use the same witness `x` for both existential statements.

**Remarks:** In lean, `(P : α → Prop)` means each takes an x : α and returns a proposition: P x.
So they are often called *predicates* on α
-/

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
  by_cases hP : P
  · left
    exact hP
  · right
    intro hP'
    contradiction

/-
**Statement:** Let P and Q be propositions. Then either P is true, or if P is true then Q is true.

*proof:* We consider two cases: either P is true (`hP`) or P is false (`¬hP`).
* If P is true, then the left side of the disjunction is true.
  Therefore, P ∨ (P → Q) is true.
* If P is false, then we need to show that P → Q is true.
  To prove P → Q, we assume P is true (`hP'`)
  and obtain a contradiction. Therefore, P → Q is true,
  and hence P ∨ (P → Q) is true.
-/


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
  ext i j
  fin_cases i<;> fin_cases j<;> simp [M₁, M₂] <;> ring

/-
**Statement:** Let x be a real number. Then the matrices M₁ x and M₂ x are equal.

**proof:* To prove that two matrices are equal, we check that every entry is equal.
We consider two cases for the row index i: i = 0 and i = 1
We consider two cases for the column index j: j = 0 and j = 1
In each case, we use Lean to check that the entries of M₁ x and M₂ x are equal.
-/


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
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring


/-
**Statement:** Let n be a natural number.
Then the sum of the first n terms of the sequence 1, 7, 19, ..., (3k² + 3k + 1), ...
is equal to n^3.

*proof:* We prove the statement by induction on n.
* Base case: n = 0. The sum of the first 0 terms is 0, and 0^3 = 0.
  Therefore, the statement is true for n = 0.
* Induction step: Assume the statement is true for some n ∈ ℕ. We need to show it is true for n + 1.
  By the definition of the sum, we have
  ∑_{k=0}^{n} (3k² + 3k + 1) = n^3.
  Adding the (n+1)th term to both sides, we get
  ∑_{k=0}^{n+1} (3k² + 3k + 1) = n^3 + (3(n+1)² + 3(n+1) + 1).
  Simplifying the right-hand side, we obtain
  n^3 + 3(n+1)² + 3(n+1) + 1 = (n+1)^3.
  Therefore, the statement is true for n + 1.
-/
