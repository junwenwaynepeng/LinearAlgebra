import Mathlib

open Matrix
open scoped BigOperators

/-!
# Homework 3 — Matrices and inverses

This homework is based on the material from Class 1 and Class 2.
In particular, you may use tactics and ideas such as
`intro`, `cases`, `constructor`, `rw`, `simp`, `ext`, `congrArg`,
and `calc`.
-/


/-!
Exercise 1 — Equality of matrices

Two matrices are equal if all of their entries are equal.
Use matrix extensionality to prove the statement below.

Hint: the tactic `ext i j` reduces equality of matrices to equality
of their `(i,j)`-entries.
-/

example {m n : Type*}
    (A B : Matrix m n ℂ)
    (h : ∀ i j, A i j = B i j) :
    A = B := by
  sorry


/-!
Exercise 2 — Commuting with a diagonal matrix

Let U_i be the matrix whose `(i,i)`-entry is 1 and whose other
entries are 0. Suppose that A commutes with U_i.
Show that every entry in row i, away from the diagonal, is zero.

This is one of the main steps in the proof of Proposition 2.2.

Hint:
1. Apply the matrix equality to the `(i,j)`-entry using `congrArg`.
2. Simplify the two matrix products using
   `Matrix.mul_apply` and `Matrix.single`.
-/

example {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n)
    (hij : i ≠ j)
    (hcomm :
      A * Matrix.single i i 1 =
        Matrix.single i i 1 * A) :
    A i j = 0 := by
  sorry


/-!
For the remaining exercises, use the following definitions from Class 2.
-/

def IsInverse
    {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A * B = 1 ∧ B * A = 1


def IsInvertible
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ B, IsInverse A B


/-!
Exercise 3 — Inverse is a symmetric relation

If B is an inverse of A, prove that A is an inverse of B.

Hint: unfold `IsInverse` and use the two parts of the conjunction.
-/

example {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : IsInverse A B) :
    IsInverse B A := by
  sorry


/-!
Exercise 4 — An inverse gives invertibility

Suppose B is an inverse of A. Prove that B is invertible.

Hint: after unfolding `IsInvertible`, you must provide a matrix
that serves as the inverse.
-/

example {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : IsInverse A B) :
    IsInvertible B := by
  sorry


/-!
Exercise 5 — Cancellation by an invertible matrix

Let A be an invertible matrix. Suppose

    A * B = A * C.

Prove that B = C.

For ordinary numbers, we might try to "divide both sides by A".
For matrices, division is not available. Instead, use the fact that
A has an inverse.

Hint:
1. Unfold `IsInvertible` to obtain an inverse D of A.
2. Unfold `IsInverse` to obtain `D * A = 1`.
3. Multiply the equation `A * B = A * C` by D on the left.
4. Use associativity of matrix multiplication.
-/

example {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsInvertible A)
    (h : A * B = A * C) :
    B = C := by
  sorry

/-!
Exercise 6 — Inverse of a product

Suppose B is an inverse of A and D is an inverse of C.
Prove that D * B is an inverse of A * C.

In ordinary notation, this says

    (AC)⁻¹ = C⁻¹A⁻¹.

Do not use matrix inverse notation. Work directly from the definition
of `IsInverse` and use associativity of matrix multiplication.
-/

example {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsInverse A B)
    (hD : IsInverse C D) :
    IsInverse (A * C) (D * B) := by
  sorry
