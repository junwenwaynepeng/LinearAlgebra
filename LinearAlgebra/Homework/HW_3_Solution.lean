import Mathlib

open Matrix
open scoped BigOperators

/-!
# Homework 2 — Matrices and inverses

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
  ext i j
  exact h i j


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
  let U : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.single i i 1
  have hentry : (A * U) i j = (U * A) i j :=
    congrArg (fun M => M i j) hcomm
  simpa [Matrix.mul_apply, U, Matrix.single, hij] using hentry.symm

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
  unfold IsInverse at h
  cases h with
  | intro hAB hBA =>
      constructor
      · exact hBA
      · exact hAB


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
  unfold IsInvertible
  unfold IsInverse at *
  use A
  cases h with
  | intro hAB hBA =>
      constructor
      · exact hBA
      · exact hAB

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
  unfold IsInvertible at hA
  unfold IsInverse at hA
  obtain ⟨D, hDA, hAD⟩ := hA
  have h1 : D * (A * B) = D * (A * C) := by
    rw [h]
  have h2 : (D * A) * B = (D * A) * C := by
    simpa [Matrix.mul_assoc] using h1
  rw [hAD] at h2
  simpa using h2


/-
  unfold IsInvertible at hA
  unfold IsInverse at hA
  cases hA with
  | intro D hD =>
      cases hD with
      | intro hDA hAD =>
          have h1 : D * (A * B) = D * (A * C) := by rw [h]
          have h2 : (D * A) * B = (D * A) * C := by
            calc
              (D * A) * B = D * (A * B) := by rw [Matrix.mul_assoc]
              _ = D * (A * C) := by rw [h]
              _ = (D * A) * C := by rw [Matrix.mul_assoc]
          rw [hAD] at h2
          rw [Matrix.one_mul] at h2
          rw [Matrix.one_mul] at h2
          -- simp at h2
          exact h2
-/




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
  unfold IsInverse at *
  obtain ⟨hAB, hBA⟩ := hB
  rcases hD with ⟨hCD, hDC⟩ --obtain ⟨hCD, hDC⟩ := hB
  constructor
  calc
    (A * C) * (D * B) = A * (C * D) * B := by
      simp only [Matrix.mul_assoc]
    _ = A * 1 * B := by rw [hCD]
    _ = A * B := by simp
    _ = 1 := hAB
  calc
    (D * B) * (A * C) = D * (B * A) * C := by
      simp only [Matrix.mul_assoc]
    _ = D * 1 * C := by rw [hBA]
    _ = D * C := by simp
      _ = 1 := hDC

/-  cases hB with
  | intro hAB hBA =>
      cases hD with
      | intro hCD hDC =>
          calc
            (A * C) * (D * B) = A * (C * D) * B := by
              simp only [Matrix.mul_assoc]
            _ = A * 1 * B := by rw [hCD]
            _ = A * B := by simp
            _ = 1 := hAB
  cases hB with
  | intro hAB hBA =>
      cases hD with
      | intro hCD hDC =>
          calc
            (D * B) * (A * C) = D * (B * A) * C := by
              simp only [Matrix.mul_assoc]
            _ = D * 1 * C := by rw [hBA]
            _ = D * C := by simp
              _ = 1 := hDC
-/
/-cases hB with
| intro hAB hBA =>
  cases hD with
  | intro hCD hDC =>
    constructor
    · calc
        (A * C) * (D * B) = A * (C * D) * B := by
          simp only [Matrix.mul_assoc]
        _ = A * 1 * B := by rw [hCD]
        _ = A * B := by simp
        _ = 1 := hAB
    · calc
        (D * B) * (A * C) = D * (B * A) * C := by
          simp only [Matrix.mul_assoc]
        _ = D * 1 * C := by rw [hBA]
        _ = D * C := by simp
        _ = 1 := hDC-/
