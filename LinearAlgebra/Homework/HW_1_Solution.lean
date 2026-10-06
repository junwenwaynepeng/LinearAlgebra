import Mathlib
import LinearAlgebra.Lectures.Class_1

/-!
# Homework 1 — Lean Basics and Gaussian Elimination

This homework is based only on the material from `Class_1_Revised.lean`.

The exercises are arranged from easy to difficult.
Replace each `sorry` with Lean code.

You may use the commands and tactics introduced in class, including:

* `rfl`
* `norm_num`
* `funext`
* `fin_cases`
* `row_swap`
* `row_scale`
* `row_add`
* transitivity of `Matrix.RowEquivalent`

Remember that Lean numbers rows and columns starting from `0`.
-/

open Matrix


/-!
## Exercise 1 — Getting used to Lean syntax

Prove the following two elementary statements.

The first one should require almost no work.
For the second one, let Lean check the arithmetic for you.

**Example 1** For any real number x, we have x = x.
*proof.* This is true by reflexivity of equality.
-/

example (x : ℝ) : x = x := by
  rfl

/-
**Example 2** The sum of 7 and 5 is 12.
*proof.* This is true by arithmetic.
-/

example : (7 : ℝ) + 5 = 12 := by
  norm_num


/-!
## Exercise 2 — Reading entries of a matrix

Consider the integer matrix

    [  2   0   5 ]
    [ -3   4   1 ]

Prove the two statements below.

Remember:

* row `0` is the first row;
* row `1` is the second row;
* column `0` is the first column.
-/

def H₂ : Matrix (Fin 2) (Fin 3) ℤ :=
  !![ 2, 0, 5;
     -3, 4, 1]

/-**Example 3 and 4** The entry of H₂ at row 0 (resp. row 1) and column 2 (resp. column 0)
is 5 (resp. -3).
*proof.* This is true by the definition of H₂.
-/

example : H₂ 0 2 = 5 := by
  rfl

example : H₂ 1 0 = -3 := by
  rfl


/-!
## Exercise 3 — Equality of matrices

The following two real matrices are mathematically equal, although their
entries are written differently.

Prove that `H₃A = H₃B` by checking the entries one at a time.

Hint: the matrix-equality example in Class 1 used
`funext`, `fin_cases`, and `norm_num`.
-/

def H₃A : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 : ℝ) + 1, 3;
     2 * 2,        7 - 2]

def H₃B : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 3;
     4, 5]


/-**Example 5** The matrices H₃A and H₃B are equal.
*proof.*
ext i j : To prove that two matrices are equal, we check that every entry is equal.
fin_cases i : We consider two cases for the row index i: i = 0 and i = 1.
fin_cases j : We consider two cases for the column index j: j = 0 and j = 1.
norm_num [H₃A, H₃B] : In each case, we use Lean to check that the entries of H₃A and H₃B are equal.
-/


example : H₃A = H₃B := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [H₃A, H₃B]

/-!
## Exercise 4 — Combining row operations

Start with

    [ 1   2   3 ]
    [ 0   2   4 ]

and reach

    [ 1   0  -1 ]
    [ 0   1   2 ]

The intermediate matrix `H₄A₁` is provided for you.

Prove that `H₄A` and `H₄B` are row equivalent.
Your proof should:

1. prove the first elementary row operation;
2. prove the second elementary row operation;
3. combine the two proofs using transitivity.
-/

def H₄A : Matrix (Fin 2) (Fin 3) ℝ :=
  !![1, 2, 3;
     0, 2, 4]

-- After R₂ ← (1/2)R₂

def H₄A₁ : Matrix (Fin 2) (Fin 3) ℝ :=
  !![1, 2, 3;
     0, 1, 2]

def H₄B : Matrix (Fin 2) (Fin 3) ℝ :=
  !![1, 0, -1;
     0, 1,  2]

/-**Example 6** The matrices H₄A and H₄B are row equivalent.
*proof.* H₄A ~ H₄A₁ by R₂ ← (1/2)R₂, and H₄A₁ ~ H₄B by R₁ ← R₁ - 2R₂. By transitivity, H₄A ~ H₄B.
-/

example : Matrix.RowEquivalent H₄A H₄B := by
  calc
    H₄A = H₄A₁ := by
      row_scale H₄A => H₄A₁, 1, (1 / 2 : ℝ)
    _ = H₄B := by
      row_add H₄A₁ => H₄B, 0, 1, (-2 : ℝ)


/-!
## Exercise 5 — Design a complete Gaussian elimination

This is the challenge problem.

Start with the augmented matrix

    [ 0   2   2 | 4 ]
    [ 1   1   0 | 2 ]
    [ 0   1  -1 | 0 ]

and reduce it to

    [ 1   0   0 | 1 ]
    [ 0   1   0 | 1 ]
    [ 0   0   1 | 1 ]

Prove that the two matrices are row equivalent.

Unlike Exercise 4, the intermediate matrices are NOT provided.
You must decide which row operations to perform and create any intermediate
matrices you need, following the style of the Gaussian-elimination example
from Class 1.

Your proof should use all three kinds of elementary row operations:

* a row swap;
* scaling a row by a nonzero number;
* adding a multiple of one row to another row.

You may define intermediate matrices above the proof, or introduce them in
another clear way.
-/

def H₅A : Matrix (Fin 3) (Fin 4) ℝ :=
  !![0, 2,  2, 4;
     1, 1,  0, 2;
     0, 1, -1, 0]

def H₅B : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 0, 0, 1;
     0, 1, 0, 1;
     0, 0, 1, 1]

/-**Example 7** The matrices H₅A and H₅B are row equivalent.

We first define the intermediate matrices H₅A₁, ⋯, H₅A₇, and then prove that H₅A ~ H₅B by a sequence of row operations.
*proof.* We have H₅A ~ H₅A₁ by R₁ ↔ R₂;
H₅A₁ ~ H₅A₂ by R₂ ← (1/2)R₂;
H\₅A₂ ~ H₅A₃ by R₃ ← R₃ - R₂;
H₅A₃ ~ H₅A₄ by R₂ ← R₂ - R₃;
H₅A₄ ~ H₅A₅ by R₁ ← R₁ - R₂;
H₅A₅ ~ H₅A₆ by R₂ ← R₂ - R₁;
H₅A₆ ~ H₅B by R₁ ← R₁ - R₂.
By transitivity, H₅A ~ H₅B.
-/

def H₅A₁ : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 1, 0, 2;
     0, 2, 2, 4;
     0, 1, -1, 0]

def H₅A₂ : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 1, 0, 2;
     0, 1, 1, 2;
     0, 1, -1, 0]

def H₅A₃ : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 1, 0, 2;
     0, 1, 1, 2;
     0, 0, -2, -2]

def H₅A₄ : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 1, 0, 2;
     0, 1, 1, 2;
     0, 0, 1, 1]

def H₅A₅ : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 0, -1, 0;
     0, 1, 1, 2;
     0, 0, 1, 1]

def H₅A₆ : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 0, -1, 0;
     0, 1, 0, 1;
     0, 0, 1, 1]

def H₅A₇ : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 0, 0, 1;
     0, 1, 0, 1;
     0, 0, 1, 1]

example : Matrix.RowEquivalent H₅A H₅B := by
  calc
    H₅A = H₅A₁ := by
      row_swap H₅A => H₅A₁, 0, 1
    _ = H₅A₂ := by
      row_scale H₅A₁ => H₅A₂, 1, (1 / 2 : ℝ)
    _ = H₅A₃ := by
      row_add H₅A₂ => H₅A₃, 2, 1, (-1 : ℝ)
    _ = H₅A₄ := by
      row_add H₅A₃ => H₅A₄, 1, 2, (-1 : ℝ)
    _ = H₅A₅ := by
      row_add H₅A₄ => H₅A₅, 0, 1, (1 : ℝ)
    _ = H₅A₆ := by
      row_add H₅A₅ => H₅A₆, 1, 0, (-1 : ℝ)
    _ = H₅B := by
      row_add H₅A₆ => H₅B, 0, 1, (-1 : ℝ)
