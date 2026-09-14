import ?

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

open ?


/-!
## Exercise 1 — Getting used to Lean syntax

Prove the following two elementary statements.

The first one should require almost no work.
For the second one, let Lean check the arithmetic for you.
-/

example (x : ℝ) : x = x := by
  sorry

example : (7 : ℝ) + 5 = 12 := by
  sorry


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

example : H₂ 0 2 = 5 := by
  sorry

example : H₂ 1 0 = -3 := by
  sorry


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

example : H₃A = H₃B := by
  sorry


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

example : Matrix.RowEquivalent H₄A H₄B := by
  sorry


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

example : Matrix.RowEquivalent H₅A H₅B := by
  sorry
