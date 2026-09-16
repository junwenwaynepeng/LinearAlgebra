import Mathlib
import LinearAlgebra.CourseTools

/-!
# Class 1 — Getting Started with Lean and Gaussian Elimination

## Goals for today

1. Install Lean and Visual Studio Code.
2. Clone and update the course repository with GitHub.
3. Learn how to interact with Lean using `#check` and `#eval`.
4. Learn how Lean represents a matrix.
5. See one very small proof.
6. Preview how Lean checks equality of matrices.
7. Use the three elementary row operations.
8. Verify a complete Gaussian elimination in Lean.

The goal of the first class is to **use Lean successfully**.
We will explain more of the proof language in Class 2.
-/

open Matrix


/-!
## 0. Setup: Lean, VS Code, and GitHub

### Install

You need:

* Git
* Visual Studio Code
* the official **Lean 4** extension for VS Code
* Lean installed through `elan`

See the repository `README.md` for platform-specific installation instructions.

### Clone the course repository

Run these commands in a terminal:

```text
git clone https://github.com/junwenwaynepeng/LinearAlgebra.git
cd LinearAlgebra
lake exe cache get
lake build
code .
```

Clone the repository only once.

### Updating the course

For later updates, run:

```text
./update_course.sh
```

On Windows with Git Bash:

```text
bash update_course.sh
```

### Where should I write my own code?

Instructor-maintained files are stored in:

```text
LinearAlgebra/Lectures/
LinearAlgebra/Homework/
```

Put your own work in:

```text
MyWork/
```

If Lean does not recognize a newly updated library file, use this order:

1. Save the library file.
2. Run `lake build`.
3. Restart the Lean server in VS Code.
-/


/-!
## 1. First interaction with Lean

`#check` asks Lean:

> What kind of object is this?

`#eval` asks Lean:

> What does this computable expression evaluate to?
-/

#check 3
#check (3 : ℝ)

#eval (2 + 3 : Nat)
#eval (3 : Int) ^ 4

/-!
## 2. A matrix in Lean

`Matrix (Fin 2) (Fin 3) ℤ` means a `2 × 3` integer matrix.

For now, you do not need to understand the implementation of `Fin`.
Just remember that Lean counts from `0`.
-/

def M : Matrix (Fin 2) (Fin 3) ℤ :=
  !![1, 2, 3;
     4, 5, 6]

#check M
#check M 0 1

#eval M 0 0
#eval M 0 1
#eval M 1 2


/-!
## 3. A first proof

The general shape is

```text
example : statement := by
  proof
```

`rfl` proves an equality that is true by definition.

`norm_num` proves straightforward numerical arithmetic.

`constructor` splits the goal P ∧ Q to two subgoals P and Q

`linarith` proves straightforward linear arithmetic

`rw [h1] at h2` rewrties the hypothesis h2 using hypothesis h1
-/

example (x : ℝ) : x = x := by
  rfl

example : (2 : ℝ) + 3 = 5 := by
  norm_num

example (x y : ℝ) (eq1 : 2 * x + y = 5) (eq2 : x - y = 1) :
    x = 2 ∧ y = 1 := by
  constructor <;> linarith

example (x y z : ℝ) (eq1 : 2 * x + y + z = 4)
(eq2 : x - y + 2 * z = -1)
(eq3 : x - z = 3) :
    x = 2 ∧ y = 1 ∧ z = -1 := by
  constructor
  · linarith
  · constructor <;> linarith

example (x y : ℝ) (eq1 : x - y = 4) (eq2 : x - y = 5) : false :=by
  linarith

example (x y : ℝ) (eq1 : x - y = 4) (eq2 : x - y = 5) : false := by
  rw [eq2] at eq1
  norm_num at eq1

/-!
## 4. Preview: equality of matrices

A matrix is, internally, a function of a row and a column.

To prove two matrices are equal, we can check that every entry is equal.

Do not worry about every tactic in this example yet.
We will return to `funext`, `fin_cases`, and `norm_num` in Class 2.
-/

def C : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 2;
     3, 4]

def D : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 2;
     3, 4]

example : C = D := by
  funext row col
  fin_cases row <;> fin_cases col <;>
    norm_num [C, D]


/-!
## 5. Elementary row operations

Mathlib contains an official notion of row equivalence.

The elementary matrices we use are:

* `Matrix.swap` — swap two rows;
* `Matrix.rowScale` — multiply one row by a nonzero scalar;
* `Matrix.transvection` — add a multiple of one row to another row.

Our course library provides shorter commands:

```text
row_swap  A => B, i, j
row_scale A => B, i, c
row_add   A => B, i, j, c
```

Lean starts counting rows at `0`:

```text
Lean row 0 = R₁
Lean row 1 = R₂
Lean row 2 = R₃
```
-/

#check Matrix.RowEquivalent
#check Matrix.transvection
#check Matrix.swap
#check Matrix.rowScale


/-!
## 6. Gaussian elimination

We now verify a complete Gaussian elimination.

Start with the augmented matrix

```text
[ 0  2  0 | 2 ]
[ 1  0  1 | 3 ]
[ 0  0  3 | 6 ]
```

and reduce it to

```text
[ 1  0  0 | 1 ]
[ 0  1  0 | 1 ]
[ 0  0  1 | 2 ]
```

This example uses all three elementary row operations.
To make the process easier to follow,
we provide both computational tools
and customized tactics for performing the row operations
and proving that each step is valid.

### Computation

`rowAdd A i j c` computes the row operation R_i \leftarrow R_i + cR_j.

`rowSwap A i j` computes the row operation R_i \leftrightarrow R_j.

`rowScale' A i c` computes the row operation R_i \leftarrow cR_i.

### Tactics

`row_swap A => A₁, i, j` verifies that A₁ is row equivalent to A by swapping rows i and j.

`row_scale A => A₁, i, (c : ℝ)` verifies that A₁ is row equivalent to A by scaling row i by c.

`row_add A => A₁, i, j, (c : ℝ)` verifies that A₁ is row equivalent to A by performing the row operation
R_i \leftarrow R_i + cR_j.

-/

def AA : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 2, 3;
     4, 5, 6;
     7, 8, 9]

#eval showMatrix (rowScale' AA 1 2)
#eval showMatrix (rowScale' AA 1 2)
def BB : Matrix (Fin 3) (Fin 3) ℚ :=
  rowSwap AA 0 1
#eval showMatrix (rowScale' BB 1 2)
#eval showMatrix (rowAdd BB 0 1 2)

def A : Matrix (Fin 3) (Fin 4) ℝ :=
  !![0, 2, 0, 2;
     1, 0, 1, 3;
     0, 0, 3, 6]

def B : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 0, 0, 1;
     0, 1, 0, 1;
     0, 0, 1, 2]


-- R₁ ↔ R₂
def A₁ : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 0, 1, 3;
     0, 2, 0, 2;
     0, 0, 3, 6]


-- R₂ ← (1/2)R₂
def A₂ : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 0, 1, 3;
     0, 1, 0, 1;
     0, 0, 3, 6]


-- R₃ ← (1/3)R₃
def A₃ : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 0, 1, 3;
     0, 1, 0, 1;
     0, 0, 1, 2]


example : Matrix.RowEquivalent A B := by
  -- R₁ ↔ R₂
  have h₁ : Matrix.RowEquivalent A A₁ := by
    row_swap A => A₁, 0, 1

  -- R₂ ← (1/2)R₂
  have h₂ : Matrix.RowEquivalent A₁ A₂ := by
    row_scale A₁ => A₂, 1, (1 / 2 : ℝ)

  -- R₃ ← (1/3)R₃
  have h₃ : Matrix.RowEquivalent A₂ A₃ := by
    row_scale A₂ => A₃, 2, (1 / 3 : ℝ)

  -- R₁ ← R₁ - R₃
  have h₄ : Matrix.RowEquivalent A₃ B := by
    row_add A₃ => B, 0, 2, (-1 : ℝ)

  -- Row equivalence is transitive.
  -- exact h₁.trans (h₂.trans (h₃.trans h₄))
  exact h₁.trans <| h₂.trans <| h₃.trans <| h₄


example : Matrix.RowEquivalent A B := by
  calc
    Matrix.RowEquivalent A A₁ := by
      row_swap A => A₁, 0, 1
    -- R₂ ← (1/2)R₂
    Matrix.RowEquivalent A₁ A₂ := by
      row_scale A₁ => A₂, 1, (1 / 2 : ℝ)
    -- R₃ ← (1/3)R₃
    Matrix.RowEquivalent A₂ A₃ := by
      row_scale A₂ => A₃, 2, (1 / 3 : ℝ)
    -- R₁ ← R₁ - R₃
    Matrix.RowEquivalent A₃ B := by
      row_add A₃ => B, 0, 2, (-1 : ℝ)


/-!
## 7. What happened behind the scenes?

The commands

```text
row_swap
row_scale
row_add
```

are small course tools built on top of Mathlib's official theorems.

They hide some Lean techniques that we do not need on the first day, including:

* `convert`
* `by decide`
* `funext`
* `fin_cases`
* `simp`
* `norm_num`

In Class 2, we will open this box and learn what these ideas mean.
-/
