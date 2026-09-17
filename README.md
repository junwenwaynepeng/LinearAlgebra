# Linear Algebra with Lean

This repository contains the Lean files used in my Linear Algebra course.

The purpose of Lean in this course is **not** to replace ordinary mathematical reasoning. Instead, we use Lean to make definitions, computations, and proofs precise. Early in the course, Lean will be used alongside familiar topics such as matrices, systems of linear equations, and elementary row operations. Later, we will use it to formalize more abstract ideas such as vector spaces, linear independence, span, basis, and linear maps.

You do not need previous experience with Lean.

---

## 1. What is in this repository?

The main folders are:

```text
LinearAlgebra/
├── LinearAlgebra/
│   ├── Lectures/
│   │   ├── Class_1.lean
│   │   ├── Class_2.lean
│   │   └── ...
│   └── Homework/
│       ├── HW_1.lean
│       ├── HW_2.lean
│       └── ...
├── MyWork/
├── lakefile.toml
├── lean-toolchain
└── update_course.sh
```

### `LinearAlgebra/Lectures/`

These are the Lean files used in class.

You are encouraged to read them, run them in VS Code, change small pieces, and experiment with them.

### `LinearAlgebra/Homework/`

These are the Lean homework files distributed for the course.

### `MyWork/`

**Do your own work here.**

Files in `Lectures/` and `Homework/` may be updated by the instructor. If you want to modify one of them, copy it into `MyWork/` first.

For example:

```bash
cp LinearAlgebra/Homework/HW_1.lean MyWork/HW_1.lean
```

Then edit:

```text
MyWork/HW_1.lean
```

This prevents future course updates from conflicting with your work.

---

## 2. Install Lean

The recommended setup is:

1. Install Git
2. Install Visual Studio Code
3. the official **Lean 4** extension for VS Code
4. `elan`, the Lean version manager (Instruction)[https://lean-lang.org/install/manual/?utm_source=chatgpt.com]
4. Make sure Elan is installed
5. Clone the course repository
6. Open the repository in VS Code

Jump to your OS [Windows](#windows) [Ununtu/Linux](#ubuntu--linux) [Mac](#macos)

**You do not need to install a specific version of Lean manually.**
We use `elan`, the Lean version manager. This repository contains a `lean-toolchain` file that tells `elan` which version of Lean the course requires. When the course Lean version changes, `elan` will automatically use the version specified by the repository.


### Windows

1. Install Git: https://git-scm.com/download/win
2. Install Visual Studio Code: https://code.visualstudio.com/
3. In VS Code, install the extension **Lean 4** by `leanprover`.
4. Follow the extension instructions to install Lean through `elan`.

For the update script in this repository, Windows users should use **Git Bash** or **WSL**.

### Ubuntu / Linux

Install Git and `curl`:

```bash
sudo apt update
sudo apt install git curl
```

Install Lean through `elan`:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
```

Then install Visual Studio Code and the official **Lean 4** extension.

### macOS

Install Lean through `elan`:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
```

Then install Visual Studio Code and the official **Lean 4** extension.

### iPad / iPhone

A practical option is **GitHub Codespaces**. Open this repository on GitHub and choose:

```text
Code → Codespaces → Create codespace
```

You can then use the browser version of VS Code.

---

## 3. First-time setup

Clone the repository instead of downloading a ZIP file:

```bash
git clone https://github.com/junwenwaynepeng/LinearAlgebra.git
cd LinearAlgebra
lake exe cache get
lake build
code .
```

You normally only need to clone the repository once.

`lake exe cache get` downloads precompiled mathlib files so that your computer does not need to compile most of mathlib from source.

---

## 4. Updating the course

The course repository may change during the semester. For example, new lecture files may be added, homework may be released, Lean examples may be corrected, or the mathlib version may be updated.

### Recommended method

Run:

```bash
./update_course.sh
```

On Windows using Git Bash:

```bash
bash update_course.sh
```

The update script will:

1. check that your repository has no uncommitted changes;
2. download the newest course files;
3. update Lean/mathlib dependencies;
4. download the matching mathlib cache;
5. run `lake build` to make sure the project is working.

### If you cloned the repository before `update_course.sh` was added

Run this once:

```bash
git pull --ff-only
bash update_course.sh
```

After that, you can normally use only:

```bash
bash update_course.sh
```

---

## 5. Important: protect your own work

The updater intentionally stops if Git detects uncommitted changes. This is a safety feature.

If you have changed files, first save your work:

```bash
git status
git add .
git commit -m "Save my work"
```

Then run:

```bash
./update_course.sh
```

For ordinary homework and experiments, the recommended approach is still to work inside `MyWork/` rather than editing the instructor-maintained files directly.

---

## 6. Using Lean in VS Code

Open the project folder itself:

```bash
code .
```

Then open a `.lean` file. Lean continuously checks the file while you type.

The **Lean Infoview** shows the current goal, hypotheses, errors, and output from commands such as `#check` and `#eval`.

If the Infoview is hidden, open the VS Code command palette with `Ctrl + Shift + P` and search for:

```text
Lean: Show Infoview
```

---

## 7. Useful Lean commands

### `#check`

Ask Lean for the type of an expression:

```lean
#check 3
#check Matrix
#check Matrix.RowEquivalent
```

Think of it as asking: **What kind of mathematical object is this?**

### `#eval`

Ask Lean to compute a concrete value:

```lean
#eval 2 + 3
```

For a matrix, you can evaluate an entry:

```lean
def A : Matrix (Fin 2) (Fin 3) ℤ :=
  !![1, 2, 3;
     4, 5, 6]

#eval A 0 1
```

The output appears in the Lean Infoview.

### `example`

Use `example` when you want Lean to verify a mathematical statement:

```lean
example : (2 : ℝ) + 3 = 5 := by
  norm_num
```

`#eval` computes; `example` proves.

---

## 8. Matrices and row operations

One of the first applications of Lean in this course is Gaussian elimination.

```lean
import Mathlib

def A : Matrix (Fin 2) (Fin 3) ℝ :=
  !![1, 2, 3;
     4, 5, 6]
```

Mathlib includes an official notion of row equivalence:

```lean
#check Matrix.RowEquivalent
#check Matrix.rowEquivalent_swap
#check Matrix.rowEquivalent_rowScale
#check Matrix.rowEquivalent_transvection
```

These correspond to the three elementary row operations:

1. swap two rows;
2. multiply a row by a nonzero scalar;
3. add a multiple of one row to another row.

For example:

```lean
example :
    Matrix.RowEquivalent A
      (Matrix.swap ℝ (0 : Fin 2) (1 : Fin 2) * A) := by
  exact Matrix.rowEquivalent_swap A 0 1
```

As the course progresses, we will use Lean to connect these formal statements to the linear algebra you already know.

---

## 9. Some tactics you will encounter

You do **not** need to memorize all Lean tactics at once.

```text
rfl         proof by definitional equality
rw          rewrite using an equality
simp        simplify expressions
norm_num    prove explicit numerical arithmetic
ring        prove polynomial identities
linarith    solve linear arithmetic consequences
intro       introduce an assumption
exact       provide exactly the required proof
constructor split a goal with multiple components
```

We will introduce them gradually when they are mathematically useful.

---

## 10. Course philosophy

The goal is not to learn Lean syntax for its own sake.

We use Lean because formalization forces us to answer questions such as:

- What exactly is a matrix?
- What does it mean for two matrices to be row equivalent?
- Why does an elementary row operation preserve the solution set?
- What exactly does “linearly independent” mean?
- Which assumptions are really needed in a proof?

At first, Lean may feel stricter than handwritten mathematics. That strictness is useful: it helps expose hidden assumptions and makes the logical structure of an argument visible.

You should still learn ordinary calculations and handwritten proofs. Lean is an additional language for understanding and verifying mathematics.

---

## 11. If something is not working

First try:

```bash
./update_course.sh
```

or on Windows Git Bash:

```bash
bash update_course.sh
```

If VS Code still shows errors:

1. make sure you opened the **whole repository folder**, not just one `.lean` file;
2. restart the Lean language server;
3. run:

```bash
lake build
```

If the problem remains, send me the error message, file name, and line where the error occurs.

Do not reinstall everything unless necessary.

---

## 12. Repository updates

This repository is actively maintained during the course. Lecture files may therefore evolve as we find clearer ways to express the mathematics in Lean.

When an important dependency update is made, the repository will pin the required Lean/mathlib versions so that everyone in the class can work with the same environment.
