# Linear Algebra with Lean

Lean files for this Linear Algebra course.

## 1. Install Lean

### Windows
1. Install [Git](https://git-scm.com/download/win).
2. Install [Visual Studio Code](https://code.visualstudio.com/).
3. In VS Code, install the official **Lean 4** extension by `leanprover`.
4. Follow the Lean 4 extension setup to install Lean/`elan`.

### Linux
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

Then install VS Code and the official **Lean 4** extension.

### iPad / iPhone
Use **GitHub Codespaces** in Safari. Open this repository on GitHub, choose:

**Code → Codespaces → Create codespace**

Then use the browser version of VS Code and install the **Lean 4** extension if necessary.

---

## 2. Get the course files

For the first time, **clone the repository instead of using Download ZIP**:

```bash
git clone https://github.com/junwenwaynepeng/LinearAlgebra.git
cd LinearAlgebra
lake exe cache get
lake build
code .
```

After that, get new lecture and homework files with:

```bash
git pull
```

You normally only need to clone the repository once.

---

## 3. IMPORTANT: Do all your work in `MyWork/`

**Do not edit files in `LinearAlgebra/Lectures/` or `LinearAlgebra/Homework/`.**

Those files are maintained by the instructor and may change when you run `git pull`.

Instead, copy anything you want to modify into:

```text
MyWork/
```

For example:

```bash
cp LinearAlgebra/Homework/HW_01.lean MyWork/HW_01.lean
```

Then edit:

```text
MyWork/HW_01.lean
```

Use `MyWork/` for homework, experiments, practice, and any file you create yourself.

A good weekly routine is:

```bash
git pull
code .
```

Then read the released files and copy anything you want to work on into `MyWork/`.

---

## 4. Course outline

### Class 01 — [Title]
[Write a short 1–3 sentence summary.]

**Lean:** `intro`, `exact`, `apply`, ...

### Class 02 — [Title]
[Write a short 1–3 sentence summary.]

**Lean:** ...

### Class 03 — [Title]
[Write a short 1–3 sentence summary.]

**Lean:** ...
