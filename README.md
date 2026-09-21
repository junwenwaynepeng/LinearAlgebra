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

You are encouraged to read them, run them in VS Code. **Do not** save any change you make in this folder.

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

## 2. Install Lean for This Course

This course uses Lean through Visual Studio Code. Before installing anything, it is helpful to distinguish three different components:

* **Lean 4** is the theorem prover and programming language itself.
* The **Lean 4 extension for Visual Studio Code** helps VS Code work with Lean. It provides syntax highlighting, the Infoview, error messages, and Lean-related commands. The extension itself is **not Lean**.
* **Elan** is the Lean version manager. It installs and manages Lean toolchains and allows different projects to use different versions of Lean.

You do **not** need to manually choose or download a specific Lean version for this course. The course repository specifies the required version.

---

### Step 1. Install Lean

#### Recommended

Follow the official [manual installation guide](https://lean-lang.org/install/manual/). This will install Lean on your computer.

After completing the guide, you should have VS Code, the Lean 4 extension, Elan, and a working Lean installation.

Once everything is set up, continue to [Step 3](#step 3. Clonethe course repository).

#### For Beginners

Follow the official [installation guide](https://lean-lang.org/install/).

After completing the three steps, open VS Code and press `Ctrl + Shift + P` (`Cmd + Shift + P` on macOS). Search for `Lean 4: Install Elan` and follow the instructions.

After Elan is installed, continue to [Step 2](Step 2. Check that Git is installed).

---

### Step 2. Check that Git is installed

First check whether Git is already installed:

```bash
git --version
```

If this prints a version number, continue to Step 3.

#### Windows

Install **Git for Windows**:

https://git-scm.com/download/win

Git for Windows also installs **Git Bash**, which will be useful for running the course update script.

After installation, open Git Bash and check:

```bash
git --version
```

#### Ubuntu / Debian Linux

Run:

```bash
sudo apt update
sudo apt install git
```

Then check:

```bash
git --version
```

#### macOS

First try:

```bash
git --version
```

If macOS asks you to install the Command Line Tools, follow the prompt.

You can also install them manually with:

```bash
xcode-select --install
```

Then check again:

```bash
git --version
```

---

### Step 3. Clone the course repository

Open a terminal.

On Windows, I recommend using **Git Bash**.

Run:

```bash
git clone https://github.com/junwenwaynepeng/LinearAlgebra.git
cd LinearAlgebra
```

Do not download the repository as a ZIP file.

Cloning with Git allows you to receive future lecture notes, homework, corrections, and other course updates.

If your terminal says `git: command not found`, please return to Step 2. 

---

### Step 4. Download Mathlib cache: the main mathematical library for Lean

You should now be inside the `LinearAlgebra` directory.

Run:

```bash
lake exe cache get
lake build
```

This is an important part of the initial project setup.

The repository contains:

```text
lean-toolchain
```

which specifies the Lean version required by this course.

When you run `lake` inside the project, `Elan` checks this file. If the required Lean toolchain is not already installed, `Elan` will install it.

The command

```bash
lake exe cache get
```

downloads the precompiled **Mathlib cache** used by the project. This prevents your computer from having to compile most of Mathlib from source.

Then:

```bash
lake build
```

checks that the entire course project builds correctly.

So this step prepares both the correct Lean environment and the Mathlib files needed by the course.

---

### Step 5. Check the installation

Inside the terminal, run:

```bash
elan --version
lean --version
lake --version
git --version
```

All four commands should print version information.

If Lean works inside VS Code but `lean` or `lake` is not found in the terminal, first close and reopen the terminal or VS Code.

On Linux, you can also try:

```bash
source "$HOME/.elan/env"
```

On MacOS, you can try: `source ~/.profile` or `source ~/.bash_profile`

and then:

```bash
lake --version
```

again.

---

### Step 6. Open the project in VS Code

From inside the `LinearAlgebra` directory, run:

```bash
code .
```

Alternatively, open VS Code and choose:

```text
File → Open Folder
```

then select the whole `LinearAlgebra` directory.

Do **not** open only an individual `.lean` file.

Lean projects depend on files such as:

```text
lean-toolchain
lakefile.toml
lake-manifest.json
```

so VS Code should open the entire project folder.

When you open a Lean file, the Lean extension will start the Lean language server and display information in the **Infoview**.

---

### Step 7. Updating the course

You only need to clone and prepare the repository once.

After that, when new course material is released, go to your LinearAlgebra directory and run:

```bash
bash update_course.sh
```

On Windows, run this inside **Git Bash**.

The update script will:

1. check that you do not have uncommitted changes;
2. download the newest course files;
3. update the Lean/Mathlib dependencies if necessary;
4. download the matching Mathlib cache;
5. run lake build to verify that everything still works.

The updater intentionally stops if you have uncommitted changes. This protects your work from being accidentally overwritten.

If **VS Code was open** while you ran the update, restart the Lean language server afterward so that VS Code uses the updated Lean toolchain and project dependencies.

Open the Command Palette:

* Windows/Linux: press Ctrl + Shift + P
* macOS: press Cmd + Shift + P

Then search for:

Lean 4: Restart Server

and press `Enter`.

For your own homework and experiments, use the MyWork/ directory rather than modifying instructor-maintained files directly.