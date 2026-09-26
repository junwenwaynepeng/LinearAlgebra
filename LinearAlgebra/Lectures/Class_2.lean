import Mathlib
--import LinearAlgebra.CourseTools
open scoped BigOperators

/-!
# Class 2 — The Language of Proof in Lean

In Class 1, we used Lean to verify computations and row operations arising from Gaussian elimination.
In this class, we step back and develop the basic proof language that appeared behind those examples.

A major theme of this file is:

> The same mathematical argument can often be expressed in several different Lean styles.

We intentionally keep several equivalent proofs together. The goal is not to memorize every possible tactic, but to learn how the logical structure of a mathematical statement suggests a natural proof strategy in Lean.

For example:

- to prove an implication, assume the hypothesis;
- to prove a conjunction, prove both parts;
- to prove an existential statement, provide a witness;
- to prove two functions or matrices are equal, compare their values;
- to prove a statement by contradiction or contraposition, transform the logical structure of the goal.

As you become more familiar with Lean, you will gradually develop your own preferred proof-writing style.

Topics:

1. Equality: `rw`, `subst`, `congrArg`, and `funext`
2. Implication: `intro`, `exact`, `apply`, and `assumption`
3. Conjunction in the goal
4. Conjunction in the assumptions
5. Disjunction in the goal
6. Disjunction in the assumptions
7. Existential statements: witnesses and extraction
8. Excluded middle and `by_cases`
9. Negation, contraposition, `push Not`, and `by_contra`
10. Contradiction: `exfalso` and `contradiction`
11. Intermediate statements: `have` and `suffices`
12. Implication and its negation
13. Automation: `omega`, `simp`, `norm_num`, `ring`, and `linarith`
14. Matrices as functions: `funext` and `ext`
15. Finite cases: `fin_cases`
16. Decidable propositions: `decide`
17. Induction
18. Finite sums and induction
-/


/-!
## 1. Equality
### Rewriting: `rw`

If `h : y = x + 7`, then we may replace `y` by `x + 7`.
-/

example (x y : ℝ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]


/-!
### Replacing a variable completely: `subst`

`rw` rewrites where we ask it to.
`subst x` removes a variable using an equality involving `x`.
-/

example (x y : ℝ) (h : x = y) : x + y = 2 * y := by
  subst x
  ring


/-!
The same statement can also be proved with `rw`.
-/

example (x y : ℝ) (h : x = y) : x + y = 2 * y := by
  rw [h]
  ring


/-!
### Applying the same function to equal objects: `congrArg`

Mathematically:

    x = y  ⟹  f x = f y
-/

example (x y : ℝ) (h : x = y) : x ^ 2 = y ^ 2 := by
  exact congrArg (fun t => t ^ 2) h

example (x y : ℝ) (h : x = y) : x + 1 = y + 1 := by
  exact congrArg (fun t => t + 1) h


/-!
### Functions are equal if they agree on every input: `funext`

Mathematically:

    (∀ x, f x = g x) ⟹ f = g

This is called function extensionality.
-/

example (f g : ℝ → ℝ) (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x

/-In-class-practice-/

example : (fun x : ℝ => x + x) = (fun x => 2 * x) := by
  sorry

/-!
## 2. Implication: `intro`, `exact`, `apply`, and `assumption`

A proof of `P → Q` is something that takes a proof of `P` and produces a proof
of `Q`.
-/

example (P : Prop) : P → P := by
  intro hP
  exact hP


/-!
### `assumption`

If the goal already appears in the context, Lean can find it for us.
-/

example (P : Prop) : P → P := by
  intro hP
  assumption


/-!
### `apply` versus direct `exact`

Both examples prove the same statement.
-/

example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  apply h
  exact p

example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  exact h p


/-!
## 3. Conjunction `P ∧ Q` in goal

There are several common equivalent styles.

### Version 1: `constructor`
-/

example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  · exact p
  · exact q


/-!
### Version 2: construct the proof object directly
-/

example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  exact ⟨p, q⟩


/-!
### Version 3: `refine`

`refine` lets us specify the shape of the proof while leaving subgoals.
-/

example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  refine ⟨?_, ?_⟩
  · exact p
  · exact q


/-!
## 4. Conjunction `P ∧ Q` in assumption

There are several common styles.

### Version 1: projections `.1` and `.2`
-/

example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.1

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.2


/-!
### Version 2: `cases`
-/

example (P Q : Prop) (h : P ∧ Q) : P := by
  cases h with
  | intro p q =>
      exact p


/-!
### Version 3: `obtain`
-/

example (P Q : Prop) (h : P ∧ Q) : P := by
  obtain ⟨p, q⟩ := h
  exact p


/-!
### Version 4: `rcases`
-/

example (P Q : Prop) (h : P ∧ Q) : P := by
  rcases h with ⟨p, q⟩
  exact p


/-!
### Version 5: `intro` can both introduce an assumption and immediately pattern-match it.
-/

example (P Q : Prop) : P ∧ Q → P := by
  intro h
  rcases h with ⟨p, q⟩
  exact p

example (P Q : Prop) : P ∧ Q → P := by
  intro ⟨p, q⟩
  exact p

/-!
## 5. Disjunction `P ∨ Q` in goal

### Version 1: left or right
-/

example (P Q : Prop) (p : P) : P ∨ Q := by
  left
  exact p

example (P Q : Prop) (q : Q) : P ∨ Q := by
  right
  exact q

/-!
### Version 2: Or.inl or Or.inr
-/

example (P Q : Prop) (p : P) : P ∨ Q := by
  exact Or.inl p

example (P Q : Prop) (q : Q) : P ∨ Q := by
  exact Or.inr q


/-!
## 6. Disjunction `P ∨ Q` in assumption

Again, the following proofs establish the same statement.

### Version 1: `cases`
-/

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl p =>
      right
      exact p
  | inr q =>
      left
      exact q

/-!
### Version 2: `obtain`
-/

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  obtain p | q := h
  · right
    exact p
  · left
    exact q

/-!
### Version 3: `rcases`
-/

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with p | q
  · right
    exact p
  · left
    exact q

/-!
### Version 4: `intro` can both introduce an assumption and immediately pattern-match it.
-/

example (P Q : Prop) :  P ∨ Q → Q ∨ P := by
  intro
  | Or.inl p =>
      right
      exact p
  | Or.inr q =>
      left
      exact q

/-!
## 7. Existential statements

To prove

    ∃ x, P x

we must provide a witness `x` and then prove `P x`.

### Version 1: `use`
-/

example : ∃ x : ℝ, x ^ 2 = 4 := by
  use 2
  norm_num


/-!
### Version 2: `refine`
-/

example : ∃ x : ℝ, x ^ 2 = 4 := by
  refine ⟨2, ?_⟩
  norm_num


/-!
### Version 3: construct the proof directly
-/

example : ∃ x : ℝ, x ^ 2 = 4 := by
  exact ⟨2, by norm_num⟩


/-!
### Extracting an existential witness

`rcases` or `obtain` separates the witness from the proof that it has the required
property.
-/

example (h : ∃ x : ℝ, x = 3) : True := by
  --rcases h with ⟨x, hx⟩
  obtain ⟨x, hx⟩ := h
  trivial


/-!
If an existential statement is introduced as an assumption, `intro` can
introduce and decompose it at the same time.
-/

example : (∃ x : ℝ, x = 3) → True := by
  intro ⟨x, hx⟩
  trivial

/-
## 8. Excluded middle and `by_cases`

The law of excluded middle says that for any proposition `P`,

    P ∨ ¬P.

Lean provides this theorem as `Classical.em`.
-/

example (P : Prop) : P ∨ ¬P := by
  --classical
  exact Classical.em P

example (P : Prop) : P ∨ ¬P := by
  by_cases h : P
  · left
    exact h
  · right
    exact h

/-In-class-practice-/

example (P Q : Prop) (h₁ : P → Q) (h₂ : ¬P → Q) : Q := by
  sorry

/-!
## 9. Negation and contraposition

In Lean,

    ¬P

means

    P → False.

We prove

    (P → Q) → (¬Q → ¬P)

in several equivalent styles.

### Version 1: unfold `Not`, then use `apply`
-/

example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  unfold Not
  intro h1 h2 p
  apply h2
  exact h1 p

  -- The last two lines can also be replaced by:
  -- exact h2 (h1 p)

/-!
### Version 2: introduce an intermediate fact
-/

example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro h1 h2 p
  have q : Q := h1 p
  contradiction


/-!
### Version 3: place `P → Q` directly in the context
-/

example (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  intro h1 p
  apply h1
  exact h p

/-!
### version 4: Contrapose
-/

example (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  contrapose
  exact h

/-
### Summary
-/
example (P Q : Prop) :
    (P → Q) ↔ (¬Q → ¬P) := by
  constructor
  · intro h NotQ p
    apply NotQ
    exact h p
  · intro h p
    by_contra hQ
    exact h hQ p
    --contrapose


/-!
### Pushing negations inward: `push Not`

Negations sometimes appear in a form that is inconvenient for ordinary
mathematical reasoning.

For example, instead of

    ¬ x ≤ y

we usually want to work with

    y < x

`push Not` performs this kind of normalization.
-/

example (x y : ℝ) (h : ¬ x ≤ y) : y < x := by
  push Not at h
  exact h

example (P : Prop) : P → ¬¬P := by
  intro h
  push Not
  exact h

example (P : Prop) : ¬¬P → P := by
  intro h
  push Not at h
  exact h

example (P : Prop) (h : ¬¬P) : P := by
  by_contra hP
  exact h hP

example {α : Type} (P : α → Prop) :
    ¬(∃ x, P x) ↔ ∀ x, ¬P x := by
  constructor
  · intro h
    push Not at h
    exact h
  · intro h
    push Not
    exact h

/-In-class-practice-/

example {α : Type} (P : α → Prop) :
    ¬(∀ x, P x) ↔ ∃ x, ¬P x := by
  sorry

/-!
Useful forms are

    push Not
    push Not at h
    push Not at *

There are also variants such as

    by_cases!
    by_contra!
    contrapose!

A useful informal mnemonic is:

    by_cases!   ≈ by_cases   + push Not
    by_contra!  ≈ by_contra  + push Not
    contrapose! ≈ contrapose + push Not

The `!` does not mean that Lean automatically finishes the proof.
It means that the resulting negations are also simplified.
-/

/-!
## 10. From contradiction, anything follows

Suppose our assumptions contain both

    P

and

    ¬P.

Then we can derive `False`.

If the current goal is some proposition `Q`, the tactic

    exfalso

changes the goal from `Q` to `False`. Once we prove the contradiction, the
original goal follows.

The tactic `contradiction` can often detect such a contradiction automatically.
-/

example (P Q : Prop) : (P ∧ ¬P) → Q := by
  intro h
  obtain ⟨p, notp⟩ := h
  exfalso
  exact notp p

example (P Q : Prop) : (P ∧ ¬P) → Q := by
  intro h
  rcases h with ⟨p, notp⟩
  contradiction

/-!
## 11. Intermediate statements: `have` and `suffices`

### `have`

`have` proves an intermediate statement and adds it to the context.
-/

example (x : ℝ) (h : x = 3) : x ^ 2 = 9 := by
  have hx : x ^ 2 = 3 ^ 2 := by
    rw [h]
  norm_num at hx
  exact hx


/-!
### `suffices`

`suffices h : P` means:

> it is enough to prove `P`; after that, I can finish the current goal.

It lets us work backward from the goal.
-/

example (x : ℝ) (h : x = 3) : x + 1 = 4 := by
  suffices hx : x = 3 by
    rw [hx]
    norm_num
  exact h


/-!
## 12. Implication and its negation

We use implication and its negation to summarize all the tactics
and proof techniques from this class.

Classically,

    P → Q

can be expressed as

    ¬P ∨ Q,

and the failure of an implication means

    P ∧ ¬Q.

-/

example (P Q : Prop) :
    (P → Q) ↔ (¬P ∨ Q) := by
  constructor
  · intro h
    by_cases hp : P
    · right
      exact (h hp)
    · left
      exact hp
  · intro h p
    obtain notp | q := h
    · contradiction
    · assumption

example (P Q : Prop) :
    ¬(P → Q) ↔ (P ∧ ¬Q) := by
  constructor
  · intro h
    by_cases hp : P
    · constructor
      · exact hp
      · intro hq
        unfold Not at h
        have pimpq: P → Q := by
          intro _
          exact hq
        exact h pimpq
    · exfalso
      have pimpq : P → Q := by
        intro hp
        contradiction
      exact h pimpq
  · intro h hf
    exact h.2 (hf h.1)

/-!
## 14. Five useful automation tactics

These tactics do different jobs.


### `omega`

Use `omega` for Presburger arithmetic over `ℕ` and `ℤ`
-/

example (m n : ℕ) (h : m + 3 ≤ n) : m + 1 < n := by
  omega

/-
### `simp`

Use `simp` for structural simplification and standard rewrite rules.
-/

example (G : Type) [Group G] (a b c : G) :
    a * a⁻¹ * 1 * b = b * c * c⁻¹ := by
  simp


/-!
### `norm_num`

Use `norm_num` for explicit numerical arithmetic.
-/

example : (3 : ℝ) * 7 - 5 = 16 := by
  norm_num


/-!
### `ring`

Use `ring` for polynomial identities.
-/

example (x y : ℝ) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring


/-!
### `linarith`

Use `linarith` for linear consequences of hypotheses.
-/

example (x y a b : ℝ) (h1 : x < y) (h2 : a < b) :
    x + a < y + b := by
  linarith [h1, h2]

  -- A direct theorem-based proof is also possible:
  -- exact add_lt_add h1 h2


/-!
A useful rule of thumb:

    arithmetic over ℕ or ℤ     → omega
    simplify structure         → simp
    explicit numerical facts   → norm_num
    polynomial identity        → ring
    linear consequence         → linarith
-/


/-!
## 15. Matrix is a function

Recall that to prove two functions are equal, prove that they agree at every input.
-/

example (f g : ℝ → ℝ) (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x


/-!
A matrix in Lean is essentially a function

    row → column → entry.
-/

def M₁ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 2;
     3, 4]

def M₂ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 2;
     3, 4]


/-!
### Version 1: `funext`
-/

example : M₁ = M₂ := by
  funext row col
  fin_cases row <;>
  fin_cases col <;>
  norm_num [M₁, M₂]


/-!
### Version 2: `ext`
-/

example : M₁ = M₂ := by
  ext row col
  fin_cases row <;>
  fin_cases col <;>
  norm_num [M₁, M₂]


/-!
For this course:

* `funext` emphasizes that a matrix is a function;
* `ext` is a convenient general-purpose extensionality tactic.
-/


/-!
## 16. Finite cases: `fin_cases`

If `i : Fin 3`, then there are only three possibilities:
`0`, `1`, and `2`.
-/

example (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i
  · simp
  · simp
  · simp


/-!
## 17. Decidable propositions: `decide`

Some propositions can be checked directly by computation.
-/

example : (1 : Fin 3) ≠ 0 := by
  decide

example : (2 : Fin 4) ≠ 1 := by
  decide


/-!
This is the same kind of fact that appears behind a row addition:
the source row and target row must be different.
-/


/-!
## 18. Proving a natural-number inequality in different ways

We prove

    x ≤ 1 + x.

### Version 1: rewrite as an existence statement
-/

example (x : Nat) : x ≤ 1 + x := by
  rw [le_iff_exists_add]
  use 1
  omega


/-!
### Version 2: induction
-/

example (x : Nat) : x ≤ 1 + x := by
  induction x with
  | zero =>
      simp
  | succ x ih =>
      linarith


/-!
## 19. A first induction example
-/

example (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
      linarith
  | succ n ih =>
      linarith


/-!
## 20. The sum of the first `n` odd numbers is `n²`

This example combines induction, rewriting, and polynomial algebra.
-/

example (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-
### Reading Lean as mathematical language

A useful habit is to translate each Lean command into an ordinary mathematical sentence.

| Lean | Natural mathematical language |
|---|---|
| `intro hP` | Assume `P`. |
| `intro x` | Let `x` be arbitrary. |
| `exact h` | This follows from `h`. |
| `apply h` | Apply `h`; it remains to verify the required hypothesis. |
| `assumption` | This is already one of our assumptions. |
| `constructor` | We prove the two required parts separately. |
| `left` | We prove the left-hand alternative. |
| `right` | We prove the right-hand alternative. |
| `rcases h with ⟨p, q⟩` | From `h`, we obtain both `P` and `Q`. |
| `rcases h with p \| q` | Consider the two possible cases: `P` or `Q`. |
| `use x` | Take `x` as the required witness. |
| `have h : P := by ...` | First, we show that `P`. |
| `suffices h : P by ...` | It is enough to show that `P`. |
| `by_cases h : P` | Consider separately the cases `P` and `¬P`. |
| `by_contra h` | Suppose, for contradiction, that the desired statement is false. |
| `contrapose` | We prove the statement by proving its contrapositive. |
| `rw [h]` | Rewrite using the equality `h`. |
| `subst x` | Substitute for `x` using an equality involving `x`. |
| `funext x` | Fix an arbitrary `x`; it is enough to compare the two functions at `x`. |
| `ext i j` | Fix arbitrary `i` and `j`; it is enough to compare the corresponding matrix entries. |
| `fin_cases i` | Check each of the finitely many possible values of `i`. |
| `induction n with` | We prove the statement by induction on `n`. |

The important idea is not to translate tactics word for word, but to recognize
the mathematical proof move that each tactic represents.
-/
