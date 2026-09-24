import Mathlib
--import LinearAlgebra.CourseTools
open scoped BigOperators

/-!
# Class 2 — Basic Logic and Equivalent Proof Styles in Lean

In Class 1, we used Lean to verify Gaussian elimination.
This class develops the proof language that appeared behind those examples.

A major theme of this file is:

> The same mathematical argument can often be written in several equivalent
> Lean styles.

We intentionally keep these equivalent versions together so that you can compare
them and gradually develop your own proof-writing style.

Topics:

1. Equality: `rfl`, `rw`, `subst`, and `congrArg`
2. Implication: `intro`, `exact`, `apply`, and `assumption`
3. Conjunction: `constructor`, `⟨_, _⟩`, `refine`, `.1/.2`
4. `cases`, `obtain`, `rcases`, and `rintro`
5. Disjunction
6. Existential statements: `use`, `refine`, `exact`
7. Negation, contradiction, and excluded middle
8. `have` and `suffices`
9. `simp`, `norm_num`, `ring`, and `linarith`
10. `funext`, `ext`, `fin_cases`, and `decide`
11. Induction
12. Returning to the row operations from Class 1
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
## 3. Conjunction: constructing `P ∧ Q`

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
## 4. Conjunction: extracting information from `P ∧ Q`

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
### `rintro` = `intro` + decomposition

The next two proofs are equivalent.
-/

example (P Q : Prop) : P ∧ Q → P := by
  intro h
  rcases h with ⟨p, q⟩
  exact p

example (P Q : Prop) : P ∧ Q → P := by
  intro ⟨p, q⟩
  exact p


/-!
## 5. Disjunction: proving `P ∨ Q`
-/

example (P Q : Prop) (p : P) : P ∨ Q := by
  left
  exact p

example (P Q : Prop) (q : Q) : P ∨ Q := by
  right
  exact q


/-!
## 6. Disjunction: extracting information from `P ∨ Q`

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
If the existential statement is introduced as an assumption, `intro ⟨?_,?_ ⟩ ` can
introduce and decompose it immediately.
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

/-In-class-practicer-/

example (P Q : Prop) (h₁ : P → Q) (h₂ : ¬P → Q) : Q := by
  sorry

/-!
### `classical`

Lean is constructive by default.

Writing

    classical

allows Lean to use classical reasoning and classical decidability.

For this course, you mainly need to recognize this line when it appears
in a proof.
-/

example (P : Prop) : P ∨ ¬P := by
  --classical
  exact Classical.em P


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
The above direction is constructive, and the reverse is classical reasoning
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

    y <af

`push_neg` performs this kind of normalization.
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

    push_neg
    push_neg at h
    push_neg at *

There are also variants such as

    by_cases!
    by_contra!
    contrapose!

A useful informal mnemonic is:

    by_cases!   ≈ by_cases   + push_neg
    by_contra!  ≈ by_contra  + push_neg
    contrapose! ≈ contrapose + push_neg

The `!` does not mean that Lean automatically finishes the proof.
It means that the resulting negations are also simplified.
-/

/-!
### Negating implication
-/

example (P Q : Prop) :
    (P → Q) ↔ (¬P ∨ Q) := by
  constructor
  · intro h
    by_cases hp : P
    · exact Or.inr (h hp)
    · exact Or.inl hp
  · intro h
    cases h with
    | inl hnp =>
        intro p
        exfalso
        exact hnp p
    | inr hq =>
        intro _
        exact hq

example (P Q : Prop) :
    ¬(P → Q) ↔ (P ∧ ¬Q) := by
  constructor
  · intro h
    by_cases hp : P
    · constructor
      · exact hp
      · intro hq
        exact h (fun _ => hq)
    · exfalso
      exact h (fun p => False.elim (hp p))
  · intro h hf
    exact h.2 (hf h.1)
/-!
## 10. From contradiction, anything follows

We prove

    (P ∧ ¬P) → Q

in several styles.
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


example (P Q : Prop) : (P ∧ ¬P) → Q := by
  intro h
  cases h with
  | intro p notp =>
      exfalso
      exact notp p


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
## 12. Four useful automation tactics

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

    simplify structure         → simp
    explicit numerical facts   → norm_num
    polynomial identity        → ring
    linear consequence         → linarith
-/


/-!
## 13. Equality of functions: `funext`

To prove two functions are equal, prove that they agree at every input.
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
## 14. Finite cases: `fin_cases`

If `i : Fin 3`, then there are only three possibilities:
`0`, `1`, and `2`.
-/

example (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i
  · simp
  · simp
  · simp


/-!
## 15. Decidable propositions: `decide`

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
## 16. Proving a natural-number inequality in different ways

We prove

    x ≤ 1 + x.

### Version 1: rewrite as an existence statement
-/

example (x : Nat) : x ≤ 1 + x := by
  rw [le_iff_exists_add]
  use 1
  omega --linarith


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
## 17. A first induction example
-/

example (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
      linarith
  | succ n ih =>
      linarith


/-!
## 18. The sum of the first `n` odd numbers is `n²`

This example combines induction, rewriting, and polynomial algebra.
-/

example (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
