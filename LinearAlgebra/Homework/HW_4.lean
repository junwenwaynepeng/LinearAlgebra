import Mathlib

/-!
# Homework 4 — Matrices and Vector-Space Reasoning

Based only on Lectures 1–4. Homework N uses Lectures 1 through N,
unless a different scope is explicitly requested.

Six questions: 2 basic, 2 medium, 2 hard. Total: 100 points.
Estimated working time: 150 minutes, plus time to review your proofs.

Replace the six exercise proof holes with complete Lean proofs.
Keep the theorem statements and supplied definitions unchanged.
Add a short mathematical explanation in a comment above each proof.
You may introduce auxiliary lemmas and use earlier questions once proved.

Use the techniques from class: intro, exact, apply, constructor, rcases,
use, rw, change, unfold, congrArg, funext, ext, fin_cases, have, calc,
by_cases, by_contra, simp, norm_num, ring, and linarith.
The library facts specifically mentioned below are also allowed.
Do not use an existing theorem that directly states an exercise's conclusion.

This file supplies its own required course definitions in a namespace.
To make a personal working copy, copy this file into MyWork/.
-/

namespace Homework4

open Matrix
open scoped BigOperators

/-!
## Question 1 — A concrete failure of commutativity
Basic · 10 points · about 10 minutes

Objective: connect matrix multiplication with entry computations and
a proof of inequality.

For the rational matrices below, prove P * Q ≠ Q * P.
First compute the (0,0)-entry of each product on paper and record the
results in a comment. Then use these entries in your formal proof.

Hint: a matrix equality gives an entry equality via
congrArg (fun M => M 0 0). Matrix.mul_apply expands a product entry.
Fin.sum_univ_two expands a sum over Fin 2 as its two terms.

References:
- LinearAlgebra/Lectures/Class_1.lean, §2 "A matrix in Lean".
- LinearAlgebra/Lectures/Class_2.lean, §1 "congrArg" and §9 "Negation".
- LinearAlgebra/Lectures/Class_3.lean, proposition_2_1 and matrix_assoc_basic.
-/

def P : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 1;
     0, 1]

def Q : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0;
     1, 1]

theorem q1_noncommuting : P * Q ≠ Q * P := by
  sorry

/-!
## Question 2 — Symmetry of a combination of function vectors
Basic · 10 points · about 15 minutes

Objective: use pointwise vector operations and universal hypotheses.

A function f is even when f (-x) = f x for every real x.
Suppose f and g are even. Prove that a • f + b • g is also even
for arbitrary real scalars a and b.

On functions, addition and scalar multiplication act pointwise:
(f + g) x = f x + g x and (a • f) x = a * f x.
Hint: introduce x, use change to expose the scalar expressions,
and rewrite with the hypotheses at x.

References:
- LinearAlgebra/Lectures/Class_2.lean, §2 "Implication" and §1 "Rewriting".
- LinearAlgebra/Lectures/Class_4.lean, funAdd, funSMul, F_is_vector_space.
-/

theorem q2_even_combination
    (a b : ℝ) (f g : ℝ → ℝ)
    (hf : ∀ x : ℝ, f (-x) = f x)
    (hg : ∀ x : ℝ, g (-x) = g x) :
    ∀ x : ℝ, (a • f + b • g) (-x) = (a • f + b • g) x := by
  sorry

/-!
## Question 3 — Solving a system with a self-inverse matrix
Medium · 15 points · about 20 minutes

Objective: turn a matrix identity into an equivalence describing solutions.

Assume A * A = I. Show that A x = b holds exactly when x = A b.
Prove both directions, showing how applying A twice removes it.
Use a calculation with matrix-vector products, rather than a general
library theorem about solving invertible systems.

Useful facts from the Class 3 calculation:
- Matrix.mulVec_mulVec: A *ᵥ (B *ᵥ v) = (A * B) *ᵥ v.
- Matrix.one_mulVec: (1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ v = v.

The statement allows n = 0; no positive-dimension assumption is needed.

References:
- LinearAlgebra/Lectures/Class_2.lean, §3 "Conjunction" (constructor also
  separates the two directions of an equivalence).
- LinearAlgebra/Lectures/Class_3.lean, IsInverse and solution_unique.
-/

theorem q3_self_inverse_system
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A * A = 1) (x b : Fin n → ℂ) :
    A *ᵥ x = b ↔ x = A *ᵥ b := by
  sorry

/-!
### The course's vector-space axioms

The next structure is copied from Class_4.lean into this namespace.
In particular, neg_add_cancel asserts existence of an additive inverse;
it does not identify that inverse with the supplied Neg operation.
No extra axioms or Mathlib Module instances are assumed.
-/

structure VectorSpaceAxioms
    (V K : Type*) [Field K] [Add V] [Zero V] [Neg V] [SMul K V] : Prop where
  add_comm : ∀ u v : V, u + v = v + u
  add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w)
  zero_add : ∀ v : V, 0 + v = v
  neg_add_cancel : ∀ v : V, ∃ u, u + v = 0
  one_smul : ∀ v : V, (1 : K) • v = v
  mul_smul : ∀ (a b : K) (v : V), (a * b) • v = a • (b • v)
  smul_add : ∀ (a : K) (u v : V), a • (u + v) = a • u + a • v
  add_smul : ∀ (a b : K) (v : V), (a + b) • v = a • v + b • v

/-!
## Question 4 — Cancellation of a nonzero scalar
Medium · 15 points · about 25 minutes

Objective: derive a new vector-space law from the stated axioms.

If a ≠ 0 and a • u = a • v, prove u = v.
Use hV.one_smul and hV.mul_smul, keeping the scalar factors in order.
The field identity inv_mul_cancel₀ ha states a⁻¹ * a = 1.

The only structure on V is the one listed below. A scalar-cancellation
lemma requiring a Mathlib Module instance is therefore not available.

References:
- LinearAlgebra/Lectures/Class_4.lean, VectorSpaceAxioms, cancellation_law,
  and zero_smul_V (deriving laws from axioms).
- LinearAlgebra/Lectures/Class_3.lean, inverse_unique (using an inverse).
-/

theorem q4_cancel_nonzero_scalar
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (a : K) (ha : a ≠ 0) (u v : V)
    (h : a • u = a • v) :
    u = v := by
  sorry

/-!
### Matrix inverses

This is the IsInverse definition from Class_3.lean, placed in this
namespace to avoid collisions with other course files.
-/

def IsInverse
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A * B = 1 ∧ B * A = 1

/-!
## Question 5 — Commuting with a matrix and with its inverse
Hard · 25 points · about 35 minutes

Objective: combine inverse identities, associativity, and a reusable
argument in the two directions of an equivalence.

Assume B is an inverse of A. Prove that C commutes with A if and only
if C commutes with B. Work from IsInverse and show the matrix calculations;
do not use matrix inverse notation or a general commutation theorem.

Useful facts: Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one.
A local claim proved with have can be reused with A and B interchanged.
Explain why reversing their roles is legitimate.

References:
- LinearAlgebra/Lectures/Class_2.lean, §11 "Intermediate statements".
- LinearAlgebra/Lectures/Class_3.lean, matrix_assoc_basic, IsInverse,
  and inverse_unique.
-/

theorem q5_commuting_inverse
    {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hAB : IsInverse A B) :
    A * C = C * A ↔ B * C = C * B := by
  sorry

/-!
## Question 6 — A vector equation has exactly one solution
Hard · 25 points · about 45 minutes

Objective: synthesize additive inverses, scalar inverses, and uniqueness
using only the course's explicit axioms.

For a nonzero scalar a and vectors u,w, prove there is exactly one v
such that a • v + u = w. The notation ∃! asks for a witness, a proof
that it solves the equation, and a proof that any other solution equals it.

You may reuse Question 4. Additive cancellation and v + 0 = v may be
derived as in Class 4. The field identity mul_inv_cancel₀ ha states
a * a⁻¹ = 1.

Important: obtain an additive inverse of u using hV.neg_add_cancel u.
Do not assume that the arbitrary Neg instance on V supplies this inverse.
The proof should work without installing an AddGroup or Module instance.

References:
- LinearAlgebra/Lectures/Class_2.lean, §7 "Existential statements".
- LinearAlgebra/Lectures/Class_3.lean, solution_unique.
- LinearAlgebra/Lectures/Class_4.lean, VectorSpaceAxioms, add_zero_V,
  cancellation_law, and neg_unique_V.
-/

theorem q6_unique_vector_solution
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (a : K) (ha : a ≠ 0) (u w : V) :
    ∃! v : V, a • v + u = w := by
  sorry

end Homework4
