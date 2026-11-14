import Mathlib
import LinearAlgebra.VectorSimp

/-!
# Homework 5 — Linear Combinations, Spans, and Subspaces

Scope: Lectures 1–5.
Two basic questions, three medium questions, and one hard question.
100 points · about 150 minutes.

Replace each exercise's sorry with a proof. For each question, first write
a short mathematical argument in a comment, then formalize it in Lean.
You may use the proof techniques and arithmetic tactics from Lectures 1–5.
Use vector_simp for representation changes and numerical calculations.
Keep mathematical operations such as distributivity, finite-sum interchange,
subspace closure, and finite induction explicit in your argument.

The course definitions LinearCombination, IsLinearCombination, Span,
VectorSpaceAxioms, and IsVectorSubspace are imported from CourseTools.
Use these definitions throughout this homework.
-/

namespace Homework5

open scoped BigOperators
open scoped Classical

/-!
### Supplied facts about function vectors and subspaces

Both Fin 3 → ℝ and ℝ → ℝ use pointwise operations:
(f + g) x = f x + g x and (a • f) x = a * f x.
The first supplied theorem verifies the vector-space axioms for X → ℝ,
as in Class 4 and Class5Examples.F_is_vector_space.

The second theorem extracts the three subspace properties from the course's
definition of IsVectorSubspace. It is supplied so that you can work with
zero, addition, and scalar multiplication directly.

Usage:
  obtain ⟨hzero, hadd, hsmul⟩ := subspace_properties hW

Here hadd u v hu hv proves u + v ∈ W, and
hsmul a v hv proves a • v ∈ W.
To prove a new set is a subspace, use the course theorem subspace_test.

CourseTools also supplies subspace_sum_mem: a finite sum belongs to a
subspace when every summand belongs to it. Its proof is provided; in
Question 6, justify membership of each summand before applying it.
-/

theorem function_space_axioms (X : Type*) :
    VectorSpaceAxioms (X → ℝ) ℝ where
  add_comm := add_comm
  add_assoc := add_assoc
  zero_add := zero_add
  neg_add_cancel := neg_add_cancel
  one_smul := one_smul ℝ
  mul_smul := mul_smul
  smul_add := smul_add
  add_smul := add_smul

theorem subspace_properties
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    {hV : VectorSpaceAxioms V K} {W : Set V}
    (hW : IsVectorSubspace hV W) :
    (0 : V) ∈ W ∧
    (∀ u v : V, u ∈ W → v ∈ W → u + v ∈ W) ∧
    (∀ (a : K) (v : V), v ∈ W → a • v ∈ W) := by
  obtain ⟨addW, zeroW, negW, smulW, _, hadd, hzero, _, hsmul⟩ := hW
  refine ⟨?_, ?_, ?_⟩
  · rw [← hzero]
    exact zeroW.zero.property
  · intro u v hu hv
    rw [← hadd ⟨u, hu⟩ ⟨v, hv⟩]
    exact (addW.add ⟨u, hu⟩ ⟨v, hv⟩).property
  · intro a v hv
    rw [← hsmul a ⟨v, hv⟩]
    exact (smulW.smul a ⟨v, hv⟩).property

/-!
## Question 1 — Construct a linear combination
Basic · 10 points · about 20 minutes

Objective: find coefficients and verify a vector identity.

Let u = (1,1,0), v = (0,1,1), and b = (2,1,-1).
Find real scalars a and c such that b = a • u + c • v.
Record the scalars and verify the three coordinates in your written argument.
Then prove that b is a linear combination of the finite set S = {u,v}.

Hint: vector_simp [S] expresses this goal as the existence of two scalar
coefficients. Supply your chosen coefficients, then verify the vector identity.
vector_simp [b, u, v] handles the pointwise representation and numerical check.
The tool constructs the underlying finite-set coefficient function for you.

References:
- LinearAlgebra/Lectures/Class_2.lean, equality, finite cases, and finite sums.
- LinearAlgebra/Lectures/Class_4.lean, funAdd and funSMul.
- LinearAlgebra/Lectures/Class_5.lean, LinearCombination and IsLinearCombination.
-/

def u : Fin 3 → ℝ := ![1, 1, 0]
def v : Fin 3 → ℝ := ![0, 1, 1]
def b : Fin 3 → ℝ := ![2, 1, -1]
noncomputable def S : Finset (Fin 3 → ℝ) := {u, v}

theorem q1_linear_combination :
    IsLinearCombination (function_space_axioms (Fin 3)) S b := by
  sorry

/-!
## Question 2 — Recover vectors from their combinations
Basic · 10 points · about 20 minutes

Objective: find useful linear combinations before applying subspace closure.

Let W be a subspace of ℝ³. Suppose u + v ∈ W and 2 • u - v ∈ W.
Prove that both u and v belong to W.

First express u and v as linear combinations of the two given vectors.
Then use the addition and scalar-multiplication properties of W.
The supplied subspace_properties theorem makes those properties available.

Hint: reason with the two given combinations as whole vectors.
For an identity between vectors in ℝ³, vector_simp can expose the pointwise
scalar calculation. Use explicit algebraic steps to justify the identity;
distributivity is not supplied automatically.

References:
- LinearAlgebra/Lectures/Class_1.lean, solving small linear systems.
- LinearAlgebra/Lectures/Class_2.lean, conjunctions and intermediate statements.
- LinearAlgebra/Lectures/Class_5.lean, LinearCombination and subspace_test.
-/

theorem q2_recover_vectors
    (W : Set (Fin 3 → ℝ))
    (hW : IsVectorSubspace (function_space_axioms (Fin 3)) W)
    (u v : Fin 3 → ℝ)
    (h₁ : u + v ∈ W) (h₂ : (2 : ℝ) • u - v ∈ W) :
    u ∈ W ∧ v ∈ W := by
  sorry

/-!
## Question 3 — A homogeneous system defines a subspace
Medium · 15 points · about 20 minutes

Objective: prove that two simultaneous homogeneous constraints are preserved
by vector-space operations.

Let W be the set of x = (x₀,x₁,x₂) ∈ ℝ³ satisfying both equations
  x₀ + 2x₁ - x₂ = 0,
  2x₀ - x₁ = 0.
Prove that W is a subspace of ℝ³ using subspace_test.

Show that the zero vector satisfies both equations, and that addition
and scalar multiplication preserve both equations.
Keep the two constraints visible in your written argument and Lean proof.

Hint: membership in systemSolutions is a conjunction. vector_simp can
express pointwise operations in coordinates after you introduce the relevant
vectors. In the closure calculations, show the distributive step explicitly
before using linarith or linear_combination to finish the scalar equations.

References:
- LinearAlgebra/Lectures/Class_1.lean, linear systems.
- LinearAlgebra/Lectures/Class_2.lean, conjunctions and arithmetic tactics.
- LinearAlgebra/Lectures/Class_5.lean, homogeneousSolutions and subspace_test.
-/

def systemSolutions : Set (Fin 3 → ℝ) :=
  {x | x 0 + 2 * x 1 - x 2 = 0 ∧ 2 * x 0 - x 1 = 0}

theorem q3_system_subspace :
    IsVectorSubspace (function_space_axioms (Fin 3)) systemSolutions := by
  sorry

/-!
## Question 4 — Periodic function vectors
Medium · 15 points · about 20 minutes

Objective: apply the subspace test to a space of functions.

Let P be the set of functions f : ℝ → ℝ such that
  f (x + 1) = f x for every real x.
Prove that P is a subspace of the real vector space ℝ → ℝ.

The condition requires 1 to be a period; it does not require 1 to be the
smallest positive period. Constant functions also satisfy the condition.

Use subspace_test and verify the zero, addition, and scalar-multiplication
conditions. In each closure argument, compare function values at x + 1
and x for an arbitrary x.

Hint: after introducing the functions and x, vector_simp exposes the
pointwise real-valued expressions. Apply the membership hypotheses at x
explicitly to finish the closure arguments.

References:
- LinearAlgebra/Lectures/Class_2.lean, universal hypotheses and rewriting.
- LinearAlgebra/Lectures/Class_4.lean, funAdd, funSMul, and F_is_vector_space.
- LinearAlgebra/Lectures/Class_5.lean, subspace_test and ODESolutions.
-/

def periodicFunctions : Set (ℝ → ℝ) :=
  {f | ∀ x : ℝ, f (x + 1) = f x}

theorem q4_periodic_subspace :
    IsVectorSubspace (function_space_axioms ℝ) periodicFunctions := by
  sorry

/-!
## Question 5 — Intersection of subspaces
Medium · 20 points · about 20 minutes

Objective: prove a general subspace construction from the defining properties.

Let U and W be subspaces of a vector space V over a field K.
Prove that U ∩ W is a subspace of V.

Use subspace_test and justify all three conditions:
- the zero vector belongs to U ∩ W;
- U ∩ W is closed under addition;
- U ∩ W is closed under scalar multiplication.

You may use subspace_properties to obtain the closure facts for U and W.
Give the argument for arbitrary subspaces; no generators are specified.

Hint: membership in U ∩ W means membership in U and membership in W.
The hypotheses on V are the course's custom axioms; a Mathlib Module
instance is not assumed.

References:
- LinearAlgebra/Lectures/Class_2.lean, conjunctions in goals and hypotheses.
- LinearAlgebra/Lectures/Class_5.lean, IsVectorSubspace and subspace_test.
-/

theorem q5_intersection_subspace
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (U W : Set V)
    (hU : IsVectorSubspace hV U) (hW : IsVectorSubspace hV W) :
    IsVectorSubspace hV (U ∩ W) := by
  sorry

/-!
## Question 6 — Span is the smallest containing subspace
Hard · 30 points · about 50 minutes

Objective: connect the finite-linear-combination definition of Span with
its characterization as the smallest subspace containing the generators.

Let X be any subset of a vector space V over K. Prove all three statements:
1. X ⊆ Span hV X.
2. Span hV X is a subspace of V.
3. If W is any subspace of V and X ⊆ W, then Span hV X ⊆ W.

For statement 1, construct a singleton finite set and its coefficients
directly from the definition of Span. Do not cite mem_span_of_mem.
For statement 2, you may use span_is_subspace from Class 5.
For statement 3, obtain a finite linear combination representing a vector
in Span hV X. Show that each scalar multiple belongs to W, then use the
supplied finite-sum closure theorem subspace_sum_mem from CourseTools.

Hint: subspace_properties gives the scalar-multiplication closure fact for W.
The supplied theorem subspace_sum_mem hW I f hf proves
  (∑ i ∈ I, f i) ∈ W
when hf proves ∀ i ∈ I, f i ∈ W. This includes the empty sum.
The definition LinearCombination hV S a is ∑ t : S, a t • (t : V).
For this sum, take I = Finset.univ on the index type S. An index t : S
carries the fact t.property : (t : V) ∈ S; use it to show (t : V) ∈ X,
then (t : V) ∈ W, and finally a t • (t : V) ∈ W.

The set X may be empty or infinite. Do not assume that X itself is a Finset.
Use the course definition Span, not Submodule.span.

References:
- LinearAlgebra/Lectures/Class_2.lean, existential witnesses and finite sums.
- LinearAlgebra/Lectures/Class_5.lean, Span, LinearCombination,
  IsVectorSubspace, and span_is_subspace.
-/

theorem q6_span_smallest_subspace
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (X : Set V) :
    X ⊆ Span hV X ∧
    IsVectorSubspace hV (Span hV X) ∧
    (∀ W : Set V, IsVectorSubspace hV W → X ⊆ W → Span hV X ⊆ W) := by
  sorry

end Homework5
