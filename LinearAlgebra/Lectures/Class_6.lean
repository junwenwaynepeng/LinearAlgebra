import Mathlib
import LinearAlgebra.CourseTools
open scoped BigOperators

/-!-/

def IsLinearlyIndependent
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (S : Finset V) : Prop :=
  ∀ (a : S → K), LinearCombination hV S a = 0 → a = 0

def IsLinearlyDependent
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (S : Finset V) : Prop :=
  Not (IsLinearlyIndependent hV S)

lemma LinearlyDependentTrans
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    [DecidableEq V]
    (hV : VectorSpaceAxioms V K)
    (S₁ S₂ : Finset V) (hS : S₁ ⊆ S₂)
    (hS' : IsLinearlyDependent hV S₁) :
    IsLinearlyDependent hV S₂ := by
  unfold IsLinearlyDependent at *
  unfold IsLinearlyIndependent at *
  push Not at *
  obtain ⟨a, sum_a_v, ha⟩ := hS'
  let a' : S₂ → K := fun v => if h : (v : V) ∈ S₁ then a ⟨v, h⟩ else 0
  have hext : LinearCombination hV S₂ a' = 0 := by
    calc
      LinearCombination hV S₂ a' =
          LinearCombination hV S₁ a :=
        sum_extendCoefficients_V hV S₁ S₂ a hS
      _ = 0 := sum_a_v
  have ha' : a' ≠ 0 := extendCoefficients_ne_zero hS ha
  use a'

lemma LinearlyIndependentDome
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    [DecidableEq V]
    (hV : VectorSpaceAxioms V K)
    (S₁ S₂ : Finset V) (hS : S₁ ⊆ S₂)
    (hS' : IsLinearlyIndependent hV S₂) :
    IsLinearlyIndependent hV S₁ := by
  contrapose hS'
  exact LinearlyDependentTrans hV S₁ S₂ hS hS'

/-- Adding a vector outside the span preserves linear independence. -/
lemma LinearlyIndependentInsert
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    [DecidableEq V]
    (hV : VectorSpaceAxioms V K)
    (S : Finset V) (v : V)
    (hS : IsLinearlyIndependent hV S)
    (hv : v ∉ Span hV (S : Set V)) :
    IsLinearlyIndependent hV (insert v S) := by
