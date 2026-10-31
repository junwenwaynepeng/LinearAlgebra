import Mathlib
import LinearAlgebra.CourseTools

/-! Linear independence, dependence, and adjoining a vector. -/

open scoped Classical

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
  ¬ IsLinearlyIndependent hV S

/-- A set containing a dependent set is dependent. -/
lemma linearly_dependent_trans
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (S₁ S₂ : Finset V) (hS : S₁ ⊆ S₂)
    (hdep : IsLinearlyDependent hV S₁) :
    IsLinearlyDependent hV S₂ := by
  unfold IsLinearlyDependent IsLinearlyIndependent at *
  push Not at *
  obtain ⟨a, hsum, ha⟩ := hdep
  -- Give the additional vectors coefficient zero.
  let a' : S₂ → K :=
    fun v => if h : (v : V) ∈ S₁ then a ⟨(v : V), h⟩ else 0
  have hsum' : LinearCombination hV S₂ a' = 0 := by
    calc
      LinearCombination hV S₂ a' = LinearCombination hV S₁ a :=
        linearCombination_extendCoefficients hV S₁ S₂ a hS
      _ = 0 := hsum
  have ha' : a' ≠ 0 := extendCoefficients_ne_zero hS ha
  exact ⟨a', hsum', ha'⟩

/-- Every subset of an independent set is independent. -/
lemma linearly_independent_subset
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (S₁ S₂ : Finset V) (hS : S₁ ⊆ S₂)
    (hind : IsLinearlyIndependent hV S₂) :
    IsLinearlyIndependent hV S₁ := by
  contrapose hind
  exact linearly_dependent_trans hV S₁ S₂ hS hind

/-- Adding a vector outside the span preserves linear independence. -/
lemma linearly_ind_add_vector
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (S : Finset V) (v : V)
    (hS : IsLinearlyIndependent hV S)
    (hv : v ∉ Span hV (S : Set V)) :
    IsLinearlyIndependent hV (S ∪ {v}) := by
  have hvS : v ∉ S := by
    intro hvS
    exact hv (mem_span_of_mem hV hvS)
  -- Start with an arbitrary zero linear combination of S ∪ {v}.
  intro a hsum
  obtain ⟨c, b, hsplit, hzero⟩ := linearCombination_union_singleton hV S v hvS a
  have hrelation : c • v + LinearCombination hV S b = 0 := by
    rw [← hsplit]
    exact hsum
  by_cases hc : c = 0
  · -- Independence of S forces all the remaining coefficients to vanish.
    have hb : b = 0 := hS b (by
      simpa [hc, zero_smul_V hV] using hrelation)
    exact hzero.mpr ⟨hc, hb⟩
  · -- A nonzero coefficient of v would express v as a combination of S.
    exfalso
    have hv' : IsLinearCombination hV S v := by
      let d : S → K := fun u => -b u / c
      have hd : d = fun u => (-(c⁻¹)) * b u := by
        funext u
        dsimp [d]
        ring
      refine ⟨d, ?_⟩
      calc
        v = c⁻¹ • (c • v) := by
          rw [← hV.mul_smul, inv_mul_cancel₀ hc, hV.one_smul]
        _ = c⁻¹ • (-LinearCombination hV S b) := by
          rw [eq_neg_of_add_eq_zero_V hV hrelation]
        _ = (-(c⁻¹)) • LinearCombination hV S b := by
          rw [← neg_one_smul_V hV, ← hV.mul_smul]
          congr 1
          ring
        _ = LinearCombination hV S d := by
          simp only [hd, linearCombination_smul_V]
    exact hv hv'.mem_span

theorem linearly_independent_iff_unique_solution
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (S : Finset V):
    IsLinearlyIndependent hV S ↔ ∀ u ∈ Span hV S, ∃! (a : S → K), u = LinearCombination hV S a := by
  constructor
  · intro hS
    by_contra!
    obtain ⟨u, hu, hu'⟩ := this
    push Not at hu'


  · intro huniuqe
    hunique 0
