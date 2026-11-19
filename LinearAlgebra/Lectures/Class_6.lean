import Mathlib
import LinearAlgebra.CourseTools
import LinearAlgebra.VectorSimp

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
    (hV : VectorSpaceAxioms V K) (S : Finset V) :
    IsLinearlyIndependent hV S ↔ ∀ u ∈ Span hV S, ∃! (a : S → K), u = LinearCombination hV S a := by
  constructor
  · intro hS
    by_contra!
    obtain ⟨u, hu, hu'⟩ := this
    unfold ExistsUnique at hu'
    push Not at hu'
    obtain ⟨a, ha⟩ := IsLinearCombination.of_mem_span hV hu
    obtain ⟨b, hb, hab⟩ := hu' a ha
    let a_mins_b : S → K := fun (u : S) => a u - b u
    have hzero : 0 = LinearCombination hV S a_mins_b :=by
      calc
        0 = (-1 : K) • u + u := (neg_one_smul_add_V hV u).symm
        _ = u + (-1 : K) • u := (hV.add_comm ((-1 : K) • u) u)
        _ = (LinearCombination hV S a) + (-1 : K) • u := by rw [ha]
        _ = (LinearCombination hV S a) + (-1 : K) • (LinearCombination hV S b) := by rw [hb]
        _ = (LinearCombination hV S a) + (LinearCombination hV S (fun v => (-1 : K) * b v)) :=by rw [(linearCombination_smul_V hV S b (-1 : K)).symm]
        _ = (LinearCombination hV S (a + (fun v => (-1 : K) * b v))) := (linearCombination_add_V hV S a (fun v => (-1 : K) * b v)).symm
        _ = LinearCombination hV S a_mins_b := by
          congr 1
          funext v
          simp [a_mins_b]
          ring
    have ha_mins_b : a_mins_b ≠ 0 := by
      intro h
      have hab' : a = b := by
        funext v
        have hv : a v - b v = 0 := congrFun h v
        exact sub_eq_zero.mp hv
      exact hab hab'.symm
    have hS' : IsLinearlyDependent hV S := by
      unfold IsLinearlyDependent
      unfold IsLinearlyIndependent
      push Not
      use a_mins_b
      exact ⟨hzero.symm, ha_mins_b⟩
    contradiction
  · unfold IsLinearlyIndependent
    intro hunique a ha
    let zero : S → K := fun (u : S) => 0
    have hzero : 0 = LinearCombination hV S zero := by
      simp [LinearCombination, zero, zero_smul_V hV]
    have h0 : (0 : V) ∈ Span hV (S : Set V) :=
      ⟨S, Set.Subset.rfl, zero, hzero⟩
    have hazero : a = zero :=
      (hunique 0 h0).unique ha.symm hzero
    exact hazero


/-!
# In-class practice — linear independence and unique representations

Plan: about 35–40 minutes. Work through Practices 1–3 together; Practices
4–6 can be completed in pairs or used for discussion if time is short.
Before each Lean proof, explain the mathematical argument in one or two
sentences. The exercises use the course definitions from this lecture.

The supplied facts below handle the finite-set coefficient bookkeeping.
Use vector_simp [u, v, ...] to check a chosen vector equality. When using
an equality hypothesis h, congrFun h i gives the equality at coordinate i;
norm_num [u, v, ...] at hi exposes its scalar equation.
-/

namespace Class6Practice

abbrev Vec3 := Fin 3 → ℝ

noncomputable local instance : DecidableEq Vec3 := Classical.decEq _

/-- Supplied: the pointwise operations on coordinate vectors satisfy the axioms. -/
theorem vector_axioms : VectorSpaceAxioms Vec3 ℝ where
  add_comm := add_comm
  add_assoc := add_assoc
  zero_add := zero_add
  neg_add_cancel := neg_add_cancel
  one_smul := one_smul ℝ
  mul_smul := mul_smul
  smul_add := smul_add
  add_smul := add_smul

def u : Vec3 := ![1, 1, 0]
def v : Vec3 := ![1, 0, 1]
def w : Vec3 := ![2, 1, 1]
def z : Vec3 := ![1, 0, 0]
def p : Vec3 := ![5, 2, 3]

/-- Supplied: translate finite-set independence into the usual two-scalar test.
The hypothesis u ≠ v ensures that the finite set has two elements. -/
lemma independent_pair_iff
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (u v : V) (huv : u ≠ v) :
    IsLinearlyIndependent hV {u, v} ↔
      ∀ a b : K, a • u + b • v = 0 → a = 0 ∧ b = 0 := by
  constructor
  · intro hind a b hsum
    let c : ({u, v} : Finset V) → K :=
      fun t => if (t : V) = u then a else b
    have hc_sum : LinearCombination hV {u, v} c = 0 := by
      unfold LinearCombination
      rw [VectorSimp.sum_pair_subtype u v huv]
      simpa [c, Ne.symm huv] using hsum
    have hc : c = 0 := hind c hc_sum
    constructor
    · simpa [c] using congrFun hc ⟨u, by simp⟩
    · simpa [c, Ne.symm huv] using congrFun hc ⟨v, by simp⟩
  · intro h a hsum
    have hpair : a ⟨u, by simp⟩ • u + a ⟨v, by simp⟩ • v = 0 := by
      simpa only [LinearCombination, VectorSimp.sum_pair_subtype u v huv] using hsum
    obtain ⟨hu, hv⟩ := h _ _ hpair
    funext t
    change a t = 0
    have ht : (t : V) = u ∨ (t : V) = v := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using t.property
    rcases ht with ht | ht
    · have ht' : t = ⟨u, by simp⟩ := Subtype.ext ht
      rw [ht']
      exact hu
    · have ht' : t = ⟨v, by simp⟩ := Subtype.ext ht
      rw [ht']
      exact hv

/-- Supplied: membership in the span of u and v means a two-term expression. -/
lemma mem_span_uv_iff (x : Vec3) :
    x ∈ Span vector_axioms ({u, v} : Finset Vec3) ↔
      ∃ a b : ℝ, x = a • u + b • v := by
  rw [VectorSimp.mem_span_finset_iff, VectorSimp.isLinearCombination_pair_iff]

/-- Supplied: u and v are distinct, as their coordinate 1 values differ. -/
lemma u_ne_v : u ≠ v := by
  intro h
  have h1 := congrFun h 1
  norm_num [u, v] at h1

/-!
## Practice 1 — Which coordinates force the coefficients to vanish?
Basic · about 5 minutes

Show that a u + b v = 0 forces a = b = 0. Choose two useful coordinates
and explain your choice. Hint: obtain scalar equations using congrFun;
then use norm_num [u, v] at those equations.
-/
theorem practice1_zero_coefficients (a b : ℝ)
    (h : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
  sorry

/-!
## Practice 2 — Turn the coordinate argument into independence
Basic · about 3 minutes

Use independent_pair_iff, u_ne_v, and Practice 1 to prove independence
in the lecture's finite-set definition. Explain why testing the zero
linear combination is enough.
-/
theorem practice2_pair_independent :
    IsLinearlyIndependent vector_axioms {u, v} := by
  sorry

/-!
## Practice 3 — Find a nontrivial relation
Basic · about 5 minutes

Find a, b, c with a ≠ 0 such that a u + b v + c w = 0. Choose the scalars
before calculating. Explain in words why your relation shows that
{u, v, w} is dependent, although {u, v} is independent.
Hint: after choosing the scalars, vector_simp [u, v, w] checks the equality.
-/
theorem practice3_nontrivial_relation :
    ∃ a b c : ℝ, a ≠ 0 ∧ a • u + b • v + c • w = 0 := by
  sorry

/-!
## Practice 4 — Why is the zero vector special?
Medium · about 6 minutes

Prove that {0} is dependent in any vector space from this lecture.
Use the definition: assign its only vector coefficient 1. The sum is zero,
but this coefficient function is not the zero function.
Hint: simp [LinearCombination, smul_zero_V hV] checks the zero sum.
If two coefficient functions are equal, congrFun h ⟨0, by simp⟩ compares
their values at the zero vector. In discussion, use the subset theorem
above to explain why an independent set cannot contain 0.
-/
theorem practice4_zero_singleton_dependent
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) :
    IsLinearlyDependent hV {(0 : V)} := by
  sorry

/-!
## Practice 5 — Can we adjoin z?
Medium · about 10 minutes

Prove that adjoining z to {u, v} preserves independence. Use
linearly_ind_add_vector and Practice 2. The mathematical task is to show
z ∉ Span vector_axioms {u, v}.
Hint: if hz is span membership, (mem_span_uv_iff z).mp hz gives a and b
with z = a • u + b • v. Compare coordinates 1, 2, and then 0 to find a
contradiction. Explain why adjoining w in Practice 3 behaves differently.
-/
theorem practice5_adjoin_vector :
    IsLinearlyIndependent vector_axioms
      (({u, v} : Finset Vec3) ∪ {z}) := by
  sorry

/-!
## Practice 6 — Existence and uniqueness do different jobs
Medium · about 8 minutes

First find scalars a and b with p = a • u + b • v, so that p belongs
to the span. Then use Practice 2 and
linearly_independent_iff_unique_solution to prove that its coefficient
function is unique. Explain which step supplies existence and which
supplies uniqueness. Use mem_span_uv_iff to construct span membership;
use its two scalar coefficients as the span-membership witness.
-/
theorem practice6_unique_representation :
    ∃! a : ({u, v} : Finset Vec3) → ℝ,
      p = LinearCombination vector_axioms {u, v} a := by
  sorry

end Class6Practice
