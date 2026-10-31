import Mathlib
import LinearAlgebra.CourseTools
/-! Linear combinations and vector subspaces. -/

open scoped BigOperators

namespace Class5


def LinearCombination
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (_ : VectorSpaceAxioms V K)
    (S : Finset V)
    (a : S → K) : V :=
  ∑ v : S, a v • v

def IsLinearCombination
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (S : Finset V) (b : V) : Prop :=
  ∃ a : S → K, b = LinearCombination hV S a

def Span
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (_ : VectorSpaceAxioms V K) (X : Set V) : Set V :=
  {w | ∃ (S : Finset X) (a : S → K),
    w = ∑ v : S, a v • (v : V)}


/-
↥ (\u-|): v : ↥W means v is a type V (above W), and v is in V

↑ (\u-): ↑v means it original in W, but now treat it like in V
-/

def IsVectorSubspace
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (_ : VectorSpaceAxioms V K)
    (W : Set V) : Prop :=
  ∃ (addW : Add W)
    (zeroW : Zero W)
    (negW : Neg W)
    (smulW : SMul K W),
    @VectorSpaceAxioms W K _
      addW zeroW negW smulW ∧
    (∀ u v : W,
      ((addW.add u v : W) : V) =
        (u : V) + (v : V)) ∧
    (((zeroW.zero : W) : V) = (0 : V)) ∧
    (∀ u : W,
      ((negW.neg u : W) : V) = -(u : V)) ∧
    (∀ (a : K) (u : W),
      ((smulW.smul a u : W) : V) =
        a • (u : V))

theorem subspace_test
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (W : Set V)
    (has_zero : (0 : V) ∈ W)
    (add_close :
      ∀ u v : V, u ∈ W → v ∈ W → u + v ∈ W)
    (smul_close :
      ∀ (a : K) (v : V), v ∈ W → a • v ∈ W) :
    IsVectorSubspace hV W:= by
  let addW : Add W :=
    ⟨fun u v =>
      ⟨(u : V) + (v : V),
        add_close (u : V) (v : V) u.property v.property⟩⟩
  let zeroW : Zero W :=
    ⟨⟨0, has_zero⟩⟩
  let smulKW : SMul K W :=
    ⟨fun a v =>
      ⟨a • (v : V),
        smul_close a (v : V) v.property⟩⟩
  let negW : Neg W :=
    ⟨fun v =>
      ⟨(-v : V), by
        have hneg : (-1 : K) • (v : V) = -(v : V) :=
          cancellation_law hV _ _ (v : V) (by
            rw [neg_one_smul_V hV, hV.neg_add_cancel])
        rw [← hneg]
        exact smul_close (-1 : K) (v : V) v.property⟩⟩
  have W_is_vector_space : VectorSpaceAxioms (↥W) K :={
      add_assoc := by
        intro u v w
        apply Subtype.ext
        exact hV.add_assoc u v w
      add_comm := by
        intro u v
        apply Subtype.ext
        exact hV.add_comm u v
      zero_add := by
        intro u
        apply Subtype.ext
        exact hV.zero_add u
      neg_add_cancel := by
        intro u
        apply Subtype.ext
        exact hV.neg_add_cancel u
      one_smul := by
        intro u
        apply Subtype.ext
        exact hV.one_smul u
      mul_smul := by
        intro a b u
        apply Subtype.ext
        exact hV.mul_smul a b u
      smul_add := by
        intro a u v
        apply Subtype.ext
        exact hV.smul_add a u v
      add_smul := by
        intro a b u
        apply Subtype.ext
        exact hV.add_smul a b u
    }
  refine ⟨addW, zeroW, negW, smulKW, W_is_vector_space, ?_, ?_, ?_, ?_ ⟩
  · intro u v
    rfl
  · rfl
  · intro u
    rfl
  · intro a u
    rfl

theorem span_is_subspace
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V] [DecidableEq V]
    (hV : VectorSpaceAxioms V K) (X : Set V) :
    IsVectorSubspace hV (Span hV X) := by
  apply subspace_test hV (Span hV X)
  · refine ⟨∅, (fun _ => 0), ?_⟩
    simp
  · intro u v hu hv
    obtain ⟨S, a, ha⟩ := hu
    obtain ⟨T, b, hb⟩ := hv
    let U : Finset X := S ∪ T
    let a' : U → K := extendCoefficients S U a
    let b' : U → K := extendCoefficients T U b
    have ha' : (∑ s : U, a' s • (s : V)) = ∑ s : S, a s • (s : V) :=
      sum_extendCoefficients_smul hV S U a Finset.subset_union_left
        (fun x : X => (x : V))
    have hb' : (∑ s : U, b' s • (s : V)) = ∑ s : T, b s • (s : V) :=
      sum_extendCoefficients_smul hV T U b Finset.subset_union_right
        (fun x : X => (x : V))
    refine ⟨U, (fun s => a' s + b' s), ?_⟩
    rw [ha, hb, ← ha', ← hb']
    simp only [hV.add_smul, Finset.sum_add_distrib]
  · intro c v hv
    obtain ⟨S, a, ha⟩ := hv
    refine ⟨S, (fun s => c * a s), ?_⟩
    rw [ha, smul_sum_V hV]
    simp only [hV.mul_smul]

end Class5

-- These examples use their own namespace so Class 5 compiles independently.
namespace Class5Examples

structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

abbrev V := Vec3

-- Step 1: Define the operations and distinguished vectors.

def vectorAdd (u v : Vec3) : Vec3 :=
  ⟨u.x + v.x, u.y + v.y, u.z +v.z⟩

def scalarMul (a : ℝ) (v : Vec3) : Vec3 :=
  ⟨a * v.x, a * v.y, a * v.z⟩

def zeroVector : Vec3 :=
  ⟨0, 0, 0⟩

def vectorNeg (v : Vec3) : Vec3 :=
  ⟨-v.x, -v.y, -v.z⟩

-- Step 2: Verify the vector space axioms.

instance : Add Vec3 := ⟨vectorAdd⟩
instance : Zero Vec3 := ⟨zeroVector⟩
instance : Neg Vec3 := ⟨vectorNeg⟩
instance : SMul ℝ Vec3 := ⟨scalarMul⟩

theorem vector_add_eq (u v : V) :
    u + v = vectorAdd u v := by
  rfl

theorem zero_vector : 0 = zeroVector := by
  rfl

theorem smul (a : ℝ) (v : V) : a•v = scalarMul a v :=by
  rfl

theorem neg_vector (v : V) : -v = vectorNeg v := by
  rfl

theorem V_is_vector_space : VectorSpaceAxioms V ℝ where
  add_assoc := by
    intro u v w
    repeat rw [vector_add_eq]
    unfold vectorAdd
    simp?
    refine ⟨?_,?_,?_⟩<;>ring

  add_comm := by
    intro u v
    repeat rw [vector_add_eq]
    unfold vectorAdd
    simp?
    refine ⟨?_,?_,?_⟩<;>ring

  zero_add := by
    intro v
    rw [zero_vector, vector_add_eq]
    unfold vectorAdd zeroVector
    simp

  neg_add_cancel := by
    intro v
    change vectorAdd (vectorNeg v) v = zeroVector
    unfold vectorAdd vectorNeg zeroVector
    simp

  smul_add := by
    intro a u v
    change scalarMul a (vectorAdd u v) =
      vectorAdd (scalarMul a u) (scalarMul a v)
    unfold scalarMul vectorAdd
    simp?
    refine ⟨?_,?_,?_⟩<;>ring

  add_smul := by
    intro a b v
    change scalarMul (a + b) v = vectorAdd (scalarMul a v) (scalarMul b v)
    unfold scalarMul vectorAdd
    simp?
    refine ⟨?_,?_,?_⟩<;>ring

  mul_smul := by
    intro a b v
    change scalarMul (a * b) v =
      scalarMul a (scalarMul b v)
    unfold scalarMul
    simp?
    refine ⟨?_,?_,?_⟩<;>ring

  one_smul := by
    intro v
    change scalarMul 1 v = v
    unfold scalarMul
    simp

theorem F_is_vector_space (X : Type*) :
    VectorSpaceAxioms (X → ℝ) ℝ where
  add_comm := add_comm
  add_assoc := add_assoc
  zero_add := zero_add
  neg_add_cancel := neg_add_cancel
  one_smul := one_smul ℝ
  mul_smul := mul_smul
  smul_add := smul_add
  add_smul := add_smul

end Class5Examples

open Class5Examples

/-- `y` is a twice-differentiable solution of
    y'' + 2y' - 3y = 0. -/
def IsODESolution (y : ℝ → ℝ) : Prop :=
  ∃ y' y'' : ℝ → ℝ,
    (∀ x, HasDerivAt y (y' x) x) ∧
    (∀ x, HasDerivAt y' (y'' x) x) ∧
    (∀ x, y'' x + 2 * y' x - 3 * y x = 0)

def ODESolutions : Set (ℝ → ℝ) :=
  {y | IsODESolution y}

lemma ode_zero_mem :
    (0 : ℝ → ℝ) ∈ ODESolutions := by
  change IsODESolution (fun _ => 0)
  refine ⟨(fun _ => 0), (fun _ => 0), ?_, ?_, ?_⟩
  · intro x
    simpa using
      (hasDerivAt_const (x := x) (c := (0 : ℝ)))
  · intro x
    simpa using
      (hasDerivAt_const (x := x) (c := (0 : ℝ)))
  · intro x
    simp

lemma ode_add_mem
    (y z : ℝ → ℝ)
    (hy : y ∈ ODESolutions)
    (hz : z ∈ ODESolutions) :
    y + z ∈ ODESolutions := by
  change IsODESolution (fun x => y x + z x)

  rcases hy with ⟨y', y'', hy', hy'', hyEq⟩
  rcases hz with ⟨z', z'', hz', hz'', hzEq⟩

  refine
    ⟨(fun x => y' x + z' x),
     (fun x => y'' x + z'' x), ?_, ?_, ?_⟩

  · intro x
    exact (hy' x).fun_add (hz' x)

  · intro x
    exact (hy'' x).fun_add (hz'' x)

  · intro x
    linear_combination hyEq x + hzEq x

lemma ode_smul_mem
    (a : ℝ)
    (y : ℝ → ℝ)
    (hy : y ∈ ODESolutions) :
    a • y ∈ ODESolutions := by
  change IsODESolution (fun x => a * y x)

  rcases hy with ⟨y', y'', hy', hy'', hyEq⟩

  refine
    ⟨(fun x => a * y' x),
     (fun x => a * y'' x), ?_, ?_, ?_⟩

  · intro x
    exact HasDerivAt.const_mul a (hy' x)

  · intro x
    exact HasDerivAt.const_mul a (hy'' x)

  · intro x
    linear_combination a * hyEq x

theorem ode_solutions_are_subspace :
    IsVectorSubspace (F_is_vector_space ℝ) ODESolutions := by
  exact
    subspace_test
      (F_is_vector_space ℝ)
      ODESolutions
      ode_zero_mem
      ode_add_mem
      ode_smul_mem

def homogeneousSolutions : Set Vec3 :=
  {v | v.x + 2 * v.y - v.z = 0}

lemma homogeneous_zero_mem :
    (0 : Vec3) ∈ homogeneousSolutions := by
  change (0 : ℝ) + 2 * 0 - 0 = 0
  norm_num

lemma homogeneous_add_mem
    (u v : Vec3)
    (hu : u ∈ homogeneousSolutions)
    (hv : v ∈ homogeneousSolutions) :
    u + v ∈ homogeneousSolutions := by

  change
    (u.x + v.x) +
      2 * (u.y + v.y) -
      (u.z + v.z) = 0

  change u.x + 2 * u.y - u.z = 0 at hu
  change v.x + 2 * v.y - v.z = 0 at hv

  linarith

lemma homogeneous_smul_mem
    (a : ℝ) (v : Vec3)
    (hv : v ∈ homogeneousSolutions) :
    a • v ∈ homogeneousSolutions := by

  change
    a * v.x +
      2 * (a * v.y) -
      a * v.z = 0

  change v.x + 2 * v.y - v.z = 0 at hv

  linear_combination a * hv

theorem homogeneous_solutions_are_subspace :
    IsVectorSubspace V_is_vector_space homogeneousSolutions := by
  exact
    subspace_test
      V_is_vector_space
      homogeneousSolutions
      homogeneous_zero_mem
      homogeneous_add_mem
      homogeneous_smul_mem
