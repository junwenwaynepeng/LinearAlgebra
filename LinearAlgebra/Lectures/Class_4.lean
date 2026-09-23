import Mathlib

/-! Axioms characterizing a vector space over a field. -/

structure VectorSpaceAxioms
    (K V : Type*) [Field K] [Add V] [Zero V] [Neg V] [SMul K V] : Prop
where
  -- Vector addition
  add_comm : ∀ u v : V, u + v = v + u
  add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w)
  add_zero : ∀ v : V, v + 0 = v
  neg_add_cancel : ∀ v : V, -v + v = 0

  -- Scalar multiplication
  one_smul : ∀ v : V, (1 : K) • v = v
  mul_smul : ∀ (a b : K) (v : V),
    (a * b) • v = a • (b • v)
  smul_add : ∀ (a : K) (u v : V),
    a • (u + v) = a • u + a • v
  add_smul : ∀ (a b : K) (v : V),
    (a + b) • v = a • v + b • v


-- The set of ordered triples of real numbers.
abbrev V := ℝ × ℝ × ℝ

-- Step 1: Define the operations and distinguished vectors.

def vectorAdd (u v : V) : V :=
  (u.1 + v.1, u.2.1 + v.2.1, u.2.2 +v.2.2)

def scalarMul (a : ℝ) (v : V) : V :=
  (a * v.1, a * v.2.1, a * v.2.2)

def zeroVector : V :=
  (0, 0, 0)

def vectorNeg (v : V) : V :=
  (-v.1, -v.2.1, -v.2.2)

-- Step 2: Verify the vector space axioms.

local instance : Add V := ⟨vectorAdd⟩
local instance : Zero V := ⟨zeroVector⟩
local instance : Neg V := ⟨vectorNeg⟩
local instance : SMul ℝ V := ⟨scalarMul⟩

theorem V_is_vector_space : VectorSpaceAxioms ℝ V where
  add_assoc := by
    intro u v w
    change vectorAdd (vectorAdd u v) w =
      vectorAdd u (vectorAdd v w)
    ext <;> unfold vectorAdd <;> ring

  add_comm := by
    intro u v
    change vectorAdd u v = vectorAdd v u
    ext<;> unfold vectorAdd <;> ring

  zero_add := by
    intro v
    change vectorAdd zeroVector v = v
    unfold vectorAdd zeroVector
    simp

  add_zero := by
    intro v
    change vectorAdd v zeroVector = v
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
    simp
    constructor
    · ring
    · constructor <;> ring

  add_smul := by
    intro a b v
    change scalarMul (a + b) v = vectorAdd (scalarMul a v) (scalarMul b v)
    unfold scalarMul vectorAdd
    simp
    constructor
    · ring
    · constructor <;> ring

  mul_smul := by
    intro a b v
    change scalarMul (a * b) v =
      scalarMul a (scalarMul b v)
    unfold scalarMul
    simp
    constructor
    · ring
    · constructor <;> ring

  one_smul := by
    intro v
    change scalarMul 1 v = v
    unfold scalarMul
    simp
