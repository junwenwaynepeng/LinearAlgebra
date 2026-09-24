import Mathlib

/-! Axioms characterizing a vector space over a field. -/

structure VectorSpaceAxioms
    (K V : Type*) [Field K] [Add V] [Zero V] [Neg V] [SMul K V] : Prop
where
  -- Vector addition
  add_comm : ∀ u v : V, u + v = v + u
  add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w)
  zero_add : ∀ v : V, 0 + v = v
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
--abbrev V := ℝ × ℝ × ℝ

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

local instance : Add Vec3 := ⟨vectorAdd⟩
local instance : Zero Vec3 := ⟨zeroVector⟩
local instance : Neg Vec3 := ⟨vectorNeg⟩
local instance : SMul ℝ Vec3 := ⟨scalarMul⟩

theorem vector_add_eq (u v : V) :
    u + v = vectorAdd u v := by
  rfl

theorem zero_vector : 0 = zeroVector := by
  rfl

theorem smul (a : ℝ) (v : V) : a•v = scalarMul a v :=by
  rfl

theorem neg_vector (v : V) : -v = vectorNeg v := by
  rfl

theorem V_is_vector_space : VectorSpaceAxioms ℝ V where
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

noncomputable section

abbrev P := Polynomial ℝ

noncomputable def polyAdd (p q : P) : P :=
  ∑ n ∈ Finset.range (max p.natDegree q.natDegree +1), Polynomial.monomial n (p.coeff n + q.coeff n)

noncomputable def polySMul (a : ℝ) (p : P) : P :=
  ∑ n ∈ Finset.range (p.natDegree + 1), Polynomial.monomial n (a * p.coeff n)

noncomputable def polyZero : P :=
  (0 : P)

noncomputable def polyNeg (p : P) : P :=
  ∑ n ∈ Finset.range (p.natDegree + 1), Polynomial.monomial n (- p.coeff n)

theorem polyAdd_coeff (p q : P) (n : ℕ) :
    (polyAdd p q).coeff n = p.coeff n + q.coeff n := by
  classical
  by_cases h : n < max p.natDegree q.natDegree + 1
  · rw [polyAdd, Polynomial.finsetSum_coeff]
    have hmem : n ∈ Finset.range (max p.natDegree q.natDegree + 1) := by
      simpa [Finset.mem_range] using h
    rw [Finset.sum_eq_single n]
    · simp [Polynomial.coeff_monomial]
    · intro a ha hne
      simp [Polynomial.coeff_monomial, hne]
    · intro hnot
      exact (hnot hmem).elim
  · have hp : p.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hq : q.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [polyAdd, Polynomial.finsetSum_coeff]
    have hsum :
        ∑ x ∈ Finset.range (max p.natDegree q.natDegree + 1),
          (((Polynomial.monomial x) (p.coeff x + q.coeff x)).coeff n) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      by_cases hx' : x = n
      · subst hx'
        simp [Polynomial.coeff_monomial, hp, hq]
      · simp [Polynomial.coeff_monomial, hx']
    simpa [Polynomial.coeff_monomial, hp, hq] using hsum

local instance : Add P := ⟨polyAdd⟩
local instance : Zero P := ⟨polyZero⟩
local instance : Neg P := ⟨polyNeg⟩
local instance : SMul ℝ P := ⟨polySMul⟩

theorem poly_add (p q : P) :
    p + q = polyAdd p q := by
  rfl

theorem zero_poly : 0 = polyZero := by
  rfl

theorem poly_smul (a : ℝ) (p : P) : a•p = polySMul a p :=by
  rfl

theorem neg_poly (p : P) : -p = polyNeg p := by
  rfl

theorem P_is_vector_space : VectorSpaceAxioms ℝ P where
  add_assoc := by
    intro u v w
    repeat rw [poly_add]
    unfold polyAdd
    simp?




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
