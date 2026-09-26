import Mathlib

/-! Axioms characterizing a vector space over a field. -/

structure VectorSpaceAxioms
    (K V : Type*) [Field K] [Add V] [Zero V] [Neg V] [SMul K V] : Prop
where
  -- Vector addition
  add_comm : ∀ u v : V, u + v = v + u
  add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w)
  zero_add : ∀ v : V, 0 + v = v
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
  ∑ n ∈ Finset.range (p.natDegree + 1), Polynomial.monomial n (-1 * p.coeff n)

theorem polySMul_coeff (a : ℝ)(p : P) (n : ℕ) :
    (polySMul a p).coeff n = a * p.coeff n := by
  rw [polySMul, Polynomial.finsetSum_coeff]
  by_cases hn : n < p.natDegree + 1
  · have hmem : n ∈ Finset.range (p.natDegree + 1) := Finset.mem_range.mpr hn
    rw [Finset.sum_eq_single n]
    · simp [Polynomial.coeff_monomial]
    · intro x hx hne
      simp [Polynomial.coeff_monomial, hne]
    · intro hnot
      exact (hnot hmem).elim
  · have hp : p.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Finset.sum_eq_zero]
    · simp [hp]
    · intro x hx
      have hxn : x ≠ n := by
        intro heq
        subst x
        have : n < p.natDegree + 1 := Finset.mem_range.mp hx
        omega
      simp [Polynomial.coeff_monomial, hxn]

theorem polyNeg_coeff (p : P) (n : ℕ) :
    (polyNeg p).coeff n = -p.coeff n := by
  rw [polyNeg, Polynomial.finsetSum_coeff]
  by_cases hn : n < p.natDegree + 1
  · have hmem : n ∈ Finset.range (p.natDegree + 1) := Finset.mem_range.mpr hn
    rw [Finset.sum_eq_single n]
    · simp [Polynomial.coeff_monomial]
    · intro x hx hne
      simp [Polynomial.coeff_monomial, hne]
    · intro hnot
      exact (hnot hmem).elim
  · have hp : p.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Finset.sum_eq_zero]
    · simp [hp]
    · intro x hx
      have hxn : x ≠ n := by
        intro heq
        subst x
        have : n < p.natDegree + 1 := Finset.mem_range.mp hx
        omega
      simp [Polynomial.coeff_monomial, hxn]

theorem polyAdd_coeff (p q : P) (n : ℕ) :
    (polyAdd p q).coeff n = p.coeff n + q.coeff n := by
  by_cases h : n < max p.natDegree q.natDegree + 1
  · rw [polyAdd, Polynomial.finsetSum_coeff]
    have hmem : n ∈ Finset.range (max p.natDegree q.natDegree + 1) := by
      simpa [Finset.mem_range] using h
    rw [Finset.sum_eq_single n]
    · simp
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
        simp [hp, hq]
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
    ext n
    simp only [polyAdd_coeff]
    exact add_assoc (Polynomial.coeff u n) (Polynomial.coeff v n) (Polynomial.coeff w n)

  add_comm := by
    intro u v
    repeat rw [poly_add]
    ext n
    repeat rw [polyAdd_coeff]
    exact add_comm (Polynomial.coeff u n) (Polynomial.coeff v n)

  zero_add := by
    intro v
    rw [poly_add]
    ext n
    rw [polyAdd_coeff]
    simp
    trivial

  neg_add_cancel := by
    intro v
    rw [poly_add]
    ext n
    rw [polyAdd_coeff]
    rw [add_comm]
    rw [neg_poly, polyNeg_coeff]
    simp
    trivial

  smul_add := by
    intro a u v
    repeat rw [poly_smul, poly_add]
    rw [poly_smul]
    ext n
    rw [polyAdd_coeff]
    simp [polySMul_coeff]
    simp [polyAdd_coeff]
    exact mul_add a (Polynomial.coeff u n) (Polynomial.coeff v n)

  add_smul := by
    intro a b v
    repeat rw [poly_smul, poly_add]
    repeat rw [poly_smul]
    ext n
    rw [polyAdd_coeff]
    simp [polySMul_coeff]
    exact add_mul a b (Polynomial.coeff v n)

  mul_smul := by
    intro a b v
    ext n
    repeat rw [poly_smul]
    simp [polySMul_coeff]
    exact mul_assoc a b (Polynomial.coeff v n)

  one_smul := by
    intro v
    ext n
    rw [poly_smul]
    simp [polySMul_coeff]

variable (X : Type*)
abbrev F := X → ℝ

def funAdd (f g : X → ℝ) : X → ℝ :=
  fun x => f x + g x

def funSMul (a : ℝ) (f : X → ℝ) : X → ℝ :=
  fun x => a * f x

def funZero : X → ℝ  :=
  fun _ => 0

def funNeg (f : X → ℝ ) : X → ℝ :=
  fun x => - (f x)

local instance : Add (F X) := ⟨funAdd X⟩
local instance : Zero (F X) := ⟨funZero X⟩
local instance : Neg (F X) := ⟨funNeg X⟩
local instance : SMul ℝ (F X) := ⟨funSMul X⟩

theorem fun_add (p q : X → ℝ) :
    p + q = funAdd X p q := by
  rfl

theorem zero_fun : 0 = funZero := by
  rfl

theorem fun_smul (a : ℝ) (p : X → ℝ) : a • p = funSMul X a p :=by
  rfl

theorem neg_fun (p : X → ℝ) : -p = funNeg X p := by
  rfl

theorem F_is_vector_space : VectorSpaceAxioms ℝ (F X) where
  add_assoc := by
    intro u v w
    ext x
    repeat rw [fun_add]
    unfold funAdd
    exact add_assoc (u x) (v x) (w x)

  add_comm := by
    intro u v
    ext x
    repeat rw [fun_add]
    unfold funAdd
    exact add_comm (u x) (v x)

  zero_add := by
    intro v
    ext x
    rw [fun_add]
    unfold funAdd
    simp
    trivial

  neg_add_cancel := by
    intro v
    ext x
    rw [fun_add]
    unfold funAdd
    rw [neg_fun]
    unfold funNeg
    simp
    trivial

  smul_add := by
    intro a u v
    ext x
    repeat rw [fun_smul, fun_add]
    rw [fun_smul]
    unfold funAdd funSMul
    simp
    exact mul_add a (u x) (v x)

  add_smul := by
    intro a b v
    ext x
    repeat rw [fun_smul, fun_add]
    repeat rw[fun_smul]
    unfold funAdd funSMul
    exact add_mul a b (v x)

  mul_smul := by
    intro a b v
    ext x
    repeat rw [fun_smul]
    exact mul_assoc a b (v x)

  one_smul := by
    intro v
    ext x
    rw [fun_smul]
    exact one_mul (v x)

variable {K V : Type*}
variable [Field K] [Add V] [Zero V] [Neg V] [SMul K V]

def IsVectorSubspace
    (K : Type*) {V : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (W : Set V) : Prop :=
  ∃ (addW : Add (↥W))
    (zeroW : Zero (↥W))
    (negW : Neg (↥W))
    (smulW : SMul K (↥W)),

    @VectorSpaceAxioms K (↥W) _
      addW zeroW negW smulW ∧

    (∀ u v : ↥W,
      ((addW.add u v : ↥W) : V) =
        (u : V) + (v : V)) ∧

    (((zeroW.zero : ↥W) : V) = (0 : V)) ∧

    (∀ u : ↥W,
      ((negW.neg u : ↥W) : V) = -(u : V)) ∧

    (∀ (a : K) (u : ↥W),
      ((smulW.smul a u : ↥W) : V) =
        a • (u : V))

theorem subspace_criterion
    {K V : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms K V)
    (W : Set V)
    (zero_mem : (0 : V) ∈ W)
    (add_mem :
      ∀ u v : V, u ∈ W → v ∈ W → u + v ∈ W)
    (smul_mem :
      ∀ (a : K) (v : V), v ∈ W → a • v ∈ W) :
    IsVectorSubspace K W := by
  letI : Add (↥W) :=
    ⟨fun u v =>
      ⟨(u : V) + (v : V),
        add_mem (u : V) (v : V) u.property v.property⟩⟩

  letI : Zero (↥W) :=
    ⟨⟨0, zero_mem⟩⟩

  letI : SMul K (↥W) :=
    ⟨fun a v =>
      ⟨a • (v : V),
        smul_mem a (v : V) v.property⟩⟩

  letI : Neg (↥W) :=
    ⟨fun v =>
      ⟨-(v : V), by
        sorry⟩⟩

  have W_is_vector_space : VectorSpaceAxioms K (↥W) where
      add_assoc := by
        intro u v w
