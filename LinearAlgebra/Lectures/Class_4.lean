import Mathlib

/-! Axioms characterizing a vector space over a field. -/

structure VectorSpaceAxioms
    (V K : Type*) [Field K] [Add V] [Zero V] [Neg V] [SMul K V] : Prop
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

theorem polySMul_coeff (a : ℝ) (p : P) (n : ℕ) :
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

theorem P_is_vector_space : VectorSpaceAxioms P ℝ where
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

def funNeg (f : X → ℝ) : X → ℝ :=
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

theorem F_is_vector_space : VectorSpaceAxioms (F X) ℝ where
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

lemma add_zero_V (V K: Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    v + 0 = v := by
  rw [hV.add_comm]
  exact hV.zero_add v

lemma add_neg_cancel_V (V K : Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    v + -v = 0 := by
    rw [hV.add_comm]
    exact hV.neg_add_cancel v

lemma self_add_self_imp_eq_zero (V K : Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) (hv : v + v = v) :
    v = 0 := by
  calc
    v = 0 + v := (hV.zero_add v).symm
    _ = -v + v + v := by rw [hV.neg_add_cancel v]
    _ = -v + (v + v) := (hV.add_assoc (-v) v v)
    _ = -v + v := by rw [hv]
    _ = 0 := (hV.neg_add_cancel v)

lemma neg_unique_V (V K : Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v w : V) :
    v + w = 0 → w = -v := by
  intro v_add_w_zero
  calc
    w = 0 + w := (hV.zero_add w).symm
    _ = (-v + v) + w := by rw [hV.neg_add_cancel v]
    _ = -v + (v + w) := hV.add_assoc (-v) v w
    _ = -v + 0 := by rw [v_add_w_zero]
    _ = -v := add_zero_V V K hV (-v)

lemma zero_smul_V (V K : Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    (0 : K) • v = 0 := by
  have zero_add_zero : (0 : K) • v + (0 : K) • v = (0 : K) • v := by
    calc
      (0 : K) • v + (0 : K) • v = (0 + 0 : K) • v := (hV.add_smul (0:K) (0:K) v).symm
      _ = (0: K) • v := by norm_num
  exact self_add_self_imp_eq_zero V K hV ((0 : K) • v) zero_add_zero

lemma neg_one_smul_V (K V : Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    ((-1) : K) • v = -v := by
  have hneg : v + (-1 : K) • v = 0 := by
    calc
      v + (-1 : K) • v = (1 : K) • v + (-1 : K) • v := by rw [hV.one_smul v]
      _ = (1 + -1 : K) • v := (hV.add_smul (1:K) (-1:K) v).symm
      _ = (0 : K) • v := by norm_num
      _ = 0 := (zero_smul_V V K hV v)
  apply neg_unique_V V K hV v ((-1 : K) • v)
  exact hneg

variable {V K : Type*}
variable [Field K] [Add V] [Zero V] [Neg V] [SMul K V]

def IsVectorSubspace
    (V K : Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (W : Set V) : Prop :=
  ∃ (addW : Add (↥W))
    (zeroW : Zero (↥W))
    (negW : Neg (↥W))
    (smulW : SMul K (↥W)),
    @VectorSpaceAxioms (↥W) K _
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
    IsVectorSubspace V K W:= by

  let addW : Add (↥W) :=
    ⟨fun u v =>
      ⟨(u : V) + (v : V),
        add_close (u : V) (v : V) u.property v.property⟩⟩

  let zeroW : Zero (↥W) :=
    ⟨⟨0, has_zero⟩⟩

  let smulKW : SMul K (↥W) :=
    ⟨fun a v =>
      ⟨a • (v : V),
        smul_close a (v : V) v.property⟩⟩

  let negW : Neg (↥W) :=
    ⟨fun v =>
      ⟨(-v : V), by
        rw [←neg_one_smul_V K V hV (v : V)]
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
    IsVectorSubspace (ℝ → ℝ) ℝ ODESolutions := by
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
    IsVectorSubspace Vec3 ℝ homogeneousSolutions := by
  exact
    subspace_test
      V_is_vector_space
      homogeneousSolutions
      homogeneous_zero_mem
      homogeneous_add_mem
      homogeneous_smul_mem

theorem intersection_is_subspace
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (W₁ W₂ : Set V) (hW₁ : IsVectorSubspace V K W₁)(hW₂: IsVectorSubspace V K W₂) :
    (IsVectorSubspace V K (W₁∩W₂)) := by
  rcases hW₁ with ⟨addW₁, zeroW₁, negW₁, smulW₁, hax₁,
      hadd₁, hzero₁, hneg₁, hsmul₁⟩
  rcases hW₂ with ⟨addW₂, zeroW₂, negW₂, smulW₂, hax₂,
      hadd₂, hzero₂, hneg₂, hsmul₂⟩
  have hzero : (0 : V) ∈ W₁∩W₂ := by
    constructor
    · rw [←hzero₁]
      exact Subtype.property (zeroW₁.zero : (↥W₁))
    · rw [←hzero₂]
      exact Subtype.property (zeroW₂.zero : (↥W₂))
  have h_add_closed (u v : V) (hu : u ∈ W₁∩W₂) (hv : v ∈ W₁∩W₂) : u + v ∈ W₁∩W₂ := by
    constructor
    · let uW₁ : ↥W₁ := ⟨u, hu.1⟩
      let vW₁ : ↥W₁ := ⟨v, hv.1⟩
      have hmem : ((addW₁.add uW₁ vW₁ : ↥W₁) : V) ∈ W₁ :=
        Subtype.property (addW₁.add uW₁ vW₁)
      rwa [hadd₁ uW₁ vW₁] at hmem
      --assumption
    · let uW₂ : ↥W₂ := ⟨u, hu.2⟩
      let vW₂ : ↥W₂ := ⟨v, hv.2⟩
      have hmem : ((addW₂.add uW₂ vW₂ : ↥W₂) : V) ∈ W₂ :=
        Subtype.property (addW₂.add uW₂ vW₂)
      rwa [hadd₂ uW₂ vW₂] at hmem
      --assumption
  have h_smul_closed (a : K) (u : V) (hu : u ∈ W₁∩W₂) : a • u ∈ W₁∩W₂ := by
    constructor
    · let uW₁ : ↥W₁ := ⟨u, hu.1⟩
      have hmem : ((smulW₁.smul a uW₁ : ↥W₁) : V) ∈ W₁ :=
        Subtype.property (smulW₁.smul a uW₁)
      rwa [hsmul₁ a uW₁] at hmem
      --assumption
    · let uW₂ : ↥W₂ := ⟨u, hu.2⟩
      have hmem : ((smulW₂.smul a uW₂ : ↥W₂) : V) ∈ W₂ :=
        Subtype.property (smulW₂.smul a uW₂)
      rwa [hsmul₂ a uW₂] at hmem
      --assumption
  exact
    subspace_test hV (W₁∩W₂) hzero h_add_closed h_smul_closed

def listIntersection {V : Type*} :
    List (Set V) → Set V
  | [] => Set.univ
  | W :: Ws => W ∩ listIntersection Ws

theorem univ_is_subspace
    {K V : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) :
    IsVectorSubspace V K (Set.univ : Set V) := by
  apply subspace_test hV Set.univ
  · simp
  · intro u v hu hv
    simp
  · intro a v hv
    simp

lemma smul_zero_from_axioms
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (a : K) :
    a • (0 : V) = 0 := by

  let x : V := a • (0 : V)

  have hx : x + x = x := by
    dsimp [x]
    calc
      a • (0 : V) + a • (0 : V)
          = a • ((0 : V) + 0) :=
            (hV.smul_add a 0 0).symm
      _ = a • (0 : V) := by
            rw [hV.zero_add]

  change x = 0

  calc
    x = 0 + x := (hV.zero_add x).symm
    _ = ((-x) + x) + x := by
          rw [hV.neg_add_cancel x]
    _ = (-x) + (x + x) :=
          hV.add_assoc (-x) x x
    _ = (-x) + x := by rw [hx]
    _ = 0 := hV.neg_add_cancel x

theorem zeroSubspace_is_subspace
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) :
    IsVectorSubspace V K ({0} : Set V) := by

  apply subspace_test (V := V) (K := K) hV
    ({0} : Set V)

  · simp

  · intro u v hu hv
    simp only [Set.mem_singleton_iff] at hu hv ⊢
    subst u
    subst v
    exact hV.zero_add 0

  · intro a v hv
    simp only [Set.mem_singleton_iff] at hv ⊢
    subst v
    exact smul_zero_from_axioms hV a

theorem listIntersection_is_subspace
    {K V : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (Ws : List (Set V)) :
    (∀ W ∈ Ws, IsVectorSubspace V K W) →
      IsVectorSubspace V K (listIntersection Ws) := by

  induction Ws with
  | nil =>
      intro hWs
      exact univ_is_subspace hV

  | cons W Ws ih =>
      intro hWs

      have hW : IsVectorSubspace V K W := by
        apply hWs W
        simp

      have hTail :
          IsVectorSubspace V K (listIntersection Ws) := by
        apply ih
        intro U hU
        apply hWs U
        simp [hU]

      exact
        intersection_is_subspace
          hV
          W
          (listIntersection Ws)
          hW
          hTail
lemma isVectorSubspace_zero_mem
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    {W : Set V}
    (hW : IsVectorSubspace V K W) :
    (0 : V) ∈ W := by

  rcases hW with
    ⟨addW, zeroW, negW, smulW,
      hax, hadd, hzero, hneg, hsmul⟩

  rw [← hzero]

  exact Subtype.property (zeroW.zero : ↥W)
lemma isVectorSubspace_add_mem
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    {W : Set V}
    (hW : IsVectorSubspace V K W)
    {u v : V}
    (hu : u ∈ W)
    (hv : v ∈ W) :
    u + v ∈ W := by

  rcases hW with
    ⟨addW, zeroW, negW, smulW,
      hax, hadd, hzero, hneg, hsmul⟩

  let uW : ↥W := ⟨u, hu⟩
  let vW : ↥W := ⟨v, hv⟩

  have hmem :
      ((addW.add uW vW : ↥W) : V) ∈ W :=
    Subtype.property (addW.add uW vW)

  rw [hadd uW vW] at hmem

  exact hmem

lemma isVectorSubspace_smul_mem
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    {W : Set V}
    (hW : IsVectorSubspace V K W)
    (a : K)
    {v : V}
    (hv : v ∈ W) :
    a • v ∈ W := by

  rcases hW with
    ⟨addW, zeroW, negW, smulW,
      hax, hadd, hzero, hneg, hsmul⟩

  let vW : ↥W := ⟨v, hv⟩

  have hmem :
      ((smulW.smul a vW : ↥W) : V) ∈ W :=
    Subtype.property (smulW.smul a vW)

  rw [hsmul a vW] at hmem

  exact hmem

def subspaceSum
    {V : Type*} [Add V]
    (W₁ W₂ : Set V) : Set V :=
  {x | ∃ u ∈ W₁, ∃ v ∈ W₂, x = u + v}

theorem subspaceSum_is_subspace
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (W₁ W₂ : Set V)
    (hW₁ : IsVectorSubspace V K W₁)
    (hW₂ : IsVectorSubspace V K W₂) :
    IsVectorSubspace V K (subspaceSum W₁ W₂) := by

  apply subspace_test (V := V) (K := K) hV
    (subspaceSum W₁ W₂)

  · -- 0 = 0 + 0
    change ∃ u ∈ W₁, ∃ v ∈ W₂, (0 : V) = u + v

    refine ⟨0, isVectorSubspace_zero_mem hW₁,
      0, isVectorSubspace_zero_mem hW₂, ?_⟩

    exact (hV.zero_add 0).symm

  · -- Closure under addition
    intro x y hx hy

    change (∃ u ∈ W₁, ∃ v ∈ W₂, x = u + v) at hx
    change (∃ u ∈ W₁, ∃ v ∈ W₂, y = u + v) at hy

    rcases hx with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    rcases hy with ⟨v₁, hv₁, v₂, hv₂, rfl⟩

    change ∃ p ∈ W₁, ∃ q ∈ W₂,
      (u₁ + u₂) + (v₁ + v₂) = p + q

    refine ⟨u₁ + v₁,
      isVectorSubspace_add_mem hW₁ hu₁ hv₁,
      u₂ + v₂,
      isVectorSubspace_add_mem hW₂ hu₂ hv₂,
      ?_⟩

    calc
      (u₁ + u₂) + (v₁ + v₂)
          = u₁ + (u₂ + (v₁ + v₂)) :=
            hV.add_assoc u₁ u₂ (v₁ + v₂)
      _ = u₁ + ((u₂ + v₁) + v₂) := by
            rw [← hV.add_assoc u₂ v₁ v₂]
      _ = u₁ + ((v₁ + u₂) + v₂) := by
            rw [hV.add_comm u₂ v₁]
      _ = u₁ + (v₁ + (u₂ + v₂)) := by
            rw [hV.add_assoc v₁ u₂ v₂]
      _ = (u₁ + v₁) + (u₂ + v₂) :=
            (hV.add_assoc u₁ v₁ (u₂ + v₂)).symm

  · -- Closure under scalar multiplication
    intro a x hx

    change (∃ u ∈ W₁, ∃ v ∈ W₂, x = u + v) at hx
    rcases hx with ⟨u, hu, v, hv, rfl⟩

    change ∃ p ∈ W₁, ∃ q ∈ W₂,
      a • (u + v) = p + q

    refine ⟨a • u,
      isVectorSubspace_smul_mem hW₁ a hu,
      a • v,
      isVectorSubspace_smul_mem hW₂ a hv,
      ?_⟩

    exact hV.smul_add a u v

def listSubspaceSum
    {V : Type*} [Add V] [Zero V] :
    List (Set V) → Set V
  | [] => {0}
  | W :: Ws => subspaceSum W (listSubspaceSum Ws)

theorem listSubspaceSum_is_subspace
    {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (Ws : List (Set V)) :
    (∀ W ∈ Ws, IsVectorSubspace V K W) →
      IsVectorSubspace V K (listSubspaceSum Ws) := by

  induction Ws with
  | nil =>
      intro hWs
      simpa [listSubspaceSum] using
        (zeroSubspace_is_subspace (V := V) (K := K) hV)

  | cons W Ws ih =>
      intro hWs

      have hW : IsVectorSubspace V K W := by
        exact hWs W (by simp)

      have hTail :
          IsVectorSubspace V K (listSubspaceSum Ws) := by
        apply ih
        intro U hU
        exact hWs U (by simp [hU])

      simpa [listSubspaceSum] using
        (subspaceSum_is_subspace
          (V := V) (K := K)
          hV W (listSubspaceSum Ws) hW hTail)
