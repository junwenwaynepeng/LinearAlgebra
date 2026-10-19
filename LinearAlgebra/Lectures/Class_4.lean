import Mathlib

/-! Axioms characterizing a vector space over a field. -/

structure VectorSpaceAxioms
    (V K : Type*) [Field K] [Add V] [Zero V] [Neg V] [SMul K V] : Prop
where
  -- Vector addition
  add_comm : ∀ u v : V, u + v = v + u
  add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w)
  zero_add : ∀ v : V, 0 + v = v
  neg_add_cancel : ∀ v : V, ∃ u, u + v = 0

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
    use -v
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
    use -v
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
    use -v
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

lemma add_zero_V (V K : Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    v + 0 = v := by
  rw [hV.add_comm]
  exact hV.zero_add v

lemma cancellation_law (V K : Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (u v w : V) :
    u + w = v + w → u = v := by
  intro eq
  obtain ⟨neg_w, hnegw⟩ := hV.neg_add_cancel w
  have hnegw : w + neg_w = 0 := by rw [hV.add_comm]; assumption
  calc
    u = u + 0 := (add_zero_V V K hV u).symm
    _ = u + (w + neg_w) := by rw [hnegw]
    _ = (u + w) + neg_w := (hV.add_assoc u w neg_w).symm
    _ = (v + w) + neg_w := by rw [eq]
    _ = v + (w + neg_w) := hV.add_assoc v w neg_w
    _ = v + 0 := by rw [hnegw]
    _ = v := add_zero_V V K hV v

lemma neg_unique_V (V K : Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    ∃! u : V, u + v = 0  := by
  obtain ⟨neg_v, hnegv⟩ := hV.neg_add_cancel v
  refine ⟨neg_v, hnegv, ?_⟩
  intro w hw
  calc
    w = 0 + w := (hV.zero_add w).symm
    _ = (neg_v + v) + w := by rw [hnegv]
    _ = neg_v + (v + w) := hV.add_assoc neg_v v w
    _ = neg_v + 0 := by rw [hV.add_comm] at hw; rw[hw]
    _ = neg_v := add_zero_V V K hV neg_v

lemma zero_unique_V (V K : Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    ∃! u, u + v = v := by
  use 0
  refine ⟨hV.zero_add v, ?_⟩
  intro zero' hzero'
  have hzu : zero' + v = 0 + v := by
    rw [hzero']
    rw [hV.zero_add v]
  exact cancellation_law V K hV zero' 0 v hzu

lemma self_add_self_imp_eq_zero (V K : Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) (hv : v + v = v) :
    v = 0 := by
  obtain ⟨u, hu⟩ := hV.neg_add_cancel v
  calc
    v = 0 + v := (hV.zero_add v).symm
    _ = u + v + v := by rw [hu]
    _ = u + (v + v) := (hV.add_assoc u v v)
    _ = u + v := by rw [hv]
    _ = 0 := by exact hu

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
    ((-1) : K) • v + v = 0 := by
  calc
    (-1 : K) • v + v = (-1 : K) • v + (1 : K) • v := by rw [hV.one_smul v]
    _ = (-1 + 1 : K) • v := (hV.add_smul (-1:K) (1:K) v).symm
    _ = (0 : K) • v := by norm_num
    _ = 0 := (zero_smul_V V K hV v)

lemma smul_zero_V (V K : Type*)
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (a : K) :
    a • (0 : V) = 0 := by
  have double_a0 : a • (0 : V) + a • (0 : V) = a • (0 : V) := by
    calc
      a • (0 : V) + a • (0 : V) = a • (0 + 0) := (hV.smul_add a (0 : V) (0 : V)).symm
      _ = a • 0 := by rw [(hV.zero_add 0)]
  exact self_add_self_imp_eq_zero V K hV a • (0 : V) double_a0
