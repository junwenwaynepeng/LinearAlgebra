/-
Copyright (c) 2026 Wayne Peng.
Authors: Wayne Peng
-/

import Mathlib

/-!

Simple course tactics for elementary row operations.

Lean uses 0-based row numbering:
0 = R₁
1 = R₂
2 = R₃
-/

macro "row_add " A:ident " => " B:ident
    ", " i:term ", " j:term ", " c:term : tactic =>
  `(tactic|
    convert Matrix.rowEquivalent_transvection
      $A $i $j (by decide) $c using 1 <;>
    unfold $A $B <;>
    funext row col <;>
    fin_cases row <;>
    fin_cases col <;>
    simp <;>
    norm_num
  )

macro "row_scale " A:ident " => " B:ident
    ", " i:term ", " c:term : tactic =>
  `(tactic|
    convert Matrix.rowEquivalent_rowScale
      $A $i (Units.mk0 $c (by norm_num)) using 1 <;>
    unfold $A $B <;>
    rw [Matrix.rowScale_mul] <;>
    funext row col <;>
    fin_cases row <;>
    fin_cases col <;>
    simp <;>
    norm_num
  )

macro "row_swap " A:ident " => " B:ident
    ", " i:term ", " j:term : tactic =>
  `(tactic|
    convert Matrix.rowEquivalent_swap
      $A $i $j using 1 <;>
    unfold $A $B <;>
    funext row col <;>
    fin_cases row <;> fin_cases col <;>
    simp [Matrix.swap_mul_of_ne]<;>
    norm_num
  )

instance rowEquivalentTrans
    {R m n : Type*}
    [CommRing R]
    [Fintype m]
    [DecidableEq m] :
    Trans
      (Matrix.RowEquivalent : Matrix m n R → Matrix m n R → Prop)
      (Matrix.RowEquivalent : Matrix m n R → Matrix m n R → Prop)
      (Matrix.RowEquivalent : Matrix m n R → Matrix m n R → Prop) where
  trans := Matrix.RowEquivalent.trans

def showMatrix {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℚ) :=
  List.ofFn (fun i => List.ofFn (fun j => A i j))

def rowSwap {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (i j : Fin m) :=
  (A.updateRow i (A j)).updateRow j (A i)

def rowScale' {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (c : ℚ) :=
  A.updateRow i (fun j => c * A i j)

def rowAdd {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (i j : Fin m) (c : ℚ) :=
  A.updateRow i (fun k => A i k + c * A j k)

def IsInverse
    {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A * B = 1 ∧ B * A = 1

def IsInvertible
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ B, IsInverse A B


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

lemma add_zero_V {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    v + 0 = v := by
  rw [hV.add_comm]
  exact hV.zero_add v

lemma cancellation_law {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K)
    (u v w : V) :
    u + w = v + w → u = v := by
  intro eq
  have hnegw : w + -w = 0 := by
    rw [hV.add_comm]
    exact hV.neg_add_cancel w
  calc
    u = u + 0 := (add_zero_V hV u).symm
    _ = u + (w + -w) := by rw [hnegw]
    _ = (u + w) + -w := (hV.add_assoc u w (-w)).symm
    _ = (v + w) + -w := by rw [eq]
    _ = v + (w + -w) := hV.add_assoc v w (-w)
    _ = v + 0 := by rw [hnegw]
    _ = v := add_zero_V hV v

lemma neg_unique_V {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    ∃! u : V, u + v = 0  := by
  refine ⟨-v, hV.neg_add_cancel v, ?_⟩
  intro w hw
  calc
    w = 0 + w := (hV.zero_add w).symm
    _ = (-v + v) + w := by rw [hV.neg_add_cancel v]
    _ = -v + (v + w) := hV.add_assoc (-v) v w
    _ = -v + 0 := by rw [hV.add_comm] at hw; rw [hw]
    _ = -v := add_zero_V hV (-v)

lemma zero_unique_V {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    ∃! u, u + v = v := by
  use 0
  refine ⟨hV.zero_add v, ?_⟩
  intro zero' hzero'
  have hzu : zero' + v = 0 + v := by
    rw [hzero']
    rw [hV.zero_add v]
  exact cancellation_law hV zero' 0 v hzu

lemma self_add_self_imp_eq_zero {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) (hv : v + v = v) :
    v = 0 := by
  calc
    v = 0 + v := (hV.zero_add v).symm
    _ = (-v + v) + v := by rw [← hV.neg_add_cancel v]
    _ = -v + (v + v) := hV.add_assoc (-v) v v
    _ = -v + v := by rw [hv]
    _ = 0 := hV.neg_add_cancel v

lemma zero_smul_V {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    (0 : K) • v = 0 := by
  have zero_add_zero : (0 : K) • v + (0 : K) • v = (0 : K) • v := by
    calc
      (0 : K) • v + (0 : K) • v = (0 + 0 : K) • v := (hV.add_smul (0:K) (0:K) v).symm
      _ = (0: K) • v := by norm_num
  exact self_add_self_imp_eq_zero hV ((0 : K) • v) zero_add_zero

lemma neg_one_smul_add_V {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    ((-1) : K) • v + v = 0 := by
  calc
    (-1 : K) • v + v = (-1 : K) • v + (1 : K) • v := by rw [hV.one_smul v]
    _ = (-1 + 1 : K) • v := (hV.add_smul (-1:K) (1:K) v).symm
    _ = (0 : K) • v := by norm_num
    _ = 0 := (zero_smul_V hV v)

lemma neg_one_smul_V {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (v : V) :
    (-1 : K) • v = -v := by
  have h : (-1 : K) • v + v = -v + v :=by
    rw [hV.neg_add_cancel]
    exact neg_one_smul_add_V hV v
  exact cancellation_law hV ((-1 : K) • v) (-v) v h

lemma smul_zero_V {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (a : K) :
    a • (0 : V) = 0 := by
  have double_a0 : a • (0 : V) + a • (0 : V) = a • (0 : V) := by
    calc
      a • (0 : V) + a • (0 : V) = a • (0 + 0) := (hV.smul_add a (0 : V) (0 : V)).symm
      _ = a • 0 := by rw [(hV.zero_add 0)]
  exact self_add_self_imp_eq_zero hV (a • (0 : V)) double_a0

open scoped BigOperators

/-- Scalar multiplication distributes over a finite sum. -/
lemma smul_sum_V {V K ι : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (a : K)
    (s : Finset ι) (v : ι → V) :
    a • (∑ i ∈ s, v i) = ∑ i ∈ s, a • v i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact smul_zero_V hV a
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hV.smul_add, ih]

/-- Extend coefficients from one finite set to another, using zero outside the source. -/
def extendCoefficients {V K : Type*} [Zero K] [DecidableEq V]
    (S T : Finset V) (a : S → K) : T → K :=
  fun v => if h : (v : V) ∈ S then a ⟨v, h⟩ else 0

/-- Extending coefficients by zero to a larger finite set preserves nonzeroness. -/
lemma extendCoefficients_ne_zero {V K : Type*} [Zero K] [DecidableEq V]
    {S T : Finset V} {a : S → K} (hST : S ⊆ T) (ha : a ≠ 0) :
    extendCoefficients S T a ≠ 0 := by
  intro hzero
  apply ha
  funext v
  simpa [extendCoefficients, v.property] using congrFun hzero ⟨v, hST v.property⟩

/-- Extending coefficients by zero preserves a sum of scalar multiples of any vector family. -/
lemma sum_extendCoefficients_smul {V K ι : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V] [DecidableEq ι]
    (hV : VectorSpaceAxioms V K)
    (S T : Finset ι) (a : S → K) (hST : S ⊆ T) (f : ι → V) :
    (∑ i : T, extendCoefficients S T a i • f i) =
      ∑ i : S, a i • f i := by
  let a₀ : ι → K := fun i => if h : i ∈ S then a ⟨i, h⟩ else 0
  change (∑ i : T, a₀ i • f i) = _
  calc
    (∑ i : T, a₀ i • f i) = ∑ i ∈ T, a₀ i • f i :=
      Finset.sum_coe_sort T (fun i => a₀ i • f i)
    _ = ∑ i ∈ S, a₀ i • f i := by
      symm
      apply Finset.sum_subset hST
      intro i _ hi
      simp only [a₀, dite_eq_right hi, zero_smul_V hV]
    _ = ∑ i : S, a₀ i • f i :=
      (Finset.sum_coe_sort S (fun i => a₀ i • f i)).symm
    _ = ∑ i : S, a i • f i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [a₀, dite_eq_left i.property]

/-- Adding zero coefficients on a larger finite set preserves the vector sum. -/
lemma sum_extendCoefficients_V {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    [DecidableEq V]
    (hV : VectorSpaceAxioms V K)
    (S T : Finset V) (a : S → K) (hST : S ⊆ T) :
    (∑ v : T, extendCoefficients S T a v • (v : V)) =
      ∑ v : S, a v • (v : V) := by
  exact sum_extendCoefficients_smul hV S T a hST id


def LinearCombination
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (_ : VectorSpaceAxioms V K)
    (S : Finset V)
    (a : S → K) : V :=
  ∑ v : S, a v • v

/-- Attaching membership information to every index does not change a sum. -/
lemma sum_attach_coe {ι M : Type*} [AddCommMonoid M]
    (S : Finset ι) (f : S → M) :
    (∑ i : S.attach, f (i : S)) = ∑ i : S, f i := by
  calc
    (∑ i : S.attach, f (i : S)) = ∑ i ∈ S.attach, f i :=
      Finset.sum_coe_sort S.attach f
    _ = ∑ i : S, f i := (Finset.sum_coe_sort_eq_attach S f).symm

/-- Split off the coefficient of a newly inserted vector. -/
lemma linearCombination_insert_V {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V] [DecidableEq V]
    (hV : VectorSpaceAxioms V K)
    (S : Finset V) (v : V) (hv : v ∉ S) (a : ↥(insert v S) → K) :
    LinearCombination hV (insert v S) a =
      a ⟨v, Finset.mem_insert_self v S⟩ • v +
        LinearCombination hV S
          (fun u => a ⟨(u : V), Finset.mem_insert_of_mem u.property⟩) := by
  let f : V → V := fun u =>
    if h : u ∈ insert v S then a ⟨u, h⟩ • u else 0
  calc
    LinearCombination hV (insert v S) a = ∑ u : ↥(insert v S), f u := by
      apply Finset.sum_congr rfl
      intro u _
      simp only [f, dite_eq_left u.property]
    _ = ∑ u ∈ insert v S, f u := Finset.sum_coe_sort (insert v S) f
    _ = f v + ∑ u ∈ S, f u := Finset.sum_insert hv
    _ = a ⟨v, Finset.mem_insert_self v S⟩ • v +
        LinearCombination hV S
          (fun u => a ⟨(u : V), Finset.mem_insert_of_mem u.property⟩) := by
      apply congrArg₂ (· + ·)
      · simp only [f, dite_eq_left (Finset.mem_insert_self v S)]
      · calc
          (∑ u ∈ S, f u) = ∑ u : S, f u := (Finset.sum_coe_sort S f).symm
          _ = LinearCombination hV S
              (fun u => a ⟨(u : V), Finset.mem_insert_of_mem u.property⟩) := by
            apply Finset.sum_congr rfl
            intro u _
            simp only [f, dite_eq_left (Finset.mem_insert_of_mem u.property)]

/-- Solve a vector equation for the vector with a nonzero scalar coefficient. -/
lemma eq_neg_inv_smul_of_smul_add_eq_zero_V {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (c : K) (hc : c ≠ 0) (v w : V)
    (h : c • v + w = 0) : v = (-(c⁻¹)) • w := by
  have hcoeff : -(c⁻¹) * c = (-1 : K) := by
    rw [neg_mul, inv_mul_cancel₀ hc]
  have hscaled : -v + (-(c⁻¹)) • w = 0 := by
    have h' := congrArg (fun z : V => (-(c⁻¹)) • z) h
    simpa only [hV.smul_add, ← hV.mul_smul, hcoeff,
      neg_one_smul_V hV, smul_zero_V hV] using h'
  apply cancellation_law hV v ((-(c⁻¹)) • w) (-v)
  calc
    v + -v = 0 := by
      rw [hV.add_comm]
      exact hV.neg_add_cancel v
    _ = (-(c⁻¹)) • w + -v := by
      rw [hV.add_comm]
      exact hscaled.symm

/-- Adding zero coefficients does not change a linear combination. -/
@[simp] lemma linearCombination_extendCoefficients {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V] [DecidableEq V]
    (hV : VectorSpaceAxioms V K)
    (S T : Finset V) (a : S → K) (hST : S ⊆ T) :
    LinearCombination hV T (extendCoefficients S T a) = LinearCombination hV S a :=
  sum_extendCoefficients_V hV S T a hST

/-- Scaling every coefficient scales the resulting vector. -/
@[simp] lemma linearCombination_smul_V {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (S : Finset V) (a : S → K) (c : K) :
    LinearCombination hV S (fun u => c * a u) = c • LinearCombination hV S a := by
  unfold LinearCombination
  rw [smul_sum_V hV]
  simp only [hV.mul_smul]

/-- Adding coefficient functions adds the resulting vectors. -/
@[simp] lemma linearCombination_add_V {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (S : Finset V) (a b : S → K) :
    LinearCombination hV S (fun u => a u + b u) =
      LinearCombination hV S a + LinearCombination hV S b := by
  unfold LinearCombination
  simp only [hV.add_smul, Finset.sum_add_distrib]

/-- If two vectors add to zero, either is the negative of the other. -/
lemma eq_neg_of_add_eq_zero_V {V K : Type*}
    [Field K] [Add V] [Zero V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) {u v : V} (h : u + v = 0) : u = -v :=
  cancellation_law hV u (-v) v (h.trans (hV.neg_add_cancel v).symm)

/-- A combination over `S ∪ {v}` splits into the coefficient of `v` and coefficients on `S`.
The full coefficient function vanishes exactly when both pieces vanish. -/
lemma linearCombination_union_singleton {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V] [DecidableEq V]
    (hV : VectorSpaceAxioms V K) (S : Finset V) (v : V) (hv : v ∉ S)
    (a : ↥(S ∪ {v}) → K) :
    ∃ (c : K) (b : S → K),
      LinearCombination hV (S ∪ {v}) a = c • v + LinearCombination hV S b ∧
      (a = 0 ↔ c = 0 ∧ b = 0) := by
  revert a
  rw [Finset.union_singleton]
  intro a
  let v' : ↥(insert v S) := ⟨v, Finset.mem_insert_self v S⟩
  let b : S → K := fun u => a ⟨(u : V), Finset.mem_insert_of_mem u.property⟩
  refine ⟨a v', b, linearCombination_insert_V hV S v hv a, ?_⟩
  constructor
  · intro ha
    constructor
    · exact congrFun ha v'
    · funext u
      exact congrFun ha ⟨(u : V), Finset.mem_insert_of_mem u.property⟩
  · rintro ⟨hc, hb⟩
    funext u
    rcases u with ⟨u, hu⟩
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hc
    · exact congrFun hb ⟨u, hu⟩

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


/-- A linear combination of a finite set belongs to the span of that set. -/
lemma IsLinearCombination.mem_span {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    {hV : VectorSpaceAxioms V K} {S : Finset V} {v : V}
    (h : IsLinearCombination hV S v) : v ∈ Span hV (S : Set V) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨S.attach, (fun u => a (u : S)), ?_⟩
  calc
    v = ∑ u : S, a u • (u : V) := ha
    _ = ∑ u : S.attach, a (u : S) • (u : V) :=
      (sum_attach_coe S (fun u : S => a u • (u : V))).symm

/-- A vector in the span of a finite set can use that whole set as its coefficient domain. -/
lemma IsLinearCombination.of_mem_span {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) {S : Finset V} {v : V}
    (h : v ∈ Span hV (S : Set V)) : IsLinearCombination hV S v := by
  classical
  obtain ⟨T, b, hb⟩ := h
  let a : S → K := fun s => if hs : s ∈ T then b ⟨s, hs⟩ else 0
  have hTS : T ⊆ S.attach := by
    intro s _
    exact Finset.mem_attach S s
  refine ⟨a, ?_⟩
  calc
    v = ∑ t : T, b t • (t : V) := hb
    _ = ∑ s : S.attach, extendCoefficients T S.attach b s • (s : V) :=
      (sum_extendCoefficients_smul hV T S.attach b hTS (fun s : S => (s : V))).symm
    _ = LinearCombination hV S a :=
      sum_attach_coe S (fun s : S => a s • (s : V))

/-- Every generating vector belongs to its span. -/
lemma mem_span_of_mem {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) {X : Set V} {v : V} (hv : v ∈ X) :
    v ∈ Span hV X := by
  refine ⟨{⟨v, hv⟩}, (fun _ => 1), ?_⟩
  simp only [hV.one_smul]
  simp


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
