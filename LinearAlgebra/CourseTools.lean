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

/-- Adding zero coefficients on a larger finite set preserves the vector sum. -/
lemma sum_extendCoefficients_V {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    [DecidableEq V]
    (hV : VectorSpaceAxioms V K)
    (S T : Finset V) (a : S → K) (hST : S ⊆ T) :
    (∑ v : T, extendCoefficients S T a v • (v : V)) =
      ∑ v : S, a v • (v : V) := by
  let a₀ : V → K := fun v => if h : v ∈ S then a ⟨v, h⟩ else 0
  change (∑ v : T, a₀ (v : V) • (v : V)) = _
  calc
    (∑ v : T, a₀ (v : V) • (v : V)) =
        ∑ v ∈ T, a₀ v • v := Finset.sum_coe_sort T (fun v : V => a₀ v • v)
    _ = ∑ v ∈ S, a₀ v • v := by
      symm
      apply Finset.sum_subset hST
      intro v _ hv
      simp only [a₀, dite_eq_right hv, zero_smul_V hV]
    _ = ∑ v : S, a₀ (v : V) • (v : V) :=
      (Finset.sum_coe_sort S (fun v : V => a₀ v • v)).symm
    _ = ∑ v : S, a v • (v : V) := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [a₀, dite_eq_left v.property]

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
    (hV : VectorSpaceAxioms V K) (X : Set V) : Set V :=
  {w | ∃ (S : Finset V) (a : S → K), (∀ v ∈ S, v ∈ X) ∧ w = LinearCombination hV S a}


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
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (X : Set V) :
    IsVectorSubspace hV (Span hV X) := by
  classical
  apply subspace_test hV (Span hV X)
  · refine ⟨∅, (fun _ => 0), ?_, ?_⟩
    · simp
    · simp [LinearCombination]
  · intro u v hu hv
    obtain ⟨S, a, hSX, ha⟩ := hu
    obtain ⟨T, b, hTX, hb⟩ := hv
    let U : Finset V := S ∪ T
    let a' : U → K := extendCoefficients S U a
    let b' : U → K := extendCoefficients T U b
    have ha' : LinearCombination hV U a' = LinearCombination hV S a :=
      sum_extendCoefficients_V hV S U a Finset.subset_union_left
    have hb' : LinearCombination hV U b' = LinearCombination hV T b :=
      sum_extendCoefficients_V hV T U b Finset.subset_union_right
    refine ⟨U, (fun s => a' s + b' s), ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_union.mp hw with hS | hT
      · exact hSX w hS
      · exact hTX w hT
    · rw [ha, hb, ← ha', ← hb']
      simp only [LinearCombination, hV.add_smul, Finset.sum_add_distrib]
  · intro c v hv
    obtain ⟨S, a, hSX, ha⟩ := hv
    refine ⟨S, (fun s => c * a s), hSX, ?_⟩
    rw [ha]
    unfold LinearCombination
    rw [smul_sum_V hV]
    simp only [hV.mul_smul]
