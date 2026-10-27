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
  neg_add_cancel : ∀ v : V, ∃ u, u + v = 0

  -- Scalar multiplication
  one_smul : ∀ v : V, (1 : K) • v = v
  mul_smul : ∀ (a b : K) (v : V),
    (a * b) • v = a • (b • v)
  smul_add : ∀ (a : K) (u v : V),
    a • (u + v) = a • u + a • v
  add_smul : ∀ (a b : K) (v : V),
    (a + b) • v = a • v + b • v

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
  exact self_add_self_imp_eq_zero V K hV (a • (0 : V)) double_a0
