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
