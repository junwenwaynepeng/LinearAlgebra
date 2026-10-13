import Mathlib
/-!-/
open Matrix
open scoped BigOperators
open scoped Matrix

example (x y : ℝ) (h : x = y) :
    x^2 = y^2 := by
  exact congrArg (fun t => t^2) h

example (f g : ℝ → ℝ)
    (h : ∀ x, f x = g x) :
    f = g := by
  funext x
  exact h x

/- **Lemma 2.1** - Assume that A and B are matrices of sizes m×n and p×q.
If AB = BA, then m=n=p=q; that is, A and B are square matrices of the same size.

*proof.* By assumption, A is an m×n matrix, and B is a p×q matrix.
Since AB and BA are well-defined, n=p and q=m.
Then AB is an m×q matrix and BA is a p×n matrix.
Finally, the assumption AB = BA implies m×q = p×n.
Thus, m=p and n=q. Therefore, A and B are square matrices of the same size.
-/

lemma same_size_of_commuting_dimensions'
    {m n p q : ℕ}
    (hAB : n = p)
    (hBA : q = m)
    (hrow : m = p)
    --(hcol : q = n)
    : n = p ∧ q = m ∧ m = p := by
  constructor
  · exact hAB
  · constructor
    · exact hBA
    · exact hrow

/- **Proposition 2.1** Let A be an n by n matrix. If A commutes with any n by n matrix,
then A=cIₙ for some number c.

*proof.* Let Uᵢ be the matrix whose (i,i)-entry is 1 and whose other entries are 0.
Then AUᵢ=UᵢA implies that the (i,j)-entry of A is 0 for any i≠j. Thus, A is a diagonal matrix.
Now let Uᵢⱼ be the matrix whose (i,j)-entry is 1 and whose other entries are 0.
Then AUᵢⱼ=UᵢⱼA implies that the (i,i)-entry of A is equal to the (j,j)-entry of A.
Thus, all diagonal entries of A are equal, and hence A=cIₙ for some number c.
-/

lemma proposition_2_1
    {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hcomm :
      ∀ B : Matrix (Fin n) (Fin n) ℂ,
        A * B = B * A) :
    ∃ c : ℂ, A = c•1 := by
  /-
  Step 1.
  Use Uᵢ, the matrix whose (i,i)-entry is 1
  and whose other entries are 0.
  -/
  have hoff :         --Claim Aᵢⱼ = 0 for i ≠ j
      ∀ i j : Fin n, i ≠ j → A i j = 0 := by
    intro i j hij     -- Let i and j be distinct indices in Fin n
    let U : Matrix (Fin n) (Fin n) ℂ :=   -- Let U be the matrix whose (i,j)-entry is 1 and whose other entries are 0.
      Matrix.single i i 1
    have hU : A * U = U * A := hcomm U  -- By assumption, A commutes with U.
    have hentry : (A * U) i j = (U * A) i j := --Thus, the (i,j)-entry of AU is equal to the (i,j)-entry of UA.
      congrArg (fun M => M i j) hU
    simp only [U] at hentry       -- Unfold the definition of U in the equation above.
    simp only [Matrix.mul_apply, Matrix.single] at hentry   -- Unfold the definition of matrix multiplication in the equation above.
    simp? [hij] at hentry  -- Use the fact that i ≠ j to simplify the equation above.
    symm
    exact hentry
  /-
  Step 2.
  Use Uᵢᵢ₀, the matrix whose (i,i₀)-entry is 1
  and whose other entries are 0.
  -/
  let i0 : Fin n := ⟨0, hn⟩  -- Let i₀ be the first index in Fin n, i.e. i₀ = 0.
  have hdiag : ∀ i : Fin n, A i i = A i0 i0 := by -- Claim that Aᵢᵢ = Aᵢ₀ᵢ₀ for all i in Fin n.
    intro i       -- Let i be an index in Fin n.
    let U : Matrix (Fin n) (Fin n) ℂ :=  -- Let U be the matrix whose (i,i₀)-entry is 1 and whose other entries are 0.
      Matrix.single i i0 1
    have hU : A * U = U * A := hcomm U
    have hentry : (A * U) i i0 = (U * A) i i0 :=
      congrArg (fun M => M i i0) hU
    simpa [mul_apply, U, single] using hentry
  use A i0 i0   -- Let c = Aᵢ₀ᵢ₀. Then A = cIₙ.
  ext i j       -- Let i and j be indices in Fin n. We need to show that Aᵢⱼ = cIₙᵢⱼ.
  by_cases hij : i = j  --  We consider two cases: i = j and i ≠ j.
  · subst j     --  If i = j, then Aᵢⱼ = Aᵢᵢ = c = cIₙᵢⱼ. After simplification, we have Aᵢⱼ = cIₙᵢⱼ.
    simp?
    exact hdiag i
  · rw [hoff i j hij] -- If i ≠ j, then Aᵢⱼ = 0 = cIₙᵢⱼ. After simplification, we have Aᵢⱼ = cIₙᵢⱼ.
    simp [hij]


def MyTrans
    {m n α : Type}(A : Matrix m n α) : Matrix n m α :=
  fun i j => A j i

def AA : Matrix (Fin 2) (Fin 3) ℚ :=
  !![
    1, 2, 3;
    4, 5, 6
  ]

#eval MyTrans AA

example {m n : Type} (A : Matrix m n ℚ) : MyTrans A = Aᵀ :=by
  rfl

example {m n : Type} (A : Matrix m n ℚ) : Aᵀᵀ = A := by
  rfl

/-In-Class-Practice-/
example {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (B : Matrix (Fin n) (Fin k) ℚ) :
    (A * B)ᵀ = Bᵀ * Aᵀ := by
  sorry

example {m n k l : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin k) ℚ)
    (C : Matrix (Fin k) (Fin l) ℚ) :
    (A * B * C)ᵀ = Cᵀ * Bᵀ * Aᵀ := by
  sorry
--hint:transpose_apply, Finset.sum_mul, Finset.sum_comm, Finset.sum_congr

/- **Associativity** Let A, B, and C be m×n, n×p, p×q matrices respectively.
Then (AB)C = A(BC).

*proof.* Let i and l be indices in Fin m and Fin q respectively.
Then our goal is to show that ((AB)C)ᵢⱼ = (A(BC))ᵢⱼ.
After expanding the definitions of matrix multiplication, we have
((AB)C)ᵢⱼ = ∑ₖ (∑ₗ Aᵢₗ Bₗₖ) Cₖⱼ and (A(BC))ᵢⱼ = ∑ₖ Aᵢₖ (∑ⱼ Bₖⱼ Cⱼₗ).
The left-hand side is ∑ₖ ∑ₗ (Aᵢₗ Bₗₖ) Cₖⱼ
The right-hand side is ∑ₖ ∑ₗAᵢₖ (Bₖₗ Cₗⱼ)
Since the sums are over finite indices, the double sums are commutative.
Thus, we have ∑ₖ ∑ₗ (Aᵢₗ Bₗₖ) Cₖⱼ = ∑ₗ ∑ₖ Aᵢₖ (Bₖₗ Cₗⱼ).
Set the index of outer sum to be k and the index of the inner sum to be l.
Then we have ((AB)C)ᵢⱼ = (A(BC))ᵢⱼ by the associativity (Aᵢₛ Bₛₜ) Cₜⱼ = Aᵢₛ (Bₛₜ Cₜⱼ).
-/

theorem matrix_assoc_basic
  {m n p q : Type*} [Fintype n] [Fintype p] (A : Matrix m n ℂ) (B : Matrix n p ℂ) (C : Matrix p q ℂ) :
    (A * B) * C = A * (B * C) := by
  ext i l
  simp only [mul_apply]
  change
    (∑ k : p, (∑ j : n, A i j * B j k) * C k l) =
      ∑ j : n, A i j * (∑ k : p, B j k * C k l)
  simp_rw [Finset.sum_mul]
  change
    (∑ k : p, ∑ j : n, A i j * B j k * C k l) =
      ∑ j : n, A i j * (∑ k : p, B j k * C k l)
  simp_rw [Finset.mul_sum]
  change
    ∑ k : p, ∑ j : n, A i j * B j k * C k l =
      ∑ j : n, ∑ k : p, A i j *  (B j k * C k l)
  rw [Finset.sum_comm]
  change
    ∑ j : n, ∑ k : p, A i j * B j k * C k l =
      ∑ j : n, ∑ k : p, A i j *  (B j k * C k l)
  congr 1 with s; congr 1 with t
  ring

/-**Definition 2.1** Let A and B be n×n matrices.
we say B is inverse of A if AB = BA = Iₙ.
In this case, we call A invertible and denote its inverse by A⁻¹.
-/
def IsInverse
    {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A * B = 1 ∧ B * A = 1

def IsInvertible
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ B, IsInverse A B

example {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : IsInverse A B) :
    IsInverse B A := by
  trivial

/-**Lemma 2.2** Let A be an n×n matrix. If A is invertible, then its inverse is unique.

*proof.* Since A is invertible, there exists B: a matrix B such that hB: AB = BA = Iₙ.
To show that the inverse is unique, we need to show
1. there is a matrix;
2. this matrix is an inverse of A;
3. if C is another matrix such that hC: AC = CA = Iₙ, then B = C.
Goal 1 is satisfied by the existence of B. Goal 2 is satisfied by hB.
To show Goal 3, we assume that C is another matrix such that hC: AC = CA = Iₙ. Then we have
  C = Iₙ * C
    = (B * A) * C by BA = Iₙ
    = B * (A * C) by associativity of matrix multiplication
    = B * Iₙ by AC = Iₙ
    = B
Thus, B = C. Therefore, the inverse of A is unique.
-/

lemma inverse_unique
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsInvertible A) :
    ∃! B, IsInverse A B := by
  unfold IsInvertible at *
  unfold IsInverse at *
  rcases hA with ⟨B, hB⟩
  refine ⟨?_, ?_, ?_⟩
  · use B
  · exact hB
  · intro C hC
    rcases hC with ⟨hAC, hCA⟩
    calc
      C = 1 * C := by rw [Matrix.one_mul]
      _ = (B * A) * C := by rw [hB.2]
      _ = B * (A * C) := by exact matrix_assoc_basic B A C
      _ = B * 1 := by rw [hAC]
      _ = B := by rw [Matrix.mul_one]

/-In-Class-Practice-/

lemma inverse_unique_practice
    {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsInverse A B)
    (hC : IsInverse A C) :
    B = C := by
  sorry

/-**Proposition 2.3.** If A ∈ Mₙ(F) is invertible, then
for every b ∈ Fⁿ, the system Ax=b has the unique solution

*proof.* Since A is invertible, there exists B: a matrix B such that hAB: AB = Iₙ and hBA: BA = Iₙ.
To show that the system Ax=b has a unique solution, we need to show
1. there is an x ∈ Fⁿ which is a solution;
2. this solution is unique.
To show the first claim, we let x = Bb. Then Ax = A(Bb) = (AB)b = Iₙb = b. Thus, x is a solution.
To show the second claim, we assume that y is another solution such that Ay = b.
Then we have
  y = Iₙy
    = (BA)y by hBA
    = B(Ay) by associativity of matrix multiplication
    = Bb by Ay = b
Thus, y = Bb. Therefore, the solution is unique.
-/

theorem solution_unique
  (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
  (hA : IsInvertible A) (b : Fin n → ℂ) :
    ∃! x : Fin n → ℂ, A *ᵥ x = b := by
  rcases hA with ⟨B, hAB, hBA⟩
  refine ⟨B *ᵥ b, ?_, ?_⟩
  · calc
    A *ᵥ (B*ᵥ b) = (A * B) *ᵥ b := by rw [mulVec_mulVec]
    _ = 1 *ᵥ b := by rw [hAB]
    _ = b := by rw [Matrix.one_mulVec]
  · intro y hy
    calc
    y = 1 *ᵥ y := by rw [Matrix.one_mulVec]
    _ = (B * A) *ᵥ y := by rw [hBA]
    _ = B *ᵥ (A *ᵥ y) := by rw [mulVec_mulVec]
    _ = B *ᵥ b := by rw [hy]
