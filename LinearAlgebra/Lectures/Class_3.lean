import Mathlib

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

/-* Lemma 2.1 - Assume that $A$ and $B$ are matrices of sizes $m\times n$ and $p\times q$.
If $AB = BA$, then $m=n=p=q$; that is, $A$ and $B$ are square matrices of the same size.

poof. By assumption, $A$ is an $m\times n$ matrix, and $B$ is a $p\times q$ matrix.
Since $AB$ and $BA$ are well-defined, $n=p$ and $q=m$.
Then $AB$ is an $m\times q$ matrix and $BA$ is a $p\times n$ matrix.
Finally, the assumption $AB = BA$ implies $m\times q = p\times n$.
Thus, $m=p$ and $n=q$. Therefore, $A$ and $B$ are square matrices of the same size.
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


/- Proposition 2.2 Let $A$ be an $n$ by $n$ matrix. If $A$ commutes with any $n$ by $n$ matrix, then $A=cI_n$ for some number $c$.

proof. Let $U_i$ be the matrix whose $(i,i)$-entry is $1$ and whose other entries are $0$.
Then $AU_i=U_iA$ implies that the $(i,j)$-entry of $A$ is $0$ for any $i\neq j$. Thus, $A$ is a diagonal matrix.
Now let $U_{ij}$ be the matrix whose $(i,j)$-entry is $1$ and whose other entries are $0$.
Then $AU_{ij}=U_{ij}A$ implies that the $(i,i)$-entry of $A$ is equal to the $(j,j)$-entry of $A$.
Thus, all diagonal entries of $A$ are equal, and hence $A=cI_n$ for some number $c$.
-/


lemma proposition_2_2
    (n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hcomm :
      ∀ B : Matrix (Fin n) (Fin n) ℂ,
        A * B = B * A) :
    ∃ c : ℂ, A = (Matrix.scalar (Fin n)) c := by
  /-
  Step 1.
  Use U_i, the matrix whose (i,i)-entry is 1
  and whose other entries are 0.
  -/
  have hoff :
      ∀ i j : Fin n, i ≠ j → A i j = 0 := by
    intro i j hij
    let U : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.single i i 1
    have hU : A * U = U * A := hcomm U
    have hentry : (A * U) i j = (U * A) i j :=
      congrArg (fun M => M i j) hU
    simp [Matrix.mul_apply, U, Matrix.single, hij] at hentry
    symm
    exact hentry
    --simpa [Matrix.mul_apply, U, Matrix.single, hij] using hentry.symm
  let i0 : Fin n := ⟨0, hn⟩
  have hdiag : ∀ i : Fin n, A i i = A i0 i0 := by
    intro i
    let U : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.single i i0 1
    have hU : A * U = U * A := hcomm U
    have hentry : (A * U) i i0 = (U * A) i i0 :=
      congrArg (fun M => M i i0) hU
    simpa [Matrix.mul_apply, U, Matrix.single] using hentry
  let c := A i0 i0
  refine ⟨c, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [Matrix.scalar] using hdiag i
  · rw [hoff i j hij]
    simp [Matrix.scalar, hij]




theorem matrix_assoc_basic
  {m n p q : Type*} [Fintype n] [Fintype p] (A : Matrix m n ℂ) (B : Matrix n p ℂ) (C : Matrix p q ℂ) :
    (A * B) * C = A * (B * C) := by
  -- Step 1: Two matrices are equal if all their entries (i, l) are equal
  ext i l
  -- Step 2: Unfold the definition of matrix multiplication on both sides
  -- This replaces the '*' with explicit summation symbols (Finset.sum)
  simp [mul_apply]
  -- Step 3: Distribute the C_kl entry into the inner sum on the left-hand side
  simp_rw [Finset.sum_mul]
  -- Step 4: Distribute the A_ij entry into the inner sum on the right-hand side
  simp_rw [Finset.mul_sum]
  -- Step 5: Swap the order of summation (∑ j, ∑ k ...) to match (∑ k, ∑ j ...)
  -- and use the commutativity of scalar multiplication (A * B * C = A * (B * C))
  rw [Finset.sum_comm]
  -- Step 6: Ensure the terms inside the sums match exactly using associativity of α
  congr 1 with k
  congr 1 with j
  ring


def IsInverse
    {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A * B = 1 ∧ B * A = 1

def IsInvertible
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ B, IsInverse A B

theorem inverse_unique
    {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsInverse A B)
    (hC : IsInverse A C) :
    B = C := by
  unfold IsInverse at *
  rcases hB with ⟨hAB, hBA⟩
  /-
  cases hB with
  |  intro hAB hBA
  -/
  rcases hC with ⟨hAC, hCA⟩
  calc
    B = 1 * B := by rw [Matrix.one_mul]
    _ = (C * A) * B := by rw [hCA]
    _ = C * (A * B) := by exact matrix_assoc_basic C A B
    _ = C * 1 := by rw [hAB]
    _ = C := by rw [Matrix.mul_one]


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

example {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (B : Matrix (Fin n) (Fin k) ℚ) :
    (A * B)ᵀ = Bᵀ * Aᵀ := by
  ext i j
  simp [Matrix.mul_apply]
  simp [mul_comm]
  --simp [Matrix.mul_apply, Finset.sum_comm, mul_comm]

example {m n k l : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin k) ℚ)
    (C : Matrix (Fin k) (Fin l) ℚ) :
    (A * B * C)ᵀ = Cᵀ * Bᵀ * Aᵀ := by
  ext i j
  simp only[transpose_apply, mul_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro x_1 hx_1
  ring

theorem solution_unique (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsInvertible A) (b : Fin n → ℂ) :
    ∃! x : Fin n → ℂ, A *ᵥ x = b := by
  rcases hA with ⟨B, hAB, hBA⟩
  by_cases hb : b = (0 : Fin n → ℂ)
  · subst b
    refine ⟨0, ?_, ?_⟩
    · simp
    · intro y hy
      calc
        y = (1 :  Matrix (Fin n) (Fin n) ℂ) *ᵥ y := by rw [Matrix.one_mulVec]
        _ = (B * A) *ᵥ y := by rw [hBA]
        _ = B *ᵥ (A *ᵥ y) := by rw [mulVec_mulVec]
        _ = B *ᵥ 0 := by  rw [hy]
        _ = 0 := by simp
  · refine ⟨B *ᵥ b, ?_, ?_⟩
    · calc
      A *ᵥ (B*ᵥ b) = (A * B) *ᵥ b := by rw [mulVec_mulVec]
      _ = (1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ b := by rw [hAB]
      _ = b := by rw [Matrix.one_mulVec]
    · intro y hy
      calc
      y = (1 :  Matrix (Fin n) (Fin n) ℂ) *ᵥ y := by rw [Matrix.one_mulVec]
      _ = (B * A) *ᵥ y := by rw [hBA]
      _ = B *ᵥ (A *ᵥ y) := by rw [mulVec_mulVec]
      _ = B *ᵥ b := by rw [hy]
