import LinearAlgebra.VectorSimp

/-!
Regression examples for the public vector_simp interface.
Run lake env lean LinearAlgebra/Tests/VectorSimp.lean after building the module.
The numerical fixtures are independent of the homework answers.
-/

namespace VectorSimpTests

open scoped BigOperators
open scoped Classical

theorem function_axioms (X : Type*) : VectorSpaceAxioms (X → ℝ) ℝ where
  add_comm := add_comm
  add_assoc := add_assoc
  zero_add := zero_add
  neg_add_cancel := neg_add_cancel
  one_smul := one_smul ℝ
  mul_smul := mul_smul
  smul_add := smul_add
  add_smul := add_smul

def u : Fin 3 → ℝ := ![1, 0, 1]
def v : Fin 3 → ℝ := ![0, 1, 2]
def b : Fin 3 → ℝ := ![3, 2, 7]
noncomputable def S : Finset (Fin 3 → ℝ) := {u, v}

-- Reveals the coefficients but leaves the mathematical choice to the user.
theorem pair_coefficients :
    IsLinearCombination (function_axioms (Fin 3)) S b := by
  -- Importing the package does not change ordinary simp.
  fail_if_success solve | simp [S]
  vector_simp [S]
  change ∃ a c : ℝ, b = a • u + c • v
  refine ⟨3, 2, ?_⟩
  vector_simp [b, u, v]

-- Works from custom course axioms without assuming a Mathlib Module instance.
theorem abstract_pair
    {V K : Type*} [Field K] [AddCommMonoid V] [Neg V] [SMul K V] [DecidableEq V]
    (hV : VectorSpaceAxioms V K) (u v b : V) (a c : K)
    (h : b = a • u + c • v) :
    IsLinearCombination hV {u, v} b := by
  vector_simp
  exact ⟨a, c, h⟩

theorem duplicate_generator :
    IsLinearCombination (function_axioms (Fin 3)) {u, u} ((3 : ℝ) • u) := by
  vector_simp
  refine ⟨3, 0, ?_⟩
  vector_simp

theorem empty_combination :
    IsLinearCombination (function_axioms (Fin 3)) ∅ (0 : Fin 3 → ℝ) := by
  vector_simp

theorem singleton_combination :
    IsLinearCombination (function_axioms (Fin 3)) {u} (![3, 0, 3]) := by
  vector_simp
  refine ⟨3, ?_⟩
  vector_simp [u]

theorem finite_span :
    b ∈ Span (function_axioms (Fin 3)) (S : Set (Fin 3 → ℝ)) := by
  vector_simp [S]
  refine ⟨3, 2, ?_⟩
  vector_simp [b, u, v]

-- The exact scalar-sum shape that originally required sum_coe_sort by hand.
theorem subtype_sum :
    (3 : ℝ) = ∑ x : S,
      (if (x : Fin 3 → ℝ) = u then (3 : ℝ) else 2) * (x : Fin 3 → ℝ) 0 := by
  vector_simp [S, u, v]

theorem attached_sum :
    (3 : ℝ) = ∑ x ∈ S.attach,
      (if (x : Fin 3 → ℝ) = u then (3 : ℝ) else 2) * (x : Fin 3 → ℝ) 0 := by
  vector_simp [S, u, v]

theorem coefficients_sum :
    LinearCombination (function_axioms (Fin 3)) S
      (fun x => if (x : Fin 3 → ℝ) = u then (3 : ℝ) else 2) = b := by
  vector_simp [S, u, v, b]

theorem fin_sum_zero (a : Fin 0 → ℝ) :
    (∑ i, a i) = 0 := by vector_simp

theorem fin_sum_one (a : Fin 1 → ℝ) :
    (∑ i, a i) = a 0 := by vector_simp

theorem fin_sum_two (a : Fin 2 → ℝ) :
    (∑ i, a i) = a 0 + a 1 := by vector_simp

theorem fin_sum_three (a : Fin 3 → ℝ) :
    (∑ i, a i) = a 0 + a 1 + a 2 := by vector_simp

theorem fin_sum_four (a : Fin 4 → ℝ) :
    (∑ i, a i) = a 0 + a 1 + a 2 + a 3 := by vector_simp

-- Dependent coefficients work even though they carry membership proofs.
theorem dependent_pair_sum
    (f : ({(1 : ℕ), 3} : Finset ℕ) → ℝ) :
    (∑ x, f x) = f ⟨1, by simp⟩ + f ⟨3, by simp⟩ := by
  vector_simp

theorem abstract_sum (α : Type*) [DecidableEq α] (x y : α) (hxy : x ≠ y)
    (f : ({x, y} : Finset α) → ℝ) :
    (∑ z, f z) = f ⟨x, by simp⟩ + f ⟨y, by simp⟩ := by
  vector_simp [hxy]

-- Pointwise definitions are automatic; distributivity remains a mathematical step.
theorem symbolic_dimension (n : ℕ) (a : ℝ) (f g : Fin n → ℝ) :
    a • (f + g) = a • f + a • g := by
  fail_if_success solve | vector_simp
  vector_simp
  exact mul_add _ _ _

theorem coefficient_distributivity (n : ℕ) (a c : ℝ) (f : Fin n → ℝ) :
    (a + c) • f = a • f + c • f := by
  fail_if_success solve | vector_simp
  vector_simp
  exact add_mul _ _ _

theorem scalar_distributivity (a x y : ℝ) :
    a * (x + y) = a * x + a * y := by
  fail_if_success solve | vector_simp
  exact mul_add _ _ _

-- The scalar addition law is still visible after taking function values.
theorem function_calculation (f g : ℝ → ℝ) :
    f + g = g + f := by
  fail_if_success solve | vector_simp
  vector_simp
  exact add_comm _ _

theorem scalar_commutativity (x y : ℝ) : x + y = y + x := by
  fail_if_success solve | vector_simp
  exact add_comm _ _

-- Neither expanding a small index nor polynomial normalization may hide a swap.
theorem double_sum_two (f : Fin 2 → Fin 2 → ℝ) :
    (∑ i, ∑ j, f i j) = ∑ j, ∑ i, f i j := by
  fail_if_success solve | vector_simp
  exact Finset.sum_comm

theorem double_sum_dimensions (m n : ℕ) (f : Fin m → Fin n → ℝ) :
    (∑ i, ∑ j, f i j) = ∑ j, ∑ i, f i j := by
  fail_if_success solve | vector_simp
  exact Finset.sum_comm

def numericGrid : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]

-- Even fully concrete nested sums require an explicit summation operation.
theorem double_sum_numeric :
    (∑ i, ∑ j, numericGrid i j) = ∑ j, ∑ i, numericGrid i j := by
  fail_if_success solve | vector_simp [numericGrid]
  exact Finset.sum_comm

theorem double_sum_numeric_evaluation :
    (∑ i, ∑ j, numericGrid i j) = 10 := by
  fail_if_success solve | vector_simp [numericGrid]
  simp only [Fin.sum_univ_two]
  vector_simp [numericGrid]

def A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
def B : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 0, -1]

theorem matrix_calculation :
    (2 : ℝ) • A + B = !![4, 5; 6, 7] := by
  vector_simp [A, B]


theorem duplicate_sum :
    (∑ _x : ({(1 : ℕ), 1} : Finset ℕ), (2 : ℝ)) = 2 := by
  vector_simp

theorem empty_subtype_sum (f : (∅ : Finset ℕ) → ℝ) :
    (∑ x, f x) = 0 := by
  vector_simp

theorem singleton_subtype_sum (f : ({(2 : ℕ)} : Finset ℕ) → ℝ) :
    (∑ x, f x) = f ⟨2, by simp⟩ := by
  vector_simp

-- A scalar definition and facts can be passed without naming package lemmas.
def twice (x : ℝ) : ℝ := x + x
theorem extra_rewrite (x : ℝ) (hx : x = 3) : twice x = 6 := by
  vector_simp [twice, hx]

-- Leaves a false claim unproved.
example : True := by
  fail_if_success
    have bad : (1 : ℝ) = 2 := by vector_simp
  trivial


theorem linear_combination_nested_sum :
    LinearCombination (function_axioms (Fin 1)) {(![1] : Fin 1 → ℝ)}
      (fun _ => ∑ _i : Fin 2, (1 : ℝ)) = ![2] := by
  fail_if_success solve | vector_simp
  simp only [Fin.sum_univ_two]
  vector_simp


end VectorSimpTests
