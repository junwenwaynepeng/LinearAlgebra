import Mathlib
/-!-/
open Matrix
open scoped BigOperators

theorem rref_unique
    {m n : ℕ}
    {R₁ R₂ : Matrix (Fin m) (Fin (n)) ℝ}
    (hr₁ : R₁.IsReducedRowEchelon)
    (hr₂ : R₂.IsReducedRowEchelon)
    (h : R₁.RowEquivalent R₂) :
    R₁ = R₂ := by
  by_contra
  unfold RowEquivalent at *
  unfold MulAction.orbit at *
  unfold Set.range at *
  obtain ⟨m₁, hm₁⟩ := h
  simp at hm₁
  have hker : (((m₁ : Matrix (Fin m) (Fin m) ℝ) * R₁).mulVecLin).ker =
      R₁.mulVecLin.ker := by
    ext v
    constructor
    · intro hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      have hv' := congrArg
        (fun w : Fin m → ℝ => (↑(m₁⁻¹) : Matrix (Fin m) (Fin m) ℝ) *ᵥ w) hv
      have hv'' :
          (((↑(m₁⁻¹) : Matrix (Fin m) (Fin m) ℝ) * (↑m₁ : Matrix (Fin m) (Fin m) ℝ)) * R₁) *ᵥ v = 0 := by
        simpa [Matrix.mulVec_mulVec] using hv'
      have hunit :
          (↑(m₁⁻¹) : Matrix (Fin m) (Fin m) ℝ) * (↑m₁ : Matrix (Fin m) (Fin m) ℝ) = 1 := by
        exact m₁.inv_val
      rw [hunit] at hv''
      simpa using hv''
    · intro hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp this
  obtain ⟨j, hij⟩ := Function.ne_iff.mp hi

  letI mneZero : NeZero m := i.neZero
  letI nneZero : NeZero n := j.neZero

  have hj' : R₁.col j ≠ R₂.col j := by
    intro hcol
    apply hij
    exact congrFun hcol i

  let S : Finset (Fin n) :=
    Finset.univ.filter (fun j => R₁.col j ≠ R₂.col j)

  have hS : S.Nonempty := by
    refine ⟨j, ?_⟩
    simp [S, hj']

  let j₀ : Fin n := S.min' hS

  have hj₀_diff : R₁.col j₀ ≠ R₂.col j₀ := by
    have hj₀_mem : j₀ ∈ S := by
      simpa [j₀] using S.min'_mem hS
    simpa [S] using hj₀_mem

  have hbefore :
      ∀ k < j₀, R₁.col k = R₂.col k := by
    intro k hk
    by_contra hneq

    have hk_mem : k ∈ S := by
      simp [S, hneq]

    have hj₀_le_k : j₀ ≤ k := by
      simpa [j₀] using Finset.min'_le S k hk_mem

    exact (not_le_of_gt hk) hj₀_le_k

  by_cases hj₀ : j₀ = 0
  · have hdiff0 : R₁.col 0 ≠ R₂.col 0 := by
      simpa [hj₀] using hj₀_diff
    have hcol : (R₁.col 0 = 0 ∧ R₂.col 0 ≠ 0) ∨ (R₁.col 0 ≠ 0 ∧ R₂.col 0 = 0) := by
      aesop
    aesop
  · aesop
          simpa [k12] using k12'
      have hker₂ : R₂.mulVecLin.ker = R₁.mulVecLin.ker := by
        rw [← hm₁]
        exact hker
      exact hx.2 (hker₂.symm ▸ hx.1)
    · obtain ⟨k21, k22⟩ := k2
      let x : Fin n → ℝ := Pi.single (0 : Fin n) 1
      have hx : x ∈ R₂.mulVecLin.ker ∧ x ∉ R₁.mulVecLin.ker := by
        constructor
        · simp [x]
          ext k
          change R₂ k 0 = 0
          by_cases hk : k = 0
          · subst k; exact k21
          · have kpos : (0 : Fin m) < k := by exact (Fin.pos_iff_ne_zero' k).2 hk
            apply hr₂.isRowEchelon kpos
            intro j₁ hj₁
            simp at hj₁
        · simp [x]
          intro hcol
          have k22' : R₁ 0 0 = 0 := by
            simpa using congrFun hcol 0
          simpa [k22] using k22'
      have hker₂ : R₂.mulVecLin.ker = R₁.mulVecLin.ker := by
        rw [hm₁.symm]
        exact hker
      exact hx.2 (hker₂ ▸ hx.1)
  · ext i j
-/
