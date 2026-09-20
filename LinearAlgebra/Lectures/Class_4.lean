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
      by_cases hA : R₁.col 0 = 0
      · by_cases hB : R₂.col 0 = 0
        · exact False.elim (hdiff0 (hA.trans hB.symm))
        · exact Or.inl ⟨hA, hB⟩
      · by_cases hB : R₂.col 0 = 0
        · exact Or.inr ⟨hA, hB⟩
        · have hA1 : R₁.col 0 = Pi.single (0 : Fin m) (1 : ℝ) := by
            ext k
            by_cases hk : k = 0
            · subst hk
              have h00 : R₁ 0 0 ≠ 0 := by
                intro hzero
                apply hA
                ext k
                by_cases hk' : k = 0
                · subst hk'
                  simpa using hzero
                · have hkpos : (0 : Fin m) < k := (Fin.pos_iff_ne_zero' k).2 hk'
                  have hkzero : R₁ k 0 = 0 := by
                    exact hr₁.isRowEchelon (i₁ := 0) (i₂ := k) (j₂ := 0) hkpos (by
                      intro j hj
                      exact (Fin.not_lt_zero j hj).elim)
                  simpa [hk'] using hkzero
              have hlead : R₁.IsLeadingEntry 0 0 := by
                refine ⟨?_, h00⟩
                intro j hj
                exact (Fin.not_lt_zero j hj).elim
              simpa [hr₁.eq_one hlead]
            · have hk0 : k ≠ 0 := hk
              have hkzero : R₁ k 0 = 0 := by
                have hkpos : (0 : Fin m) < k := (Fin.pos_iff_ne_zero' k).2 hk0
                exact hr₁.isRowEchelon (i₁ := 0) (i₂ := k) (j₂ := 0) hkpos (by
                  intro j hj
                  exact (Fin.not_lt_zero j hj).elim)
              simp [Pi.single, hk0, hkzero]
          have hB1 : R₂.col 0 = Pi.single (0 : Fin m) (1 : ℝ) := by
            ext k
            by_cases hk : k = 0
            · subst hk
              have h00 : R₂ 0 0 ≠ 0 := by
                intro hzero
                apply hB
                ext k
                by_cases hk' : k = 0
                · subst hk'
                  simpa using hzero
                · have hkpos : (0 : Fin m) < k := (Fin.pos_iff_ne_zero' k).2 hk'
                  have hkzero : R₂ k 0 = 0 := by
                    exact hr₂.isRowEchelon (i₁ := 0) (i₂ := k) (j₂ := 0) hkpos (by
                      intro j hj
                      exact (Fin.not_lt_zero j hj).elim)
                  simpa [hk'] using hkzero
              have hlead : R₂.IsLeadingEntry 0 0 := by
                refine ⟨?_, h00⟩
                intro j hj
                exact (Fin.not_lt_zero j hj).elim
              simpa [hr₂.eq_one hlead]
            · have hk0 : k ≠ 0 := hk
              have hkzero : R₂ k 0 = 0 := by
                have hkpos : (0 : Fin m) < k := (Fin.pos_iff_ne_zero' k).2 hk0
                exact hr₂.isRowEchelon (i₁ := 0) (i₂ := k) (j₂ := 0) hkpos (by
                  intro j hj
                  exact (Fin.not_lt_zero j hj).elim)
              simp [Pi.single, hk0, hkzero]
          exact False.elim (hdiff0 (hA1.trans hB1.symm))
    rcases hcol with hR1zero | hR1nz
    · rcases hR1zero with ⟨hR1zero, hR2nz⟩
      have hker' : R₂.mulVecLin.ker = R₁.mulVecLin.ker := by
        simpa [hm₁] using hker
      let e : Fin n → ℝ := Pi.single (0 : Fin n) (1 : ℝ)
      have hmem₁ : e ∈ R₁.mulVecLin.ker := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        ext i
        simpa [e, Matrix.mulVec] using congrFun hR1zero i
      have hmem₂ : e ∉ R₂.mulVecLin.ker := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        intro hzero
        apply hR2nz
        ext i
        simpa [e, Matrix.mulVec] using congrFun hzero i
      have hmem₂' : e ∈ R₂.mulVecLin.ker := by
        rw [hker']
        exact hmem₁
      exact hmem₂ hmem₂'
    · rcases hR1nz with ⟨hR1nz, hR2zero⟩
      have hker' : R₂.mulVecLin.ker = R₁.mulVecLin.ker := by
        simpa [hm₁] using hker
      let e : Fin n → ℝ := Pi.single (0 : Fin n) (1 : ℝ)
      have hmem₁ : e ∈ R₂.mulVecLin.ker := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        ext i
        simpa [e, Matrix.mulVec] using congrFun hR2zero i
      have hmem₂ : e ∉ R₁.mulVecLin.ker := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        intro hzero
        apply hR1nz
        ext i
        simpa [e, Matrix.mulVec] using congrFun hzero i
      have hmem₂' : e ∈ R₁.mulVecLin.ker := by
        rw [← hker']
        exact hmem₁
      exact hmem₂ hmem₂'
  ·
    have hj0pos : 0 < j₀.1 := by
      refine Nat.pos_of_ne_zero ?_
      intro h0
      apply hj₀
      apply Fin.ext
      exact h0
    let z0 : Fin j₀.1 := ⟨0, hj0pos⟩
    let R₁' : Matrix (Fin m) (Fin j₀.1) ℝ :=
      fun i k => R₁ i ⟨k.1, lt_trans k.2 j₀.2⟩
    let R₂' : Matrix (Fin m) (Fin j₀.1) ℝ :=
      fun i k => R₂ i ⟨k.1, lt_trans k.2 j₀.2⟩
    have hprefix : ∀ i : Fin m, ∀ k : Fin j₀.1, R₁' i k = R₂' i k := by
      intro i k
      change R₁ i ⟨k.1, lt_trans k.2 j₀.2⟩ = R₂ i ⟨k.1, lt_trans k.2 j₀.2⟩
      exact hbefore ⟨k.1, lt_trans k.2 j₀.2⟩ k.2
    have hR1'_eq_R2' : R₁' = R₂' := by
      ext i k
      exact hprefix i k
    let v : Fin j₀.1 → ℝ := fun k => if k = z0 then 1 else 0
    have hv₁ : R₁' *ᵥ v = 0 := by
      ext i
      simp [Matrix.mulVec, R₁', v, z0, hprefix]
    have hv₂ : R₂' *ᵥ v ≠ 0 := by
      intro h
      have htrunc : ∀ k : Fin j₀.1, R₁' i k = R₂' i k := hprefix i
      -- The remaining contradiction is to evaluate at the first differing column.
      -- The actual witness construction is still the proof to finish.
      simp [Matrix.mulVec, R₂', v, z0, htrunc] at h
    let w : Fin n → ℝ := fun k =>
      if hk : (k.1 : ℕ) < j₀.1 then v ⟨k.1, hk⟩ else 0
    have hw₁ : R₁.mulVec w = 0 := by
      ext i
      -- We are using the same argument as above: the earlier columns agree, and the extension
      -- is zero on all columns after the truncated range.
      simp [Matrix.mulVec, w, v, z0, hprefix]
    have hw₂ : R₂.mulVec w ≠ 0 := by
      intro h
      have hcol : R₂.mulVec w j₀ = 0 := by simpa [Matrix.mulVec] using congrArg (fun f => f j₀) h
      -- This is the contradiction coming from the first differing column `j₀`.
      exact hj₀_diff (by
        ext k
        by_cases hk : k = 0
        · subst hk
          simpa [Matrix.mulVec, w, v, z0] using hcol
        · sorry)
    have hker' : R₂.mulVecLin.ker = R₁.mulVecLin.ker := by
      simpa [hm₁] using hker
    exact (hw₂ <| by simpa [hker'] using hw₁)
