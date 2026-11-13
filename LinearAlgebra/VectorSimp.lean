import Mathlib
import LinearAlgebra.CourseTools

/-!
# Readable simplification for course vector calculations

Import LinearAlgebra.VectorSimp, then use vector_simp or
vector_simp [definitions, extra_lemmas].

## Typical use

For a course goal IsLinearCombination hV S b with S = {u, v}:

  vector_simp [S]
  -- The goal is now ∃ a c, b = a • u + c • v.
  refine ⟨a, c, ?_⟩
  vector_simp [b, u, v]

Choose a and c yourself; vector_simp checks the remaining calculation.
It can also simplify expressions such as ∑ x ∈ S.attach, a x * (x : V) 0,
so the caller need not name sum_coe_sort or perform membership coercions.

## Supported normalization

- Course IsLinearCombination goals over ∅, {u}, or {u,v}.
- Membership in the course Span of a finite generating set.
- Subtype and attach sums over singletons and distinct pairs.
- Sums indexed by Fin 0, Fin 1, Fin 2, Fin 3, or Fin 4.
- Pointwise vector/function/matrix representations and elementary numerical arithmetic.

Pass definitions to unfold or extra rewrite facts in brackets, just as with simp.
Automatic coordinate enumeration is limited to Fin n with a concrete n ≤ 4.
For larger or symbolic dimensions, the tactic keeps a general coordinate.
## Teaching boundary

The default tactic handles representation changes: subtype membership data,
attach/coercion bookkeeping, pointwise operations, single-layer finite sums,
and numerical evaluation (including zero/one simplifications).

Students still choose coefficients and linear combinations, apply subspace
closure, use distributivity, interchange sums, and organize induction.
Nested sums, including sums used as LinearCombination coefficients, remain
visible and are not automatically expanded or evaluated.
For example, write rw [Finset.sum_comm] explicitly for a finite sum interchange,
or use mul_add/add_mul explicitly after taking function values.

There is no automatic ring normalization. Simplification uses a fixed rule
list, not the imported global simp set. Extra facts supplied in brackets are
explicit choices by the caller. Importing this module does not change simp.

The tactic runs on an already elaborated goal. It does not repair ill-typed
terms, missing type annotations, or missing proof fields in a construction.

This file uses the global CourseTools definitions. Separately copied lecture
definitions in a namespace must be converted to those definitions explicitly.
-/

namespace VectorSimp

open scoped BigOperators

theorem sum_singleton_subtype
    {ι M : Type*} [AddCommMonoid M]
    (u : ι) (f : ({u} : Finset ι) → M) :
    (∑ x, f x) = f ⟨u, by simp⟩ := by
  classical
  let F : ι → M := fun x => if h : x ∈ ({u} : Finset ι) then f ⟨x, h⟩ else 0
  calc
    (∑ x, f x) = ∑ x : ({u} : Finset ι), F x := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [F, dite_eq_left x.property]
    _ = ∑ x ∈ ({u} : Finset ι), F x := Finset.sum_coe_sort _ F
    _ = f ⟨u, by simp⟩ := by simp [F]

theorem sum_pair_subtype
    {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (u v : ι) (huv : u ≠ v) (f : ({u, v} : Finset ι) → M) :
    (∑ x, f x) = f ⟨u, by simp⟩ + f ⟨v, by simp⟩ := by
  let F : ι → M := fun x => if h : x ∈ ({u, v} : Finset ι) then f ⟨x, h⟩ else 0
  calc
    (∑ x, f x) = ∑ x : ({u, v} : Finset ι), F x := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [F, dite_eq_left x.property]
    _ = ∑ x ∈ ({u, v} : Finset ι), F x := Finset.sum_coe_sort _ F
    _ = F u + F v := Finset.sum_pair huv
    _ = f ⟨u, by simp⟩ + f ⟨v, by simp⟩ := by simp [F]

/-- Expand a pair sum while counting repeated set elements only once. -/
theorem sum_pair_subtype_if
    {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (u v : ι) (f : ({u, v} : Finset ι) → M) :
    (∑ x, f x) =
      if u = v then f ⟨u, by simp⟩
      else f ⟨u, by simp⟩ + f ⟨v, by simp⟩ := by
  let F : ι → M := fun x => if h : x ∈ ({u, v} : Finset ι) then f ⟨x, h⟩ else 0
  calc
    (∑ x, f x) = ∑ x : ({u, v} : Finset ι), F x := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [F, dite_eq_left x.property]
    _ = ∑ x ∈ ({u, v} : Finset ι), F x := Finset.sum_coe_sort _ F
    _ = if u = v then F u else F u + F v := by
      by_cases huv : u = v
      · subst v
        simp
      · simp [huv]
    _ = _ := by simp [F]

theorem sum_attach
    {ι M : Type*} [AddCommMonoid M]
    (S : Finset ι) (f : S → M) :
    (∑ x ∈ S.attach, f x) = ∑ x : S, f x :=
  (Finset.sum_coe_sort_eq_attach S f).symm

theorem isLinearCombination_empty_iff
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (b : V) :
    IsLinearCombination hV ∅ b ↔ b = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    simpa [LinearCombination] using ha
  · intro hb
    refine ⟨(fun _ => 0), ?_⟩
    simpa [LinearCombination] using hb

theorem isLinearCombination_singleton_iff
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (u b : V) :
    IsLinearCombination hV {u} b ↔ ∃ a : K, b = a • u := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a ⟨u, by simp⟩, ?_⟩
    simpa only [LinearCombination, sum_singleton_subtype] using ha
  · rintro ⟨a, ha⟩
    refine ⟨(fun _ => a), ?_⟩
    simpa only [LinearCombination, sum_singleton_subtype] using ha

/-- A two-term expression gives a finite-set linear combination, including u = v. -/
theorem isLinearCombination_pair
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V] [DecidableEq V]
    (hV : VectorSpaceAxioms V K) (a c : K) {u v b : V}
    (h : b = a • u + c • v) :
    IsLinearCombination hV {u, v} b := by
  by_cases huv : u = v
  · subst v
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self u)]
    apply (isLinearCombination_singleton_iff hV u b).mpr
    exact ⟨a + c, by rw [hV.add_smul]; exact h⟩
  · refine ⟨(fun t => if (t : V) = u then a else c), ?_⟩
    change b = ∑ t : ({u, v} : Finset V),
      (if (t : V) = u then a else c) • (t : V)
    rw [sum_pair_subtype u v huv]
    simpa [huv, Ne.symm huv] using h

theorem isLinearCombination_pair_iff
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V] [DecidableEq V]
    (hV : VectorSpaceAxioms V K) (u v b : V) :
    IsLinearCombination hV {u, v} b ↔ ∃ a c : K, b = a • u + c • v := by
  constructor
  · intro hb
    by_cases huv : u = v
    · subst v
      rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self u)] at hb
      obtain ⟨a, ha⟩ := (isLinearCombination_singleton_iff hV u b).mp hb
      exact ⟨a, 0, by rw [zero_smul_V hV, add_zero]; exact ha⟩
    · obtain ⟨a, ha⟩ := hb
      refine ⟨a ⟨u, by simp⟩, a ⟨v, by simp⟩, ?_⟩
      simpa only [LinearCombination, sum_pair_subtype u v huv] using ha
  · rintro ⟨a, c, h⟩
    exact isLinearCombination_pair hV a c h

theorem mem_span_finset_iff
    {V K : Type*}
    [Field K] [AddCommMonoid V] [Neg V] [SMul K V]
    (hV : VectorSpaceAxioms V K) (S : Finset V) (b : V) :
    b ∈ Span hV (S : Set V) ↔ IsLinearCombination hV S b :=
  ⟨IsLinearCombination.of_mem_span hV, IsLinearCombination.mem_span⟩

end VectorSimp

meta section

open Lean Meta Elab Tactic

namespace VectorSimp

/-- Keep nested summation operations visible for the student. -/
private partial def hasNestedSum (e : Expr) (insideSum : Bool := false) : Bool :=
  if e.isAppOf ``Finset.sum || e.isAppOf ``LinearCombination then
    insideSum || e.getAppArgs.any (fun arg => hasNestedSum arg true)
  else
    match e with
    | .app f a => hasNestedSum f insideSum || hasNestedSum a insideSum
    | .lam _ t b _ | .forallE _ t b _ =>
      hasNestedSum t insideSum || hasNestedSum b insideSum
    | .letE _ t v b _ =>
      hasNestedSum t insideSum || hasNestedSum v insideSum || hasNestedSum b insideSum
    | .mdata _ b | .proj _ _ b => hasNestedSum b insideSum
    | _ => false

/-- Inspect only equality goals, introducing coordinates without opening existential goals. -/
private partial def simplifyCoordinates (finish : Syntax) : TacticM Unit := focus do
  withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    match target.getAppFnArgs with
    | (``Eq, #[α, _, _]) =>
      if (← whnf α).isForall then
        let [next] ← goal.apply (← mkConstWithFreshMVarLevels ``funext)
          | throwError "vector_simp: could not introduce a coordinate"
        let (index, next) ← next.intro1
        let indexType ← next.withContext do whnf (← index.getType)
        let mut goals := [next]
        match indexType.getAppFnArgs with
        | (``Fin, #[n]) =>
          match ← whnf n with
          | .lit (.natVal k) =>
            if k ≤ 4 then
              goals ← finCasesAt next index
          | _ => pure ()
        | _ => pure ()
        setGoals goals
        allGoals (simplifyCoordinates finish)
      else
        evalTactic finish
    | _ => evalTactic finish

end VectorSimp

/-- Simplify elementary course vector calculations, optionally unfolding the listed definitions.
Existential coefficient choices remain for the student to supply. -/
syntax (name := vectorSimp) "vector_simp"
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),*,? "]")? : tactic

elab_rules : tactic
  | `(tactic| vector_simp) => do evalTactic (← `(tactic| vector_simp []))
  | `(tactic| vector_simp [$args,*]) => do
    -- Only caller-supplied rewrites are allowed during this preparation step.
    evalTactic (← `(tactic| try simp (config := { instances := true }) only [$args,*]))
    if (← getGoals).isEmpty then return
    let nested ← withMainContext do
      return VectorSimp.hasNestedSum (← instantiateMVars (← (← getMainGoal).getType))
    if nested then
      -- Coercion bookkeeping is allowed, but neither sum expansion nor
      -- numerical evaluation may erase a nested summation operation.
      let represent ← `(tactic|
        try simp only [
          VectorSimp.sum_attach,
          Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply,
          smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_succ,
          $args,*])
      evalTactic represent
      allGoals (VectorSimp.simplifyCoordinates represent)
      return
    evalTactic (← `(tactic|
      try simp (disch := first | assumption | norm_num only) only [
        ↓VectorSimp.mem_span_finset_iff, VectorSimp.mem_span_finset_iff,
        VectorSimp.isLinearCombination_empty_iff,
        VectorSimp.isLinearCombination_singleton_iff,
        VectorSimp.isLinearCombination_pair_iff,
        LinearCombination,
        ↓VectorSimp.sum_attach, VectorSimp.sum_attach,
        ↓VectorSimp.sum_singleton_subtype, VectorSimp.sum_singleton_subtype,
        ↓VectorSimp.sum_pair_subtype_if, VectorSimp.sum_pair_subtype_if,
        ↓VectorSimp.sum_pair_subtype, VectorSimp.sum_pair_subtype,
        Finset.univ_eq_empty, Finset.sum_empty,
        Fin.sum_univ_one, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
        $args,*]))
    if (← getGoals).isEmpty then return
    let finish ← `(tactic|
      try norm_num only [
        Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply,
        Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
        Matrix.smul_apply, Matrix.zero_apply,
        smul_eq_mul, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_zero',
        Matrix.cons_val_succ, Matrix.cons_val_succ',
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.vecHead, Matrix.vecTail, Matrix.vecCons_inj,
        ite_true, ite_false, and_true, true_and, and_false, false_and,
        zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one,
        sub_self, sub_zero, zero_sub, neg_zero, $args,*])
    evalTactic finish
    allGoals (VectorSimp.simplifyCoordinates finish)

end
