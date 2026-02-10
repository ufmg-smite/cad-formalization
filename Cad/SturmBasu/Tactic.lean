import Mathlib
import Lean.Elab.Tactic.Basic
import Qq

open Qq
open Lean Elab Tactic

@[simp]
def decomp' (l : List ℝ) (sl : l.SortedLT) (first : Bool) : List (Set ℝ) :=
  match l with
  | [] => []
  | [x] =>
    if first then (fun y => y < x) :: (fun y => y = x) :: (fun y => y > x) :: []
    else (fun y => y = x) :: (fun y => y > x) :: []
  | x :: y :: t =>
    if first then
      (fun z => z < x) :: (fun z => z = x) :: (fun z => z > x ∧ z < y) :: decomp' (y :: t) (by grind) false
    else
      (fun z => z = x) :: (fun z => z > x ∧ z < y) :: decomp' (y :: t) (by grind) false

@[simp]
def decomp (l : List ℝ) (sl : l.SortedLT) : List (Set ℝ) := decomp' l sl true

@[simp]
def decomp'_merge (l : List ℝ) (sl : l.SortedLT) : Set ℝ := (decomp' l sl false).foldr (fun s acc => s ∪ acc) ∅

@[simp]
def decomp_merge (l : List ℝ) (sl : l.SortedLT) : Set ℝ := (decomp l sl).foldr (fun s acc => s ∪ acc) ∅

lemma decomp'_covers (hd : ℝ) (tl : List ℝ) (sl : (hd :: tl).SortedLT) :
    decomp'_merge (hd :: tl) sl = fun x => x ≥ hd := by
  cases tl
  next =>
    simp
    ext z
    constructor
    · intro h
      simp at h
      cases h
      next h =>
        have : z = hd := Real.ext_cauchy (congrArg Real.cauchy h)
        rw [this]
        have : hd ≤ hd := Std.IsPreorder.le_refl hd
        exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 => a_1) this
      next h =>
        have : hd < z := gt_iff_lt.mp h
        bound
    · intro h
      simp
      have : hd < z ∨ hd = z := Decidable.lt_or_eq_of_le h
      cases this
      next =>
        right
        tauto
      next =>
        left
        tauto
  next hd' tl' =>
    simp
    ext z
    constructor
    · intro H
      simp at H
      cases H
      next H1 =>
        have : z = hd := Real.ext_cauchy (congrArg Real.cauchy H1)
        rw [this]
        have : hd ≤ hd := Std.IsPreorder.le_refl hd
        exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 => a_1) this
      next H1 =>
        cases H1
        next H2 =>
          have : hd < z := gt_iff_lt.mp H2.1
          bound
        next H2 =>
          have := decomp'_covers hd' tl' (by grind)
          have := (Eq.to_iff (congrFun this z)).mp H2
          have foo : hd < hd' := by grind
          suffices hd ≤ z by finiteness
          linarith
    · intro H
      simp
      have : hd ≤ z := by finiteness
      have : hd < z ∨ hd = z := Decidable.lt_or_eq_of_le H
      cases this
      next H1 =>
        right
        cases lt_trichotomy z hd'
        next H2 =>
          left
          trivial
        next H2 =>
          right
          have := decomp'_covers hd' tl' (by grind)
          have := (Eq.to_iff (congrFun this z)).mpr (by grind)
          apply this
      next H1 =>
        left
        exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 => a_1) (Eq.symm H1)

lemma decomp_covers (l : List ℝ) (sl : l.SortedLT) (hl : l ≠ []) :
    decomp_merge l sl = (Set.univ : Set ℝ) :=
  match l with
  | [] => Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 => hl rfl
  | [x] => by
    simp
    ext z
    constructor
    · exact fun a => Set.mem_univ z
    · intro _
      simp
      cases lt_trichotomy z x
      next h =>
        left
        finiteness
      next h =>
        right
        cases h
        next h1 =>
          left
          finiteness
        next h1 =>
          right
          finiteness
  | x :: y :: t => by
    simp
    ext z
    constructor
    · exact fun a => Set.mem_univ z
    · intro _
      simp
      cases lt_trichotomy z x
      next h => tauto
      next h =>
        right
        cases h
        next h1 => exact Or.symm (Or.inr h1)
        next h1 =>
          right
          cases lt_trichotomy z y
          next h2 => tauto
          next h2 =>
            right
            have := decomp'_covers y t (by grind)
            have := (Eq.to_iff (congrFun this z)).mpr (by grind)
            apply this

lemma l1 (x : ℝ) (l : List (Set ℝ)) :
    (∀ p ∈ l, x ∉ p) → x ∉ l.foldr (fun s acc => s ∪ acc) ∅ := by
  intro h
  cases l
  next => simp
  next hd tl =>
    intro abs
    simp at abs
    cases abs
    next abs' =>
      have := h hd (by grind)
      exact this abs'
    next abs' =>
      have : ∀ p ∈ tl, x ∉ p := by grind
      have := l1 x tl this
      exact (iff_false_intro this).mp abs'

lemma L (x : ℝ) (l : List ℝ) (sl : l.SortedLT) (hl : l ≠ []) :
    ∃ p ∈ decomp l sl, x ∈ p := by
  by_contra! h
  have foo := decomp_covers l sl hl
  unfold decomp_merge at foo
  have := l1 x (decomp l sl) h
  simp_all only [ne_eq, decomp, Set.mem_univ, not_true_eq_false]

theorem t (P : ℝ → Prop) (l : List ℝ) (sl : l.SortedLT) (hl : l ≠ []) :
    (∃ x, P x) → (∃ p ∈ decomp l sl, (∃ x ∈ p, P x)) := by
  rintro ⟨x, hx⟩
  obtain ⟨p, hp⟩  := L x l sl hl
  tauto

syntax (name := foo) "foo" : tactic

@[tactic foo] def evalFoo : Tactic := fun _ => do
  let mv ← Tactic.getMainGoal
  mv.withContext fun _ => do
    let lctx ← getLCtx
    for ldecl in lctx do
      if ldecl.isImplementationDetail then
        continue
      let t := ldecl.type
      if let some ty ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
        match ty with
        | ~q(LT.lt (α := Real) $lhs $rhs) =>
          logInfo "is lt"
          logInfo m!"lhs = {lhs}"
          logInfo m!"rhs = {rhs}"
          logInfo m!"-----------------------------------"
        | _ => logInfo m!"isnt lt: {repr t}¬----------------------------------"

example (x : Real) : x > 0 → x < 0 → False := by
  intros h1 h2
  foo
  admit
