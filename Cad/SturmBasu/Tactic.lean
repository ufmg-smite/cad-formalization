import Mathlib
import Lean.Elab.Tactic.Basic
import Qq

open Qq Lean Elab Tactic ToExpr

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
    simp only [decomp'_merge, decomp', Bool.false_eq_true, ↓reduceIte, gt_iff_lt, List.foldr_cons,
      List.foldr_nil, Set.union_empty, ge_iff_le]
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
      simp only [Set.mem_union]
      have : hd < z ∨ hd = z := Decidable.lt_or_eq_of_le h
      cases this
      next =>
        right
        tauto
      next =>
        left
        tauto
  next hd' tl' =>
    simp only [decomp'_merge, decomp', Bool.false_eq_true, ↓reduceIte, gt_iff_lt, List.foldr_cons,
      ge_iff_le]
    ext z
    constructor
    · intro H
      simp only [Set.mem_union] at H
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
      simp only [Set.mem_union]
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

theorem t {P : ℝ → Prop} (l : List ℝ) (sl : l.SortedLT) (hl : l ≠ []) :
    (∃ x, P x) → (∃ p ∈ decomp l sl, (∃ x ∈ p, P x)) := by
  rintro ⟨x, hx⟩
  obtain ⟨p, hp⟩  := L x l sl hl
  tauto

syntax (name := univ_cad) "univ_cad" term "," ("[" term,* "]")? : tactic

def getNatLit? : Expr → Option Nat
| .app (.app _ (.lit (.natVal x))) _ => some x
| _ => none

@[grind, simp]
def f (x : Nat) : Real := x

def stxToNat (h : Term) : TacticM Nat := do
  let expr ← elabTerm h.raw none
  match getNatLit? expr with
  | some i => pure i
  | none   => throwError "getNatLit? failed"

-- Nat for now because its easier, later we have to instrument lean-smt to parse algebraic numbers to real numbers
def parseUnivCad : Syntax → TacticM (List Nat)
  | `(tactic| univ_cad $_, [ $[$hs],* ]) => hs.toList.mapM stxToNat >>= λ li => return li
  | _ => throwError "[univ_cad]: wrong usage"

def runGrind (mv : MVarId) : MetaM Unit := do
  let params ← Meta.Grind.mkDefaultParams {}
  let _ ← Meta.Grind.main mv params

-- given the list of roots and a proof that `exists (x : ℝ), P x` produces a proof
-- that `∃ p ∈ decomp roots, ∃ x ∈ p, P x`, where `decomp roots` is the decomposition
-- of the real line into intervals separated at the roots.
def getDecompPf (roots : Q(List Real)) (h : Expr) : MetaM Expr := do
  let t ← Meta.mkAppM `List.SortedLT #[roots]
  let roots_sorted_pf ← Meta.mkFreshExprMVar t
  runGrind roots_sorted_pf.mvarId!
  let roots_not_empty : Q(Prop) := q($roots ≠ [])
  let roots_not_empty_pf ← Meta.mkFreshExprMVar roots_not_empty
  runGrind roots_not_empty_pf.mvarId!
  Meta.mkAppM ``t #[roots, roots_sorted_pf, roots_not_empty_pf, h]

def collectDisjuncts (e: Expr) : List Expr :=
  match e with
  | .app (.app (.const `Or ..) lhs) rhs =>
    lhs :: collectDisjuncts rhs
  | _ => [e]

def go (imps: List Expr) (or_pf: Expr) : MetaM Expr :=
  match imps with
  | [] => throwError ""
  | [e] => return e
  | [e1, e2] => Meta.mkAppM `Or.elim #[or_pf, e1, e2]
  | e :: t => do
    let or_ty ← Meta.inferType or_pf
    match or_ty with
    | .app (.app (.const `Or ..) _) B =>
      Meta.withLocalDeclD .anonymous B fun h => do
        let rhs ← go t h
        let rhs_lam ← Meta.mkLambdaFVars #[h] rhs
        Meta.mkAppM `Or.elim #[or_pf, e, rhs_lam]
    | _ => throwError ""

-- Solves one of the intervals for univ_cad. Returns `some mv` if it is not supported yet
def solveCase (mv : MVarId) : Option MVarId := some mv

@[tactic univ_cad] def evalUnivCad : Tactic := fun stx => withMainContext do
  let h ← elabTerm stx[1] none -- exists x, F x
  let roots ← parseUnivCad stx
  let e_roots' := toExpr roots
  let e_roots : Q(List Real) ← Meta.mkAppM ``List.map #[Expr.const `f [], e_roots']
  let decompPf ← getDecompPf e_roots h
  let decompType ← Meta.inferType decompPf
  let mainMv ← Tactic.getMainGoal
  let (fv_decomp, mainMv) ← MVarId.intro1P $ ← mainMv.assert .anonymous decompType decompPf
  let ctx ← Meta.Simp.Context.mkDefault
  -- simp on the decomp hypothesis so it becomes a finite disjunction instead of an existential
  let (some (fv_decomp, mainMv), _) ← Lean.Meta.simpLocalDecl mainMv fv_decomp ctx | throwError "impossible"
  mainMv.withContext do
    let t ← fv_decomp.getType
    let disjuncts := collectDisjuncts t
    let disjunctsToFalse ← disjuncts.mapM (mkArrow · (.const `False []))
    let disjunctsToFalseMvs ← disjunctsToFalse.mapM (fun e => Meta.mkFreshExprMVar e)
    let answer ← go disjunctsToFalseMvs (.fvar fv_decomp)
    mainMv.assign answer

    let unsolvedMvs := disjunctsToFalseMvs.map (fun e => solveCase e.mvarId!)
    let unsolvedMvs := unsolvedMvs.foldr (fun o acc => match o with | some x => x :: acc | _ => acc) []
    replaceMainGoal unsolvedMvs

example (h : ∃ (x : ℝ), x + 3 < 0 ∧ (1/2) * x ^ 2 - 1 < 0) : False := by
  univ_cad h, [1]
  · admit
  · admit
  · admit

/- syntax (name := cmdElabTerm) "#elab " term : command -/
/- open Lean.Elab Lean.Elab.Command in -/
/- @[command_elab cmdElabTerm] def evalCmdElabTerm : CommandElab -/
/-   | `(#elab $term) => withoutModifyingEnv $ runTermElabM fun _ => do -/
/-     let e ← Term.elabTerm term none -/
/-     logInfo m!"{e} ::: {repr e}" -/
/-   | _ => throwUnsupportedSyntax -/
