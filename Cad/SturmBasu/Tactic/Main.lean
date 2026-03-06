import Mathlib
import Lean.Elab.Tactic.Basic
import Qq

import CompPoly
import Cad.AlgebraicNumbers.Defs

open Qq Lean Elab Tactic ToExpr
open AlgebraicNumber

-- A tactic for comparing the projection of two algebraic numbers into the reals
section CmpAlg

open CompPoly

def nativeDecide (p: Q(Prop)) : MetaM Q($p) := do
  let hp : Q(Decidable $p) ← Meta.synthInstance q(Decidable $p)
  let auxDeclName ← mkNativeAuxDecl `_nativeUnivNl q(Bool) q(decide $p)
  let b : Q(Bool) := .const auxDeclName []
  return .app q(@of_decide_eq_true $p $hp) (.app q(Lean.ofReduceBool $b true) q(Eq.refl true))
where
  mkNativeAuxDecl (baseName : Name) (type value : Expr) : MetaM Name := do
    let auxName ← Lean.mkAuxDeclName baseName
    let decl := Declaration.defnDecl {
      name := auxName, levelParams := [], type, value
      hints := .abbrev
      safety := .safe
    }
    addAndCompile decl
    pure auxName

syntax (name := cmp_alg) "cmp_alg" term "," term "," term "," term : tactic

partial def gen_toReal_lt (a b : Q(Raw)) (ha : Q(AlgebraicNumber.Raw.wellDefined $a)) (hb : Q(AlgebraicNumber.Raw.wellDefined $b)) : MetaM Expr := do
  let goal ← Meta.mkAppM `LT.lt #[a, b]
  let h ← nativeDecide goal
  try
    -- checks if nativeDecide was successful
    withOptions (Elab.async.set · false) do
      let _ ← Meta.mkAuxLemma [] goal h
      Meta.mkAppM `AlgebraicNumber.lt_toReal #[a,b,ha,hb,h]
  catch _ =>
    let a' := mkApp (.const ``Raw.refine []) a
    let b' := mkApp (.const ``Raw.refine []) b
    let ha' := mkApp (mkApp (.const ``refine_wellDefined []) a) ha
    let hb' := mkApp (mkApp (.const ``refine_wellDefined []) b) hb
    let sub ← gen_toReal_lt a' b' ha' hb'
    Meta.mkAppM ``refine_lt_toReal #[a,b,sub]

@[tactic cmp_alg] def evalCmp_alg : Tactic := fun stx => withMainContext do
  let a : Q(Raw) ← elabTerm stx[1] none
  let b : Q(Raw) ← elabTerm stx[3] none
  -- TODO: infer these automatically via Sturm's theorem
  let ha : Q(AlgebraicNumber.Raw.wellDefined $a) ← elabTerm stx[5] none
  let hb : Q(AlgebraicNumber.Raw.wellDefined $b) ← elabTerm stx[7] none
  let mv ← gen_toReal_lt a b ha hb
  let mainMv ← getMainGoal
  let ra : Q(Real) := q(Raw.toReal $a)
  let rb : Q(Real) := q(Raw.toReal $b)
  let g ← Meta.mkAppM `LT.lt #[ra, rb]
  let (fv_decomp, mainMv) ← MVarId.intro1P $ ← mainMv.assert (Name.mkSimple "foo") g mv
  replaceMainGoal [mainMv]

syntax (name := cmp_alg_list) "cmp_alg_list" ("[" term,* "]") ("[" term,* "]") : tactic

@[tactic cmp_alg_list] def evalCmp_alg_list : Tactic := fun stx => withMainContext do
  sorry

def a : Raw := ⟨CPolynomial.X, -500, 500, by native_decide⟩ -- 0
def b : Raw := ⟨CPolynomial.X - CPolynomial.C 3, -500, 500, by native_decide⟩ -- 3

axiom wd_a : a.wellDefined
axiom wd_b : b.wellDefined

example : a.toReal < b.toReal := by
  cmp_alg a, b, wd_a, wd_b
  exact foo

end CmpAlg

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

def gen_intervals' (roots : List Real) (first : Bool) : List (Sum Real (Option Real × Option Real)) :=
  match roots with
  | [] => []
  | [x] =>
    if first then [.inr (none, some x), .inl x, .inr (some x, none)]
    else [.inl x,  .inr (some x, none)]
  | x :: y :: t =>
    if first then
      .inr (none, some x) :: .inl x :: .inr (some x, some y) :: gen_intervals' (y :: t) false
    else
      .inl x :: .inr (some x, some y) :: gen_intervals' (y :: t) false

def gen_intervals (roots : List Real) : List (Sum Real (Option Real × Option Real)) := gen_intervals' roots true

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
    (∃ x, P x) → (∃ p : Set Real, p ∈ decomp l sl ∧ (∃ x : Real, x ∈ p ∧ P x)) := by
  rintro ⟨x, hx⟩
  obtain ⟨p, hp⟩  := L x l sl hl
  tauto

def runGrind (mv : MVarId) : MetaM Unit := do
  let params ← Meta.Grind.mkDefaultParams {}
  let _ ← Meta.Grind.main mv params

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
def solveCase (mv : MVarId) (inter : Sum Real (Option Real × Option Real)) : MetaM (Option MVarId) := do
  let ty ← mv.getType
  logInfo m!"ty = {ty}"
  match inter with
  | .inl x =>
    logInfo "inl"
    return mv
  | .inr (ol, or) =>
    logInfo "inr"
    return mv

syntax (name := univ_cad) "univ_cad" term "," ("[" term,* "]")? : tactic

-- Nat for now because its easier, later we have to instrument lean-smt to parse algebraic numbers to real numbers
def parseUnivCad : Syntax → TacticM (List Nat)
  | `(tactic| univ_cad $_, [ $[$hs],* ]) => hs.toList.mapM stxToNat >>= λ li => return li
  | _ => throwError "[univ_cad]: wrong usage"

@[tactic univ_cad] def evalUnivCad : Tactic := fun stx => withMainContext do
  let h ← elabTerm stx[1] none -- exists x, F x
  let roots ← parseUnivCad stx
  let roots' := roots.map f
  let inters := gen_intervals roots'
  let e_roots' := toExpr roots
  let e_roots : Q(List Real) ← Meta.mkAppM ``List.map #[Expr.const `f [], e_roots']
  let decompPf ← getDecompPf e_roots h
  let decompType ← Meta.inferType decompPf
  let mainMv ← getMainGoal
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
    let disjsAndInters := disjunctsToFalseMvs.zip inters
    let unsolvedMvs ← disjsAndInters.mapM (fun (e, i) => solveCase e.mvarId! i)
    let unsolvedMvs := unsolvedMvs.foldr (fun o acc => match o with | some x => x :: acc | _ => acc) []
    replaceMainGoal unsolvedMvs

example (h : ∃ (x : ℝ), x + 3 < 0 ∧ (1/2) * x ^ 2 - 1 < 0) : False := by
  univ_cad h, [1, 3, 4]
  · admit
  · admit
  · admit
  · admit
  · admit
  · admit
  · admit
