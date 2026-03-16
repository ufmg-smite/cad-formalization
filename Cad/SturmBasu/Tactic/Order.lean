import Mathlib
import Lean.Elab.Tactic.Basic
import Qq

import CompPoly
import Cad.AlgebraicNumbers.Defs

open Qq Lean Elab Tactic ToExpr Meta
open AlgebraicNumber
open CompPoly

-- evalExpr?
-- it should be possible just with refl, create a minimum example and ask on zulip
-- c.f. https://github.com/Verified-zkEVM/CompPoly/issues/140
def nativeDecide (p: Q(Prop)) : MetaM Q($p) := do
  let hp : Q(Decidable $p) ← synthInstance q(Decidable $p)
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
  let goal ← mkAppM `LT.lt #[a, b]
  let h ← nativeDecide goal
  try
    -- checks if nativeDecide was successful
    withOptions (Elab.async.set · false) do
      let _ ← mkAuxLemma [] goal h
      mkAppM `AlgebraicNumber.lt_toReal #[a,b,ha,hb,h]
  catch _ =>
    let a' := mkApp (.const ``Raw.refine []) a
    let b' := mkApp (.const ``Raw.refine []) b
    let ha' := mkApp (mkApp (.const ``refine_wellDefined []) a) ha
    let hb' := mkApp (mkApp (.const ``refine_wellDefined []) b) hb
    let sub ← gen_toReal_lt a' b' ha' hb'
    mkAppM ``refine_lt_toReal #[a,b,ha,hb,sub]

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
  let g ← mkAppM `LT.lt #[ra, rb]
  let (fv_decomp, mainMv) ← MVarId.intro1P $ ← mainMv.assert (Name.mkSimple "foo") g mv
  replaceMainGoal [mainMv]

def a : Raw := ⟨CPolynomial.X, -500, 500, by decide +kernel⟩ -- 0

def b : Raw := ⟨CPolynomial.X ^ 2 - CPolynomial.C 2, 0, 2, by decide +kernel⟩ -- sqrt 2
def c : Raw := ⟨CPolynomial.X - CPolynomial.C 3, -500, 500, by decide +kernel⟩ -- 3
def d : Raw := ⟨CPolynomial.X - CPolynomial.C 10, -500, 500, by decide +kernel⟩ -- 10


axiom wd_a : a.wellDefined
axiom wd_b : b.wellDefined
axiom wd_c : c.wellDefined
axiom wd_d : d.wellDefined

example : a.toReal < b.toReal := by
  cmp_alg a, b, wd_a, wd_b
  exact foo

syntax (name := cmp_alg_list) "cmp_alg_list" ("[" term,* "]") ("[" term,* "]") : tactic

def parse_cmp_alg_list : Syntax → TacticM (List Expr × List Expr)
  | `(tactic| cmp_alg_list [ $[$as],* ] [ $[$hs],* ] ) => do
    return Prod.mk (← as.toList.mapM (elabTerm · none)) (← hs.toList.mapM (elabTerm · none))
  | _ => throwError "[parse_cmp_alg_list]: impossible"

def toListExpr (α : Q(Type*)) (es : List Q($α)) : Q(List $α) :=
  match es with
  | [] => q(@List.nil $α)
  | hd :: tl =>
    let tl' : Q(List $α) := toListExpr α tl
    q($hd :: $tl')

def getPfs (as hs : List Expr) : MetaM (List Expr) :=
  match as, hs with
  | [], [] => return []
  | _ :: [], _ :: [] => return []
  | a1 :: a2 :: as, h1 :: h2 :: hs => do
    let p ← gen_toReal_lt a1 a2 h1 h2
    let rest ← getPfs (a2 :: as) (h2 :: hs)
    return p :: rest
  | _, _ => throwError "[getPfs]: impossible"

def runGrind' (mv : MVarId) (pfs : List Expr) : MetaM Unit := do
  let mut mv := mv
  for pf in pfs do
    let t ← inferType pf
    let (_, mv') ← MVarId.intro1P $ ← mv.assert .anonymous t pf
    mv := mv'
  let params ← Meta.Grind.mkDefaultParams {}
  let _ ← Meta.Grind.main mv params

-- given a list of algebraic numbers and a list of proofs that they are well
-- defined, tries to create a proof that the list is sorted (`List.SortedLT`)
def genPfSortedLT (as : List Q(Raw)) (hs : List Expr) : MetaM Expr := do
  let pfs ← getPfs as hs -- each pair is sorted
  let as' ← as.mapM (fun a => mkAppM `AlgebraicNumber.Raw.toReal #[a])
  let as := toListExpr q(Real) as'
  let goal ← mkAppM `List.SortedLT #[as]
  let mv ← mkFreshExprMVar goal
  runGrind' mv.mvarId! pfs
  return mv

@[tactic cmp_alg_list] def evalCmp_alg_list : Tactic := fun stx => withMainContext do
  let (as, hs) ← parse_cmp_alg_list stx
  let mv ← genPfSortedLT as hs
  let goal ← Meta.inferType mv
  let mainMv ← getMainGoal
  let (_, mainMv) ← MVarId.intro1P $ ← mainMv.assert (Name.mkSimple "bar") goal mv
  replaceMainGoal [mainMv]

example : [a.toReal, b.toReal, c.toReal, d.toReal].SortedLT := by
  cmp_alg_list [a, b, c, d] [wd_a, wd_b, wd_c, wd_d]
  exact bar
