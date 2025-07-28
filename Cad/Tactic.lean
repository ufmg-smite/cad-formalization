import Lean
import Qq
import Cad.DefinitionsOne

open Qq

open Definitions Lean Elab.Tactic Meta

namespace Tactic
namespace Definitions

-- Obtém a representação em SMT-LIB para um monômio. O resultado sempre tem parêntesis em volta.
def MyMonomial.toSMTLib (m : MyMonomial) : String :=
  let ⟨coef, exp⟩ := m
  let inner :=
    if exp = 0 then "1"
    else if exp > 1 then "^ x " ++ (toString exp)
    else "x"
  let outer :=
    if coef = 0 then ""
    else if coef = 1 then "(" ++ inner ++  ")"
    else "(* " ++ toString coef ++ " " ++ inner ++ ")"
  outer

-- Obtém a representação em SMT-LIB para um polinômio. O resultado sempre tem parêntesis em volta.
def MyPolynomial.toSMTLib (p : MyPolynomial) : String :=
  let ms := List.map MyMonomial.toSMTLib p
  -- A função no List.foldl vai reverter a ordem dos monômios, então revertemos antes para não
  -- alterar a ordem que eles são passados.
  match List.reverse ms with
  | [] => ""
  | hd :: tl =>
    List.foldl (fun acc m => "(+ " ++ m ++ " " ++ acc ++ ")") hd tl

-- Cria um assert em SMT-LIB afirmando que o polinômio é igual a 0.
def MyPolynomial.assert (p : MyPolynomial) : String :=
  "(assert (= " ++ (MyPolynomial.toSMTLib p) ++ " 0))"

def f (_cvc5Out : String) : Rat × Rat := (5/4, 3/2)

syntax (name := find_root) "find_root " term : tactic

open Mathlib.Meta.NormNum in
def normNum (mv : MVarId) : MetaM Unit := do
  if let some (_, mv) ← normNumAt mv (← Meta.Simp.mkContext) #[] true false then
    throwError "[norm_num]: could not prove {← mv.getType}"

def ratToExpr (r : Rat) : Expr :=
  let den_expr : Q(Nat) := Expr.lit (Literal.natVal r.den)
  if r.num ≥ 0 then
    let num_nat := Int.toNat r.num
    let num_expr : Q(Nat) := Expr.lit (Literal.natVal num_nat)
    q(($num_expr : Rat) / $den_expr)
  else
    let neg_num_nat := Int.toNat (-r.num)
    let neg_num_nat_expr : Q(Nat) := Expr.lit (Literal.natVal neg_num_nat)
    let num_expr : Q(Int) := q(-$neg_num_nat_expr)
    q(($num_expr : Rat) / $den_expr)

-- Falha se MyPolynomial não for fechado.
@[tactic find_root] unsafe def evalFindRoot : Tactic := fun stx => withMainContext do
  let t ← elabTerm stx[1] none
  let p ← evalExpr MyPolynomial (mkConst ``MyPolynomial) t
  let sa : IO.Process.SpawnArgs := { cmd := "/usr/bin/touch", args := #["/tmp/a.smt2"] }
  let _  ← IO.Process.output sa
  let fp := "/tmp/a.smt2"
  IO.FS.writeFile fp
    ("(set-logic QF_NRA)\n(declare-const x Real)\n" ++ (MyPolynomial.assert p) ++ "\n(check-sat)\n(get-model)\n")
  let sa : IO.Process.SpawnArgs := { cmd := "/usr/bin/cvc5", args := #["/tmp/a.smt2", "--produce-models"] }
  let ⟨sc, out, err⟩ ← IO.Process.output sa

  let (left, right) := f out
  let left_expr : Q(Rat) := ratToExpr left
  let right_expr : Q(Rat) := ratToExpr right
  let prop : Expr := q($left_expr ≤ $right_expr)
  let mv ← mkFreshExprMVar (some prop)
  normNum mv.mvarId!
  let main_mv ← getMainGoal
  let (_, mvar') ← MVarId.intro1P $ ← main_mv.assert `first_hyp prop mv
  replaceMainGoal [mvar']

  let t' : Q(MyPolynomial) := t
  let left' : Q(Rat) := left_expr
  let sec_hyp : Q(Prop) := q(evalPoly $t' $left' ≤ 0)
  let mv3 ← mkFreshExprMVar (some sec_hyp)
  let ctx ← Simp.mkContext
     (config := (← elabSimpConfig Syntax.missing (kind := SimpKind.simp)))
     (simpTheorems := #[← getSimpTheorems])
     (← getSimpCongrTheorems)

  let (mv?, _) ← simpTarget mv3.mvarId! ctx
  if let some mvSimp := mv? then normNum mvSimp
  let (_, mvar'') ← MVarId.intro1P $ ← mvar'.assert `second_hyp sec_hyp mv3
  replaceMainGoal [mvar'']


end Definitions
end Tactic

section Tests

open Tactic

def M2 : MyMonomial := { coef := 2, exp := 2 }
def P1 : MyPolynomial := [M]
def P2 : MyPolynomial := [M, M2]

@[simp]
def m1 : MyMonomial := { coef := 1, exp := 2 }
@[simp]
def m2 : MyMonomial := { coef := -2, exp := 0 }
@[simp]
def p := [m1, m2]

example : evalPoly p (-1) ≤ 0 := by
  simp

example : True := by
  have := exists_root_interval p (5/4 : ℝ) (3/2 : ℝ)
  have := this (by norm_num)
  have := this (by simp; norm_num)
  have := this (by simp [p, m1, m2]; norm_num)
  trivial

set_option linter.unusedTactic false
example : True := by
  find_root p
  admit

end Tests
