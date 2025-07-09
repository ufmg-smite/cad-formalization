import Lean
import Qq
import Cad.DefinitionsOne

open Qq

open Definitions Lean Elab.Tactic Meta

namespace Tactic
namespace Definitions

#check q(2)

syntax (name := cmdElabTerm) "#elab " term : command
open Lean.Elab Lean.Elab.Command in
@[command_elab cmdElabTerm] def evalCmdElabTerm : CommandElab
  | `(#elab $term) => withoutModifyingEnv $ runTermElabM fun _ => do
    let e ← Term.elabTerm term none
    logInfo m!"{e} ::: {repr e}"
  | _ => throwUnsupportedSyntax

#elab (3/4 : ℚ)


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

#check abs
variable (a : Int)

#check Int.toNat



open Mathlib.Meta.NormNum in
def normNum (mv : MVarId) : MetaM Unit := do
  if let some (_, mv) ← normNumAt mv (← Meta.Simp.mkContext) #[] true false then
    throwError "[norm_num]: could not prove {← mv.getType}"

-- Falha se MyPolynomial não for fechado.
@[tactic find_root] unsafe def evalFindRoot : Tactic := fun stx => withMainContext do
  let t ← elabTerm stx[1] none
  let p ← evalExpr MyPolynomial (mkConst ``MyPolynomial) t
  logInfo s!"{MyPolynomial.assert p}"
  let sa : IO.Process.SpawnArgs := { cmd := "/usr/bin/touch", args := #["/tmp/a.smt2"] }
  let _  ← IO.Process.output sa
  let fp := "/tmp/a.smt2"
  IO.FS.writeFile fp
    ("(set-logic QF_NRA)\n(declare-const x Real)\n" ++ (MyPolynomial.assert p) ++ "\n(check-sat)\n(get-model)\n")
  let sa : IO.Process.SpawnArgs := { cmd := "/usr/bin/cvc5", args := #["/tmp/a.smt2", "--produce-models"] }
  let ⟨sc, out, err⟩ ← IO.Process.output sa
  let (left, right) := f out
  let den: Nat := left.den
  let den_expr : Q(Nat) := Expr.lit (Literal.natVal den)
  if left.num ≥ 0 then
    let left_num_nat := Int.toNat left.num
    let num_expr : Q(Nat) := Expr.lit (Literal.natVal left_num_nat)
    let left_expr : Q(Rat) := q(($num_expr : Rat) / $den_expr)
    if right.num >= 0 then
      let den_right_expr : Q(Nat) := Expr.lit (Literal.natVal right.den)
      let num_right_expr : Q(Nat) := Expr.lit (Literal.natVal (Int.toNat right.num))
      let right_expr : Q(Rat) := q(($num_right_expr : Rat) / $den_right_expr)
      let prop : Expr := q($left_expr ≤ $right_expr)
      let mv ← mkFreshExprMVar (some prop)
      MVarId.withContext mv.mvarId! do
        normNum mv.mvarId!
        let main_mv ← getMainGoal
        let (_, mvar') ← MVarId.intro1P $ ← main_mv.assert Name.anonymous prop mv
        replaceMainGoal [mvar']
    else
      let neg_right_num_nat := Int.toNat (-right.num)
      let neg_num_right_expr : Q(Nat) := Expr.lit (Literal.natVal neg_right_num_nat)
      let num_right_expr : Q(Int) := q(-$neg_num_right_expr)
      let den_right_expr : Q(Nat) := Expr.lit (Literal.natVal right.den)
      let right_expr : Q(Rat) := q(($num_right_expr : Rat) / $den_right_expr)
      let prop : Expr := q($left_expr ≤ $right_expr)
      let mv ← mkFreshExprMVar (some prop)
      MVarId.withContext mv.mvarId! do
        normNum mv.mvarId!
        let main_mv ← getMainGoal
        let (_, mvar') ← MVarId.intro1P $ ← main_mv.assert Name.anonymous prop mv
        replaceMainGoal [mvar']
  else
    let neg_left_num_nat := Int.toNat (-left.num)
    let neg_left_num_expr : Q(Nat) := Expr.lit (Literal.natVal neg_left_num_nat)
    let num_left_expr : Q(Int) := q(-$neg_left_num_expr)
    let den_left_expr := Expr.lit (Literal.natVal left.den)
    sorry

  /- let sa : IO.Process.SpawnArgs := { cmd := "/usr/bin/cat", args := #["/home/tomaz/Desktop/a.smt2"] } -/
  /- let ⟨ec, out, err⟩  ← IO.Process.output sa -/
  /- logInfo s!"{out}" -/

end Definitions
end Tactic

section Tests

open Tactic

def M2 : MyMonomial := { coef := 2, exp := 2 }
def P1 : MyPolynomial := [M]
def P2 : MyPolynomial := [M, M2]

def m1 : MyMonomial := { coef := 1, exp := 2 }
def m2 : MyMonomial := { coef := -2, exp := 0 }
def p := [m1, m2]

example : True := by
  have := exists_root_interval p (5/4 : ℝ) (3/2 : ℝ)
  have := this (by norm_num)
  have := this (by simp [p, m1, m2]; norm_num)
  have := this (by simp; norm_num)
  sorry

set_option linter.unusedTactic false
example : True := by
  find_root p

  trivial

#eval M.toSMTLib
#eval M2.toSMTLib

#eval P.toSMTLib
#eval P2.toSMTLib

#eval P2.assert

end Tests
