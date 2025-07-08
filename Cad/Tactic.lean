import Lean
import Cad.DefinitionsOne

open Definitions Lean Elab.Tactic Meta

namespace Tactic
namespace Definitions

-- Obtém a representação em SMT-LIB para um monômio. O resultado sempre tem parêntesis em volta.
def MyMonomial.toSMTLib (m : MyMonomial) : String :=
  let ⟨coef, exp⟩ := m
  let inner :=
    if exp > 1 then "(^ x " ++ (toString exp) ++ ")"
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

syntax (name := find_root) "find_root " term : tactic

-- Falha se MyPolynomial não for fechado.
@[tactic find_root] unsafe def evalFindRoot : Tactic := fun stx => withMainContext do
  let t ← elabTerm stx[1] none
  let p ← evalExpr MyPolynomial (mkConst ``MyPolynomial) t
  let sa : IO.Process.SpawnArgs := { cmd := "/usr/bin/cat", args := #["/home/tomaz/Desktop/a.smt2"] }
  let ⟨ec, out, err⟩  ← IO.Process.output sa
  logInfo s!"{out}"

end Definitions
end Tactic

section Tests

open Tactic

def M2 : MyMonomial := { coef := 2, exp := 2 }
def P1 : MyPolynomial := [M]
def P2 : MyPolynomial := [M, M2]

set_option linter.unusedTactic false
example : True := by
  find_root P2
  trivial

#eval M.toSMTLib
#eval M2.toSMTLib

#eval P.toSMTLib
#eval P2.toSMTLib

#eval P2.assert

end Tests
