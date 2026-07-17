import Lean
import Cad.AlgebraicNumbers.AlgNum
import Cad.AlgebraicNumbers.DeriveWellDefined

open Lean Qq

open AlgebraicNumber CompPoly CPolynomial

inductive RootVal where
  | rat (e : Expr) (v : Rat) : RootVal
  -- NOTE: They do NOT represent the same thing; the Expr is an `AlgNum`
  -- and raw is the underlying `Raw`. Unfortunately we can't generate
  -- the `AlgNum` at compile time, so we can't store it here. But it
  -- is very convenient to have the `Expr` stored as the full `AlgNum`.
  | alg (e : Q(AlgNum)) (raw : Raw) : RootVal
  deriving Inhabited

def RootVal.expr : RootVal → Expr
  | .rat e _ => e
  | .alg e _ => e

def RootVal.isAlgNum : RootVal → Bool
  | .rat .. => false
  | .alg .. => true

def RootVal.ofExpr (e : Expr) : MetaM RootVal := do
  let t ← Meta.inferType e
  if t == .const ``Rat [] then
    let v : Rat ← unsafe Meta.evalExpr Rat q(Rat) e
    return .rat e v
  else if t == .const ``AlgNum [] then
    let e : Q(AlgNum) := e
    let raw : AlgebraicNumber.Raw ← unsafe Meta.evalExpr AlgebraicNumber.Raw
      q(AlgebraicNumber.Raw) q(Subtype.val $e)
    return .alg e raw
  else
    throwError "[RootVal.ofExpr]: expected Rat or AlgNum, got {t}"

def RootVal.toReal : RootVal → MetaM Expr
  | .rat e _ => let q : Q(Rat) := e; return q(ratToReal $q)
  | .alg e _ => Meta.mkAppM ``AlgNum.toReal #[e]

instance : ToString RootVal where
  toString rv :=
    match rv with
    | .rat _ r => "Rat < " ++ toString r ++ " >"
    | .alg _ a => "Alg < " ++ toString a ++ " >"
