import Std
import Init.Data.String.Basic
import Mathlib
import Cad.DefinitionsOne

open Std
open Definitions


def MatchStrWithRat (num : String) : ℚ :=
  let (isNegative, cleanNum) := if num.startsWith "-" then (true, num.drop 1) else (false, num)
  let result : ℚ :=
    if cleanNum.contains '/' then
      let parts := (cleanNum.split "/").toList
      let a := parts[0]!
      let b := parts[1]!
      let p := a.toNat?
      let q := b.toNat?
      match p, q with
      | some p', some q' => if q' ≠ 0 then p'/q' else 0
      | _, _ => 0
    else if cleanNum.contains '.' then
      let parts := (cleanNum.split ".").toList
      if parts[1]! == "0" then
        match parts[0]!.toNat? with
        | some n => n
        | none => 0
      else
        let m := 10 ^ parts[1]!.length
        let combined : String := parts[0]!.toString++parts[1]!.toString
        match combined.toNat? with
        | some n => n/m
        | none => 0
    else
      match cleanNum.toNat? with
      | some n => n
      | none => 0
  if isNegative then -result else result

def Case1NumberString (s : String) : String :=
  let aux := (s.splitOn "Real").getLast!
  if aux.contains '.' then
    if aux.contains '-' then
      let k := ((aux.drop 3).trim).toString
      let g := k.splitOn ")"
      s!"-{g[0]!}"
    else
      let closer := aux.splitOn ")"
      closer[0]!.trim
  else
    if aux.contains '-' then
      let k := (aux.drop 6).toString.splitOn ")"
      "-"++k[0]!.trim++"/"++k[1]!.trim
    else
      let k := (aux.drop 2).toString.splitOn ")"
      let aux2 := k[0]!.splitOn " "
      aux2[1]!++"/"++aux2[2]!

def Case2NumbersString (s : String) : String×String :=
  let aux := s.splitOn ","
  let lastnumstr := aux[2]!.splitOn ")"
  let k := (aux[1]!.drop 2).toString
  (k,lastnumstr[0]!.trim)

def GetPolyAux : List String → MyPolynomial
| [] => []
| p::ps =>
  let k := p.splitOn "x"
  if k.length == 1 then
    MyMonomial.mk (MatchStrWithRat p) 0::GetPolyAux ps
  else
    let coef := if k[0]!.contains "*" then MatchStrWithRat (k[0]!.splitOn "*")[0]! else 1
    let exp := if k[1]!.contains "^" then (k[1]!.splitOn "^")[0]!.toNat! else 1
    MyMonomial.mk coef exp::GetPolyAux ps

#eval ("pr".splitOn "p")--.length

def GetPolyFromStr (s : String) : MyPolynomial :=
  let k := ((s.splitOn ",")[0]!.drop 1).toString
  GetPolyAux (k.splitOn "+")

def GetIntervalAndPoly (s : String) : ℚ × ℚ × MyPolynomial :=
  let k := s.splitOn "real_algebraic_number"
  if k.length == 1 then
    let ans := MatchStrWithRat (Case1NumberString s)
    (ans, ans, [])
  else
    let aux := Case2NumbersString s
    let a := aux.fst
    let b := aux.snd
    let p := GetPolyFromStr k[1]!
    (MatchStrWithRat a, MatchStrWithRat b, p)


-- Testando pra ver se está tudo ok
def case1_1 : String := "sat
  (
  (define-fun x () Real 1.0)
  )"

def case1_2 : String := "sat
  (
  (define-fun x () Real (/ 1 720))
  )"

def case1_3 := "sat
(
(define-fun x () Real (/ (- 1) 2))
)
"

def case1_4 := "sat
  (
  (define-fun x () Real (- 3.0))
  )"


#eval GetIntervalAndPoly case1_1 -- 1.0 (ok)
#eval GetIntervalAndPoly case1_2 -- 1/720 (ok)
#eval GetIntervalAndPoly case1_3 -- -1/2 (ok)
#eval GetIntervalAndPoly case1_4 -- -3.0 (ok)

def case2_1 : String := "sat
  (
  (define-fun x () Real (_ real_algebraic_number <1*x^2 + (-2), (5/4, 3/2)>))
  )"

def case2_2 : String := "sat
  (
  (define-fun x () Real (_ real_algebraic_number <1*x^3 + (-1775), (12, 49/4)>))
  )"

def case2_3 := "sat
  (
  (define-fun x () Real (_ real_algebraic_number <1*x^3 + 3, (-3/2, -5/4)>))
  )"

#eval GetIntervalAndPoly case2_1 -- (5/4, 3/2) (ok)
#eval GetIntervalAndPoly case2_2 -- (12, 49/4) (ok)
#eval GetIntervalAndPoly case2_3 -- (-3/2, -5/4) (ok)
