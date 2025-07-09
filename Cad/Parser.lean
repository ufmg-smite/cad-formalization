import Std
import Init.Data.String.Basic
import Mathlib
open Std

def MatchStrWithRat (num : String) : ℚ :=
  let (isNegative, cleanNum) := if num.startsWith "-" then (true, num.drop 1) else (false, num)
  let result : ℚ :=
    if cleanNum.contains '/' then
      let parts := cleanNum.splitOn "/"
      let p := parts[0]!.toNat?
      let q := parts[1]!.toNat?
      match p, q with
      | some p', some q' => if q' ≠ 0 then p'/q' else 0
      | _, _ => 0
    else if cleanNum.contains '.' then
      let parts := cleanNum.splitOn "."
      if parts[1]! == "0" then
        match parts[0]!.toNat? with
        | some n => n
        | none => 0
      else
        let m := 10 ^ parts[1]!.length
        let combined := parts[0]! ++ parts[1]!
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
      let k := (aux.drop 3).trim
      let g := k.splitOn ")"
      s!"-{g[0]!}"
    else
      let closer := aux.splitOn ")"
      closer[0]!.trim
  else
    if aux.contains '-' then
      let k := (aux.drop 6).splitOn ")"
      "-"++k[0]!.trim++"/"++k[1]!.trim
    else
      let k := (aux.drop 2).splitOn ")"
      let aux2 := k[0]!.splitOn " "
      aux2[1]!++"/"++aux2[2]!

def Case2NumbersString (s : String) : String×String :=
  let aux := s.splitOn ","
  let lastnumstr := aux[2]!.splitOn ")"
  let k := aux[1]!.drop 2
  (k,lastnumstr[0]!.trim)

def GetInterval (s : String) : ℚ × ℚ :=
  let k := s.splitOn "real_algebraic_number"
  if k.length == 1 then
    let ans := MatchStrWithRat (Case1NumberString s)
    (ans,ans)
  else
    let aux := Case2NumbersString s
    let a := aux.fst
    let b := aux.snd
    (MatchStrWithRat a, MatchStrWithRat b)


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


#eval GetInterval case1_1 -- 1.0 (ok)
#eval GetInterval case1_2 -- 1/720 (ok)
#eval GetInterval case1_3 -- -1/2 (ok)
#eval GetInterval case1_4 -- -3.0 (ok)

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

#eval GetInterval case2_1 -- (5/4, 3/2) (ok)
#eval GetInterval case2_2 -- (12, 49/4) (ok)
#eval GetInterval case2_3 -- (-3/2, -5/4) (ok)
