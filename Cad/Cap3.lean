import Mathlib

namespace SemiAlgebraic

open Classical

def R (k : Nat) : Type := Fin k → ℝ

def Roots {k : Nat} (P: MvPolynomial (Fin k) ℝ) : Set (R k) := fun f => P.eval f = 0

def Pos {k : Nat} (Qs : Finset (MvPolynomial (Fin k) ℝ)) : Set (R k) :=
  fun f => ∀ Q ∈ Qs , Q.eval f > 0

inductive BasicSA (k : Nat) where
  | mk : MvPolynomial (Fin k) ℝ → Finset (MvPolynomial (Fin k) ℝ) → BasicSA k

def interpBasicSA {k : Nat} (b : BasicSA k) : Set (R k) :=
  match b with
  | .mk P Qs =>
    let rP := Roots P
    let pQ := Pos Qs
    rP ∩ pQ

-- Semialgebraic sets
def SA {k : Nat} (b : Finset (BasicSA k)) : Set (R k) :=
  let bs : Finset (Set (R k)) := b.image interpBasicSA
  Finset.fold (fun x1 x2 => x1 ∪ x2) {} id bs

def proj {k : Nat} (a : Set (R (k + 1))) : Set (R k) :=
  a.image (fun z: (Fin (k + 1) → ℝ) => (fun x: Fin k => z x))

def IsSemiAlgebraic {k : Nat} (s : Set (R k)) : Prop := ∃ (b : Finset (BasicSA k)) , SA b = s

def relToSet {a b : Type} : Rel a b → Set (a × b) := fun R => { r: a × b | R r.1 r.2 }

def castProd {n m : Nat} : R n × R m → R (n + m) :=
  fun ⟨r₁, r₂⟩ => fun r => if h: r < n then r₁ ⟨r, h⟩ else r₂ ⟨r - n, by omega⟩

def castSetProd {n m : Nat} : Set (R n × R m) → Set (R (n + m)) := fun s: Set (R n × R m) =>
  s.image castProd

def IsSemiAlgebraicFunction (n m : Nat) (f : R n -> R m) : Prop :=
  let s: Set (R n × R m) := relToSet f.graph
  IsSemiAlgebraic (castSetProd s)

end SemiAlgebraic
