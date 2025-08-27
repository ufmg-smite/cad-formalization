import Mathlib

open Polynomial
open Set
open Filter
open Classical

noncomputable def polyRemSeq (f g : Polynomial ℝ) (h : g.natDegree ≠ 0) : List (Polynomial ℝ) :=
  go f g [f] h
where
  go (h₀ h₁ : Polynomial ℝ) (acc : List (Polynomial ℝ)) (j : h₁.natDegree ≠ 0): List (Polynomial ℝ) :=
    if h₁ = 0 then acc
    else
      let r := - h₀ % h₁
      if k : r.natDegree = 0 then acc ++ [h₁]
      else
        go h₁ r (acc ++ [h₁]) k
  termination_by h₁.natDegree
  decreasing_by
    apply Polynomial.natDegree_mod_lt
    exact j

noncomputable def sturmSeq (f g : Polynomial ℝ) : List (Polynomial ℝ) :=
  if h : g.natDegree = 0 then
    [f, g]
  else
    let aux := polyRemSeq f g h
    let gcdf := aux[aux.length - 2]! % aux[aux.length - 1]!
    if  gcdf = 0 then
      aux
    else
      aux ++ [gcdf]

-- Considerando só os não nulos
noncomputable def seqVar : List ℝ → ℕ
| [] => 0
| _::[] => 0
| a::(b::as) =>
  if b == 0 then
    seqVar (a::as)
  else if a * b < 0 then
    1 + seqVar (b::as)
  else
    seqVar (b::as)

noncomputable def seqEval (k : ℝ) : List (Polynomial ℝ) → List ℝ
| [] => []
| a::as => [eval k a]++(seqEval k as)

noncomputable def sgn (k : ℝ) : ℤ  :=
  if k > 0 then 1
  else if k = 0 then 0
  else -1

noncomputable def rootsInInterval (f : Polynomial ℝ) (a b : ℝ) : Finset ℝ :=
  f.roots.toFinset.filter (fun x => x ∈ Ioo a b)

noncomputable def c_pos (f g : Polynomial ℝ) (a b : ℝ) : ℕ :=
  let k : Finset ℝ := rootsInInterval f a b
  (k.filter (fun x => eval x g > 0)).card

noncomputable def c_neg (f g : Polynomial ℝ) (a b : ℝ) : ℕ :=
  let k : Finset ℝ := (f.roots.toFinset).filter (fun x => x ∈ Ioo a b)
  (k.filter (fun x => eval x g < 0)).card

def rightNear (x : ℝ) : Filter ℝ := nhdsWithin x (Set.Ioi x)

-- P(x + eps) > 0 for all sufficiently small eps
def sign_r_pos (x : ℝ) (p : Polynomial ℝ) : Prop :=
  Filter.Eventually (fun a => eval a p > 0) (rightNear x)

-- 1 if p / q goes from -inf to +inf in x, -1 if goes from +inf to -inf
-- 0 otherwise
noncomputable def jump_val (p q : Polynomial ℝ) (x : ℝ) : ℤ :=
  let oddOrder := Odd ((rootMultiplicity x p : ℤ) - rootMultiplicity x q)
  if p ≠ 0 ∧ q ≠ 0 ∧ oddOrder then
    -- note that p * q > 0 is the same as p / q > 0
    if sign_r_pos x (p * q) then 1 else -1
  else 0

-- Corresponde a Ind(P/Q; a, b)
noncomputable def cauchyIndex (p q : Polynomial ℝ) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval p a b, jump_val p q x

theorem Sturm (f g : Polynomial ℝ) (a b : ℝ) (h : a < b) :
      seqVar (seqEval a (sturmSeq f (derivative f * g))) - seqVar (seqEval b (sturmSeq f (derivative f * g)))
      = c_pos f g a b - c_neg f g a b
      := by
  sorry
