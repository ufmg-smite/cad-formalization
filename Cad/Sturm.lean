import Mathlib

open Polynomial
open Set

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

noncomputable def sturmSeqCompressed (f g : Polynomial ℝ) : List (Polynomial ℝ) :=
  let k := sturmSeq f g
  go k
where
  go : List (Polynomial ℝ) → List (Polynomial ℝ)
  | [] => []
  | a::as => [a/as[as.length - 1]!]++go as


theorem lastIsGCD (f g : Polynomial ℝ) : (sturmSeq f g)[(sturmSeq f g).length - 1]! = (gcd f g) := by
  sorry

theorem disjointRoots (f g : Polynomial ℝ) (h := sturmSeqCompressed f g) (i : Fin (h.length)) : ∃ c, eval c h[i]! = 0 → (∃ j, eval c h[j]! = 0 → j = i):= by
  sorry

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

theorem L8_4_1 (f g : Polynomial ℝ) (a b : ℝ) :
      ¬(∃ k, k ∈ Icc a b ∧ eval k f = 0)
      → seqVar (seqEval a (sturmSeq f g)) - seqVar (seqEval b (sturmSeq f g)) = 0
      := by
  sorry

theorem L8_4_2 (f g : Polynomial ℝ) (a b : ℝ) :
      (∃! k, k ∈ Icc a b ∧ eval k f = 0)
      → seqVar (seqEval a (sturmSeq f (derivative f * g))) - seqVar (seqEval b (sturmSeq f (derivative f * g))) = sgn (eval k g)
      := by
  sorry

noncomputable def c_pos (f g : Polynomial ℝ) (a b : ℝ) : ℕ :=
  let k : Finset ℝ := (f.roots.toFinset).filter (fun x => x ∈ Ioo a b)
  (k.filter (fun x => eval x g > 0)).card

noncomputable def c_neg (f g : Polynomial ℝ) (a b : ℝ) : ℕ :=
  let k : Finset ℝ := (f.roots.toFinset).filter (fun x => x ∈ Ioo a b)
  (k.filter (fun x => eval x g < 0)).card

theorem Sturm (f g : Polynomial ℝ) (a b : ℝ) (h : a < b) :
      seqVar (seqEval a (sturmSeq f (derivative f * g))) - seqVar (seqEval b (sturmSeq f (derivative f * g)))
      = c_pos f g a b - c_neg f g a b
      := by
  sorry
