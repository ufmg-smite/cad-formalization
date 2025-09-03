import Mathlib

open Polynomial
open Set
open Filter
open Classical

noncomputable section

def polyRemSeq (f g : Polynomial ℝ) (h : g.natDegree ≠ 0) : List (Polynomial ℝ) :=
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

def sturmSeq (f g : Polynomial ℝ) : List (Polynomial ℝ) :=
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
def seqVar : List ℝ → ℕ
| [] => 0
| _::[] => 0
| a::(b::as) =>
  if b == 0 then
    seqVar (a::as)
  else if a * b < 0 then
    1 + seqVar (b::as)
  else
    seqVar (b::as)

def seqEval (k : ℝ) : List (Polynomial ℝ) → List ℝ
| [] => []
| a::as => [eval k a]++(seqEval k as)

def sgn (k : ℝ) : ℤ  :=
  if k > 0 then 1
  else if k = 0 then 0
  else -1

def rootsInInterval (f : Polynomial ℝ) (a b : ℝ) : Finset ℝ :=
  f.roots.toFinset.filter (fun x => x ∈ Ioo a b)

def c_pos (f g : Polynomial ℝ) (a b : ℝ) : ℕ :=
  let k : Finset ℝ := rootsInInterval f a b
  (k.filter (fun x => eval x g > 0)).card

def c_neg (f g : Polynomial ℝ) (a b : ℝ) : ℕ :=
  let k : Finset ℝ := rootsInInterval f a b
  (k.filter (fun x => eval x g < 0)).card

def tarskiQuery (f g : Polynomial ℝ) (a b : ℝ) : ℤ :=
  (c_pos f g a b : ℤ) - c_neg f g a b

def rightNear (x : ℝ) : Filter ℝ := nhdsWithin x (Set.Ioi x)

-- P(x + eps) > 0 for all sufficiently small eps
def sign_r_pos (x : ℝ) (p : Polynomial ℝ) : Prop :=
  Filter.Eventually (fun a => eval a p > 0) (rightNear x)

-- 1 if p / q goes from -inf to +inf in x, -1 if goes from +inf to -inf
-- 0 otherwise
def jump_val (p q : Polynomial ℝ) (x : ℝ) : ℤ :=
  let orderP : ℤ := rootMultiplicity x p
  let orderQ : ℤ := rootMultiplicity x q
  let oddOrder := Odd (orderP - orderQ)
  if p ≠ 0 ∧ q ≠ 0 ∧ oddOrder ∧ orderP > orderQ then
    -- note that p * q > 0 is the same as p / q > 0
    if sign_r_pos x (p * q) then 1 else -1
  else 0

-- Corresponde a Ind(Q/P; a, b)
def cauchyIndex (p q : Polynomial ℝ) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval p a b, jump_val p q x

lemma B_2_57 (p q : Polynomial ℝ) (a b : ℝ) :
    tarskiQuery p q a b = cauchyIndex p (derivative p * q) a b :=
  sorry

noncomputable def sigma (b : ℝ) (f : Polynomial ℝ) : ℤ :=
  sgn (eval b f)

theorem L_2_59_1 (a b : ℝ) (p q : Polynomial ℝ) (hprod : sigma b (p*q) * sigma a (p*q) = -1):
      ((∀ i : Fin (sturmSeq p q).length, eval a (sturmSeq p q)[i]! ≠ 0) ∧ ( ∀ i : Fin (sturmSeq p q).length, eval b (sturmSeq p q)[i]! ≠ 0))
      → (seqVar (seqEval a (sturmSeq p q)) - seqVar (seqEval b (sturmSeq p q)))
      =  sigma b (p*q) + seqVar (seqEval a (sturmSeq q (-p%q))) - seqVar (seqEval b (sturmSeq q (-p%q))):= by
  intro h; rcases h with ⟨ha, hb⟩
  have sigma_a_ne_zero : sigma a (p*q) ≠ 0 := by
    intro H
    have : sigma b (p*q) * 0 = -1 := by rw [H] at hprod; exact hprod
    simp at this
  have eval_a_ne_zero : eval a (p*q) ≠ 0 := by
    intro Heval
    have : sigma a (p*q) = 0 := by simp [sigma, sgn, Heval]
    exact (sigma_a_ne_zero this)
  have h1a : sigma a (p*q) = 1 ∨ sigma a (p*q) = -1 := by
    -- expandimos sigma/sgn e dividimos por casos: >0 ou <0 (não pode ser =0 por eval_a_ne_zero)
    rw[sigma, sgn]
    if hpos : eval a (p*q) > 0 then
      left; split_ifs; rfl
    else right; split_ifs; rfl
  if hsigmaa : sigma a (p*q) = -1 then
    have h2_1 : sigma b (p*q) = 1 := by
      rw [hsigmaa] at hprod
      simp at hprod; exact hprod

    have h2_2a : seqVar (seqEval a (sturmSeq p q))
      = 1 + seqVar (seqEval a (sturmSeq q (-p%q))) := by
      sorry
    have h2_2b : seqVar (seqEval b (sturmSeq p q))
      = seqVar (seqEval b (sturmSeq q (-p%q))) := by
      sorry

    rw[h2_2a, h2_2b, h2_1]; simp
  else
    have hsa_pos : sigma a (p*q) = 1 := by
      have : sigma a (p*q) = -1 → False := by
        intro H; apply (by simp [H] at hsigmaa) -- hsigmaa : ¬ (sigma a = -1)
      rcases h1a with hpos | hneg
      · exact hpos
      · exfalso; exact this hneg
    have h2_1 : sigma b (p*q) = -1 := by
      rw [hsa_pos] at hprod
      simp at hprod
      exact hprod

    have h2_2a : seqVar (seqEval a (sturmSeq p q))
      = seqVar (seqEval a (sturmSeq q (-p%q))) := by
      sorry
    have h2_2b : seqVar (seqEval b (sturmSeq p q))
      = 1 + seqVar (seqEval b (sturmSeq q (-p%q))) := by
      sorry

    rw[h2_2a, h2_2b, h2_1]; simp
    linarith

theorem L_2_59_2 (a b : ℝ) (p q : Polynomial ℝ) (hprod : sigma b (p*q) * sigma a (p*q) = 1):
      ((∀ i : Fin (sturmSeq p q).length, eval a (sturmSeq p q)[i]! ≠ 0) ∧ ( ∀ i : Fin (sturmSeq p q).length, eval b (sturmSeq p q)[i]! ≠ 0))
      → (seqVar (seqEval a (sturmSeq p q)) - seqVar (seqEval b (sturmSeq p q)))
      =  seqVar (seqEval a (sturmSeq q (-p%q))) - seqVar (seqEval b (sturmSeq q (-p%q))):= by
  have sigma_a_ne_zero : sigma a (p*q) ≠ 0 := by
    intro H
    have : sigma b (p*q) * 0 = 1 := by
      rw [H] at hprod; exact hprod
    simp at this
  have eval_a_ne_zero : eval a (p*q) ≠ 0 := by
    intro Heval
    have : sigma a (p*q) = 0 := by simp [sigma, sgn, Heval]
    exact (sigma_a_ne_zero this)

  sorry

theorem L_2_59 (a b : ℝ) (p q : Polynomial ℝ) :
      ((∀ i : Fin (sturmSeq p q).length, eval a (sturmSeq p q)[i]! ≠ 0) ∧ ( ∀ i : Fin (sturmSeq p q).length, eval b (sturmSeq p q)[i]! ≠ 0))
      → if hprod : sigma b (p*q) * sigma a (p*q) = 1 then (seqVar (seqEval a (sturmSeq p q)) - seqVar (seqEval b (sturmSeq p q)))
      =  seqVar (seqEval a (sturmSeq q (-p%q))) - seqVar (seqEval b (sturmSeq q (-p%q))) else (seqVar (seqEval a (sturmSeq p q)) - seqVar (seqEval b (sturmSeq p q)))
      =  sigma b (p*q) + seqVar (seqEval a (sturmSeq q (-p%q))) - seqVar (seqEval b (sturmSeq q (-p%q))):= by
  sorry

theorem Sturm (f g : Polynomial ℝ) (a b : ℝ) (h : a < b) :
      seqVar (seqEval a (sturmSeq f (derivative f * g))) - seqVar (seqEval b (sturmSeq f (derivative f * g)))
      = tarskiQuery f g a b
      := by
  sorry
