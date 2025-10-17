import Mathlib

import Cad.SturmBasu.Utils
import Cad.SturmBasu.JumpPoly

noncomputable section

open Polynomial

-- Corresponde a Ind(Q/P; a, b)
def cauchyIndex (p q : Polynomial ℝ) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval p a b, jump_val p q x

def variation (a b : Real) : Int :=
  if a * b ≥ 0 then 0 else if a < b then 1 else -1

def cross (p : Polynomial Real) (a b : Real) : Int :=
  variation (p.eval a) (p.eval b)

theorem cauchyIndex_poly_inverse_add_cross (p q : Polynomial ℝ) (a b : ℝ)
    (hab : a < b) (hapq : eval a (p*q) ≠ 0) (hbpq : eval b (p*q) ≠ 0) :
    cauchyIndex p q a b + cauchyIndex q p a b = cross (p * q) a b
    := by
  unfold cross
  have tp : p ≠ 0 := by sorry
  have tq : q ≠ 0 := by sorry
  have ⟨q', hq'⟩ : ∃q', q = gcd p q * q' := by
    sorry
  have ⟨p', hp'⟩ : ∃p', p = gcd p q * p' := by
    sorry
  let g := gcd p q
  have : p' ≠ 0 := by sorry
  have : q' ≠ 0 := by sorry
  have h_gcd : gcd p q ≠ 0 := by sorry
  have : cauchyIndex p q a b + cauchyIndex q p a b = cauchyIndex q' p' a b + cauchyIndex p' q' a b := by
    sorry
  rw[this]
  have : cauchyIndex q' p' a b + cauchyIndex p' q' a b = cauchyIndex 1 (q' * p') a b := by sorry
  rw[this]
  have : cauchyIndex 1 (q' * p') a b = variation (eval a (p' * q'))  (eval b (p'*q')):= by sorry
  rw[this]
  have : variation (eval a (p' * q'))  (eval b (p'*q')) = variation (eval a (p * q))  (eval b (p*q)) := by
    have t1 : eval a (p * q) = eval a (g*g) * eval a (p' * q') := by
      sorry
    rw[t1]
    have t2 : eval b (p * q) = eval b (g*g) * eval b (p' * q') := by
      sorry
    rw[t2]
    have t3 : eval a (g*g) > 0 := by
      sorry
    have t4 : eval b (g*g) > 0 := by
      sorry
    have t5 : (eval a (g * g) * eval a (p' * q') < eval b (g * g) * eval b (p' * q'))
        ↔ eval a (p' * q') < eval b (p' * q') := by
      sorry

    rw[variation, variation]
    have t6 : eval a (g * g) * eval a (p' * q') * (eval b (g * g) * eval b (p' * q')) ≥ 0
        ↔ eval a (p' * q') * eval b (p' * q') ≥ 0 := by
      sorry
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
    · rfl
    · --exact h1 h2 t6
      sorry
    · --exact h1 h2 t6
      sorry
    · --exact h1 h5 t6
      sorry
    · rfl
    · -- exact h4 h6 t5
      sorry
    · -- exact h1 h7 t6
      sorry
    · --exact h4 h8 t5
      have : eval a (p' * q') < eval b (p' * q') := sorry -- t5
      exact h4 this
    rfl
  rw[this]

lemma cauchyIndex_poly_mod (p q : Polynomial Real) (a b : Real) :
    cauchyIndex p q a b = cauchyIndex p (q % p) a b := by
  unfold cauchyIndex
  have := jump_poly_mod p q
  exact Finset.sum_congr rfl fun x a => this x

lemma cauchyIndex_smult_1 (p q : Polynomial Real) (a b c : Real) :
    cauchyIndex p (C c * q) a b = sgn c * cauchyIndex p q a b := by
  unfold cauchyIndex
  have : sgn c * ∑ x ∈ rootsInInterval p a b, jump_val p q x = ∑ x ∈ rootsInInterval p a b, sgn c * (jump_val p q x) := Finset.mul_sum (rootsInInterval p a b) (jump_val p q) (sgn c)
  rw [this]
  congr
  ext x
  exact jump_poly_smult_1 p q c x
