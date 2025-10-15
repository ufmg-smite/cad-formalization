import Mathlib

import Cad.SturmBasu.Utils
import Cad.SturmBasu.JumpPoly

noncomputable section

-- Corresponde a Ind(Q/P; a, b)
def cauchyIndex (p q : Polynomial ℝ) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval p a b, jump_val p q x

def variation (a b : Real) : Int :=
  if a * b ≥ 0 then 0 else if a < b then 1 else -1

def cross (p : Polynomial Real) (a b : Real) : Int :=
  variation (p.eval a) (p.eval b)

lemma cauchyIndex_poly_inverse_cross (p q : Polynomial Real) (a b : Real) (hab : a < b)
    (ha2 : (p * q).eval a ≠ 0) (hb2 : (p * q).eval b ≠ 0) :
    cauchyIndex p q a b + cauchyIndex q p a b = cross (p * q) a b := sorry

lemma cauchyIndex_poly_mod (p q : Polynomial Real) (a b : Real) :
    cauchyIndex p q a b = cauchyIndex p (q % p) a b := by
  unfold cauchyIndex
  have := jump_poly_mod p q
  exact Finset.sum_congr rfl fun x a => this x

lemma cauchyIndex_smult_1 (p q : Polynomial Real) (a b c : Real) :
    cauchyIndex p (c • q) a b = sgn c * cauchyIndex p q a b := sorry

