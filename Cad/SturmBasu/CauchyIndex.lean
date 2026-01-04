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

lemma sign_r_pos_comm (x : ℝ) (p q : Polynomial ℝ) :
    sign_r_pos x (p * q) = sign_r_pos x (q * p) := by
  if hpq : p * q = 0 then
    rw [hpq, mul_comm, hpq]
  else
    rw [sign_r_pos_rec]
    nth_rw 2 [sign_r_pos_rec]
    · rw [mul_comm]
    · exact mul_ne_zero_comm.mp hpq
    · exact hpq

lemma or_neg_of_mul_neg (a b : ℝ) : a * b < 0 → a < 0 ∨ b < 0 := by
  intro h
  apply or_iff_not_imp_left.mpr
  intro ha
  by_contra hb
  simp only [not_lt] at ha hb
  have : 0 ≤ a * b := Left.mul_nonneg ha hb
  linarith

theorem variation_mult_pos1 (c x y : ℝ) (hc : c > 0) : variation (c*x) y = variation x y := by
  rw[variation, variation]
  have sgnequals : (0 ≤ x*y) = (0 ≤ c*x*y) := by
    simp
    constructor
    · intro hxy
      ring_nf; simp_all
      set k := x * y with hk
      have hk_nonneg : 0 ≤ k := by simpa [hk] using hxy
      have tk := mul_nonneg (le_of_lt hc) hxy
      have : c*x*y = c*(x*y):= by linarith
      simp_all
    · intro hcxy
      ring_nf; simp_all
      have : c * 0 ≤ c * (x * y) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcxy
      apply (mul_le_mul_left (show 0 < c from hc)).mp this
  have hneg : c * x * y < 0 → (c * x < y ↔ x < y) := by
    intro hcy
    simp_all
    have hxy : x * y < 0 := (lt_iff_lt_of_le_iff_le (Iff.symm sgnequals)).mp hcy
    have : (c * x < y) = (x < y) := by
      simp_all
      constructor
      · intro hcxley
        cases or_neg_of_mul_neg x y hxy
        next hx0 =>
          have hy0 : y > 0 := (neg_iff_pos_of_mul_neg hxy).mp hx0
          exact lt_trans hx0 hy0
        next hy => nlinarith
      · intro hxley
        cases or_neg_of_mul_neg x y hxy
        next hx0 =>
          have hy0 : y > 0 := (neg_iff_pos_of_mul_neg hxy).mp hx0
          have hcx0 : c * x < 0 := mul_neg_of_pos_of_neg hc hx0
          exact lt_trans hcx0 hy0
        next hy0 => nlinarith
    rw[this]
  have : (if 0 ≤ c * x * y then 0 else if c * x < y then 1 else -1)
     = (if 0 ≤ c * x * y then 0 else if x < y then 1 else -1) := by
    by_cases hcy : 0 ≤ c * x * y
    · simp [hcy]
    · have hcy' : c * x * y < 0 := lt_of_not_ge hcy
      have hx : (c * x < y ↔ x < y) := (hneg hcy')
      simp [hcy, hx]
  simp_all only [gt_iff_lt, eq_iff_iff, ge_iff_le]

theorem variation_mult_pos2 (c x y : ℝ) (hc : c > 0) : variation x (c*y) = variation x y := by
  rw[variation, variation]
  have sgnequals : (0 ≤ x*y) = (0 ≤ c*x*y) := by
    simp
    constructor
    · intro hxy
      ring_nf; simp_all
      set k := x * y with hk
      have hk_nonneg : 0 ≤ k := by simpa [hk] using hxy
      have tk := mul_nonneg (le_of_lt hc) hxy
      have : c*x*y = c*(x*y):= by linarith
      simp_all
    · intro hcxy
      ring_nf; simp_all
      have : c * 0 ≤ c * (x * y) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcxy
      apply (mul_le_mul_left (show 0 < c from hc)).mp this
  have hneg : c * x * y < 0 → (x < c * y ↔ x < y) := by
    intro hcy
    simp_all
    have hxy : x * y < 0 := (lt_iff_lt_of_le_iff_le (Iff.symm sgnequals)).mp hcy
    have : (x < c * y) = (x < y) := by
      simp_all
      constructor
      · intro hcxley
        cases or_neg_of_mul_neg x y hxy
        next hx0 =>
          have hy0 : y > 0 := (neg_iff_pos_of_mul_neg hxy).mp hx0
          exact lt_trans hx0 hy0
        next hy =>
          have : 0 < x := (pos_iff_neg_of_mul_neg hxy).mpr hy
          have : 0 < c * y := gt_trans hcxley this
          have : c * y < 0 := mul_neg_of_pos_of_neg hc hy
          linarith
      · intro hxley
        cases or_neg_of_mul_neg x y hxy
        next hx0 =>
          have hy0 : y > 0 := (neg_iff_pos_of_mul_neg hxy).mp hx0
          have : 0 < c * y := Left.mul_pos hc hy0
          linarith
        next hy0 => nlinarith
    rw[this]

  have : (if 0 ≤ x * c * y then 0 else if x < c * y then 1 else -1)
     = (if 0 ≤ c * x * y then 0 else if x < y then 1 else -1) := by
     have : x * c * y = c * x * y := by linarith
     rw [this]
     by_cases h: 0 ≤ c * x * y
     · simp [h]
     · simp [h]
       simp at h
       exact if_ctx_congr (hneg h) (congrFun rfl) (congrFun rfl)
  rw [<- mul_assoc, this]
  aesop

theorem cindex_poly_inverse_add_cross (p q : Polynomial ℝ) (a b : ℝ)
    (hab : a < b) (hapq : eval a (p*q) ≠ 0) (hbpq : eval b (p*q) ≠ 0) :
    cauchyIndex p q a b + cauchyIndex q p a b = variation (eval a (p * q)) (eval b (p*q))
    := by

  have pneq0 : p ≠ 0 := by
    intro hfalse
    have : eval a (p * q) = 0 := by simp [hfalse]
    exact hapq this
  have qneq0 : q ≠ 0 := by
    intro hfalse
    have : eval a (p * q) = 0 := by simp [hfalse]
    exact hapq this
  let g := gcd p q
  have ⟨q', hq'⟩ : ∃q', q = g * q' := by
    unfold g; refine dvd_iff_exists_eq_mul_right.mp ?_; exact gcd_dvd_right p q
  have ⟨p', hp'⟩ : ∃p', p = g * p' := by
    unfold g; refine dvd_iff_exists_eq_mul_right.mp ?_; exact gcd_dvd_left p q
  /- have coprimep'q': gcd p' q' = 1 := sorry -/
  have p'neq0 : p' ≠ 0 := by
    intro hfalse
    have : p = 0 := by simp [hp', hfalse]
    exact pneq0 this
  have q'neq0 : q' ≠ 0 := by
    intro hfalse
    have : q = 0 := by simp [hq', hfalse]
    exact qneq0 this
  have h_gcd : g ≠ 0 := by
    intro hfalse
    have : q = 0 := by simp [hq', hfalse]
    exact qneq0 this

  have cauchyMuls : cauchyIndex p q a b + cauchyIndex q p a b
      = cauchyIndex p' q' a b + cauchyIndex q' p' a b:= by
    --rw[cauchyIndex, cauchyIndex, cauchyIndex, cauchyIndex]
    rw[hp',hq']
    if h1p0 : p = 0 then
      exfalso
      have : ¬ p = 0 := by apply pneq0;
      exact this h1p0
    else
      unfold cauchyIndex
      have (x : ℝ) : jump_val (g * p') (g * q') x =  jump_val p' q' x := by exact jump_poly_mult h_gcd
      have (x : ℝ) : jump_val (g * q') (g * p') x =  jump_val q' p' x := by exact jump_poly_mult h_gcd
      simp_all
      -- rootsInInterval (g * p') a b = rootsInInterval p' a b ?
      sorry
  have cauchy1 : cauchyIndex p' q' a b + cauchyIndex q' p' a b
      = cauchyIndex 1 (q' * p') a b := by sorry
  have cauchyVar : cauchyIndex 1 (q' * p') a b
      = variation (eval a (p' * q'))  (eval b (p'*q')) := by sorry
  have : variation (eval a (p' * q'))  (eval b (p'*q'))
      = variation (eval a (p * q)) (eval b (p*q)) := by
    have t1 : eval a (p * q) = eval a (g*g) * eval a (p' * q') := by
      rw [hp', hq']
      simp only [eval_mul]
      linarith
    rw[t1]
    have t2 : eval b (p * q) = eval b (g*g) * eval b (p' * q') := by
      rw[hp', hq']
      simp only [eval_mul]
      linarith
    rw[t2]

    simp at hapq
    obtain ⟨hap, haq⟩ := hapq
    have hag : eval a g ≠ 0 := by
      intro abs
      rw [hp'] at hap
      simp at hap
      obtain ⟨hag, hap'⟩ := hap
      exact hag abs

    simp at hbpq
    obtain ⟨hbp, hbq⟩ := hbpq
    have hbg : eval b g ≠ 0 := by
      intro abs
      rw [hp'] at hbp
      simp at hbp
      obtain ⟨hbg, hbp'⟩ := hbp
      exact hbg abs

    have t3 : eval a (g*g) > 0 := by simp [hag]
    have t4 : eval b (g*g) > 0 := by simp [hbg]
    have aux1 : variation (eval a (p' * q')) (eval b (p' * q'))
        = variation (eval a (g * g) * eval a (p' * q')) (eval b (p' * q')) := by
      have : variation (eval a (g * g) * eval a (p' * q')) (eval b (p' * q'))
          = variation (eval a (p' * q')) (eval b (p' * q')) := by
        apply variation_mult_pos1 (eval a (g * g))  (eval a (p' * q')) ((eval b (p' * q'))) t3
      rw[this]

    have aux2 : variation (eval a (p' * q')) (eval b (p' * q'))
        = variation (eval a (p' * q')) (eval b (g * g) * eval b (p' * q')) := by
      have : variation (eval a (p' * q')) (eval b (g * g) * eval b (p' * q'))
          = variation (eval a (p' * q')) (eval b (p' * q')) := by
        apply variation_mult_pos2 (eval b (g * g))  (eval a (p' * q')) ((eval b (p' * q'))) t4
      rw[this]
    have := Trans.trans aux1.symm aux2
    admit
  simp_all
