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

@[simp]
theorem cindex_poly_z_1 {p q: Polynomial ℝ} {a b: ℝ} (hp: p = 0) : cauchyIndex p q a b  = 0 := by 
  unfold cauchyIndex jump_val
  simp [hp]

@[simp]
theorem cindex_poly_z_2 {p q: Polynomial ℝ} {a b: ℝ} (hq: q = 0) : cauchyIndex p q a b  = 0 := by
  unfold cauchyIndex jump_val
  simp [hq]

theorem cindex_poly_mult {p q p': Polynomial ℝ} {a b: ℝ} (hp' : p' ≠ 0) :
    (cauchyIndex (p' * p) (p' * q) a b) = cauchyIndex p q a b := by
  if hp: p = 0 then
    simp [hp]
  else 
    unfold cauchyIndex
    simp only [ne_eq, not_false_eq_true, jump_poly_mult, hp', hp]
    have : ∑ x ∈ rootsInInterval p' a b \ rootsInInterval p a b, jump_val p q x = 0 := by
      apply Finset.sum_eq_zero
      intros x hx
      simp only [Finset.mem_sdiff] at hx
      unfold rootsInInterval at hx
      have : eval x p ≠ 0 := by
        have ⟨hx_1, hx_2⟩ := hx
        simp_all
      exact jump_poly_not_root this
    have h_interval : rootsInInterval (p' * p) a b = rootsInInterval p a b ∪ (rootsInInterval p' a b \ rootsInInterval p a b) := by
      unfold rootsInInterval
      aesop
    simp only [h_interval]
    have hdsj : Disjoint (rootsInInterval p a b) (rootsInInterval p' a b \ rootsInInterval p a b) := by
      exact Finset.disjoint_sdiff
    rw [Finset.sum_union hdsj]
    simp [this]
         
theorem cindex_poly_inverse_add {p q: Polynomial ℝ} {a b: ℝ} (hpq_coprime: IsCoprime p q) : cauchyIndex p q a b + cauchyIndex q p a b = cauchyIndex (q * p) 1 a b := by
  if hpqz: p = 0 ∨ q = 0 then
   rcases hpqz with hp | hq <;> simp_all
  else
    rw [Mathlib.Tactic.PushNeg.not_or_eq] at hpqz; have ⟨hpz, hqz⟩ := hpqz
    let A := rootsInInterval p a b
    let B := rootsInInterval q a b
    have hl: cauchyIndex p q a b + cauchyIndex q p a b = ∑ x ∈ A, jump_val (q * p) 1 x + ∑ x ∈ B, jump_val (q*p) 1 x := by
      have hf: cauchyIndex p q a b = ∑ x ∈ A, jump_val (q * p) 1 x := by
        unfold A cauchyIndex 
        refine Finset.sum_congr rfl ?_
        intros x hx
        unfold rootsInInterval at hx
        have : eval x p = 0 := by aesop
        exact jump_poly_coprime this hpq_coprime
      have hs: cauchyIndex q p a b = ∑ x ∈ B, jump_val (q * p) 1 x := by
       unfold B cauchyIndex
       refine Finset.sum_congr rfl ?_
       intros x hx
       unfold rootsInInterval at hx
       have : eval x q = 0 := by aesop
       have hqp_coprime: IsCoprime q p := by exact id (IsCoprime.symm hpq_coprime)
       rw [mul_comm]
       exact jump_poly_coprime this hqp_coprime
      linarith
    have hab_union : A ∪ B = rootsInInterval (q * p) a b := by
      unfold A B rootsInInterval
      aesop
    have hab_disjoint' : A ∩ B = ∅ := by
      if H: A = ∅ ∨ B = ∅ then aesop
      else
        by_contra!
        have hy: ∃ y: ℝ, y ∈ A ∧ y ∈ B := by
         simp only [not_or, ne_eq, <-Finset.nonempty_iff_ne_empty] at H this
         exact Finset.filter_nonempty_iff.mp this
        have ⟨y, hy⟩ := hy
        have h_eval : eval y p = 0 ∧ eval y q = 0 := by
          unfold A B rootsInInterval at hy
          simp_all
        have h_monom: (X - C y) ∣ p ∧ (X - C y) ∣ q := by
            simp [dvd_iff_isRoot, h_eval]
        have h_monon_dvd : (X - C y) ∣ gcd p q := by exact (dvd_gcd_iff (X - C y) p q).mpr h_monom
        have hf : ¬IsUnit (gcd p q)  := by
          by_contra!
          rw [isUnit_iff] at this; have ⟨r, hr⟩ := this
          have h_contra :¬ X - C y ∣ (gcd p q) := by
            rw [<-hr.2]
            refine not_dvd_of_degree_lt ?_ ?_
            · aesop
            · have hrz : r ≠ 0 := by exact isUnit_iff_ne_zero.mp hr.1
              rw [degree_C hrz];
              exact (Monic.degree_pos (monic_X_sub_C y)).mpr (X_sub_C_ne_one y)
          exact h_contra h_monon_dvd
        exact hf ((gcd_isUnit_iff p q).mpr hpq_coprime)
    have hab_disjoint : (Disjoint A B) := by exact Finset.disjoint_iff_inter_eq_empty.mpr hab_disjoint'
    rw [hl]
    unfold cauchyIndex
    unfold A B at hab_disjoint hab_union
    rw [<-Finset.sum_union hab_disjoint, hab_union]
    
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
      = cauchyIndex p' q' a b + cauchyIndex q' p' a b:= by -- cindex_poly_mult
    --rw[cauchyIndex, cauchyIndex, cauchyIndex, cauchyIndex]
    rw[hp',hq']
    if h1p0 : p = 0 then
      exfalso
      have : ¬ p = 0 := by apply pneq0;
      exact this h1p0
    else
      rw [cindex_poly_mult h_gcd, cindex_poly_mult h_gcd]
  have cauchy1 : cauchyIndex p' q' a b + cauchyIndex q' p' a b
      = cauchyIndex 1 (q' * p') a b := by sorry -- cindex_poly_inverse_add (short)
  have cauchyVar : cauchyIndex 1 (q' * p') a b
      = variation (eval a (p' * q'))  (eval b (p'*q')) := by sorry -- cindex_poly_cross (long, but doesn't seem to use many lemmas from their formalization)
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
