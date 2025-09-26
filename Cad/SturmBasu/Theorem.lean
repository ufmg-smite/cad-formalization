import Mathlib

import Cad.SturmBasu.Utils
import Cad.SturmBasu.SignRPos

open Polynomial Set Filter Classical

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
  if f = 0 then
    []
  else
    f::(sturmSeq g (-f%g))
  termination_by if f=0 then 0 else if g=0 then 1 else 2 + degree g
  decreasing_by
    simp_all
    if g1: g = 0 then
      simp_all
    else if h : g ∣ f then
      simp_all
      have gnatdeg : g.degree ≥ 0 := by exact zero_le_degree_iff.mpr g1
      refine lt_add_of_lt_of_nonneg ?_ gnatdeg; simp
    else
      simp_all
      have :(-f % g).degree < g.degree := by
        refine degree_lt_degree ?_; refine natDegree_mod_lt (-f) ?_
        have : g.natDegree = 0 → g ∣ f := by
          intro hg
          have : ∃ c : ℝ, C c = g := by
            exact natDegree_eq_zero.mp hg
          rcases this with ⟨c, rfl⟩; use C c⁻¹ * f
          have hds : c ≠ 0 := by
            intro abs; rw [abs] at hg; simp at g1; exact g1 abs
          ext x; simp; field_simp
        have : g.natDegree ≠ 0 := by intro abs; exact h (this abs)
        exact this
      refine WithBot.add_lt_add_left ?_ this; simp_all

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
| a::as => (eval k a)::(seqEval k as)

def seqVar_ab (P: List (Polynomial ℝ)) (a b: ℝ): ℤ :=
  (seqVar (seqEval a P) : Int) - seqVar (seqEval b P)

def seqVarSturm_ab (p q: (Polynomial ℝ)) (a b : ℝ) : ℤ :=
  seqVar_ab (sturmSeq p q) a b

def sgn (k : ℝ) : ℤ  :=
  if k > 0 then 1
  else if k = 0 then 0
  else -1

def rootsInInterval (f : Polynomial ℝ) (a b : ℝ) : Finset ℝ :=
  f.roots.toFinset.filter (fun x => x ∈ Ioo a b)

def tarskiQuery (f g : Polynomial ℝ) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval f a b, sgn (g.eval x)

-- 1 if p / q goes from -inf to +inf at x, -1 if goes from +inf to -inf
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

lemma rootsInIntervalZero (a b : ℝ) : rootsInInterval 0 a b = ∅ := by
  simp [rootsInInterval]

lemma jump_poly_sign (p q : Polynomial ℝ) (x : ℝ) :
    p ≠ 0 → p.eval x = 0 → jump_val p (derivative p * q) x = sgn (q.eval x) := by
  intros hp hev
  if hq : q = 0 then
    rw [hq]
    simp [sgn, jump_val]
  else
    have deriv_ne_0 : derivative p ≠ 0 := derivative_ne_0 p x hev hp
    have elim_p_order : rootMultiplicity x p - rootMultiplicity x (derivative p * q) = 1 - rootMultiplicity x q := by
      rw [Polynomial.rootMultiplicity_mul]
      · rw [derivative_rootMultiplicity_of_root hev]
        have : 1 ≤ rootMultiplicity x p := by
          apply (Polynomial.le_rootMultiplicity_iff hp).mpr
          simp
          exact dvd_iff_isRoot.mpr hev
        omega
      · exact (mul_ne_zero_iff_right hq).mpr deriv_ne_0
    have elim_sgn_r_pos_p : sign_r_pos x ((derivative p * q) * p) = sign_r_pos x q := by
      have : sign_r_pos x ((derivative p * q) * p) = (sign_r_pos x (derivative p * p) ↔ sign_r_pos x q) := by
        rw [mul_comm, <- mul_assoc]
        have := sign_r_pos_mult (p * derivative p) q x ((mul_ne_zero_iff_right deriv_ne_0).mpr hp) hq
        nth_rw 2 [mul_comm p (derivative p)] at this
        exact this
      rw [this]
      have := sign_r_pos_deriv p x hp hev
      aesop
    unfold jump_val
    admit

lemma B_2_57 (p q : Polynomial ℝ) (a b : ℝ) (hab : a < b)  :
    tarskiQuery p q a b = cauchyIndex p (derivative p * q) a b := by
  if hp : p = 0 then
    rw [hp]
    simp [tarskiQuery, cauchyIndex]
    rw [rootsInIntervalZero]
    simp
  else
    unfold tarskiQuery
    unfold cauchyIndex
    apply Finset.sum_congr rfl
    intros x hx
    have : p.eval x = 0 := by
      simp [rootsInInterval] at hx
      exact hx.1.2
    rw [jump_poly_sign p q x hp this]

-- Talvez usar reais extendidos para a e b seja a tradução mais imediata do enunciado.
-- Por enquanto, podemos seguir desconsiderando esse caso.
theorem B_2_58 (p q: Polynomial ℝ) (hp: p != Polynomial.C 0) (a b: ℝ) (hab : a < b) :
    seqVarSturm_ab p q a b = cauchyIndex p q a b :=
  sorry

def sigma (b : ℝ) (f : Polynomial ℝ) : ℤ :=
  sgn (eval b f)

-- para o else, precisamos usar ha e hb para mostrar que σ(a) * σ(b) != 0 (e pela definição de sgn, excluir todos outros inteiros).
-- Talvez seja possível expressar isso de alguma forma melhor.
lemma B_2_60 (p q r: Polynomial ℝ) (hr: r = p % q) (a b: ℝ)
             (ha: ∀p' ∈ sturmSeq p q, ¬IsRoot p' a)
             (hb: ∀p' ∈ sturmSeq p q, ¬IsRoot p' b):
    if (sigma a p * q) * (sigma b p * q) = -1 then
      cauchyIndex p q a b = (cauchyIndex q (-r) a b) + sigma b p * q
    else
      cauchyIndex p q a b = cauchyIndex q (-r) a b :=
sorry

lemma seqVar_sign_change {x y : ℝ} {xs : List ℝ} (hy : y ≠ 0) :
  seqVar (x :: (y :: xs)) = (if x * y < 0 then 1 else 0) + seqVar (y :: xs) := by
    simp_all
    rw[seqVar]
    simp [hy]
    split_ifs; simp_all
    simp

lemma sigma_eq_def (a : ℝ) (p q : Polynomial ℝ) : sigma a (p*q) = sgn (eval a p * eval a q) := by rw[sigma]; simp

theorem L_2_59_1 (a b : ℝ) (p q : Polynomial ℝ) (hprod : sigma b (p*q) * sigma a (p*q) = -1) (hq : q ≠ 0) (hp : p ≠ 0) (hj : ((∀p' ∈ sturmSeq p q, ¬IsRoot p' a) ∧ ( ∀p' ∈ sturmSeq p q, ¬IsRoot p' b))):
      seqVarSturm_ab p q a b
      =  sigma b (p*q) + seqVarSturm_ab q (-p%q) a b := by
  rw [seqVarSturm_ab, seqVar_ab];  rcases hj with ⟨ha, hb⟩
  have sigma_a_ne_zero : sigma a (p*q) ≠ 0 := by
    intro H
    have : sigma b (p*q) * 0 = -1 := by rw [H] at hprod; exact hprod
    simp at this
  have eval_a_ne_zero : eval a (p*q) ≠ 0 := by
    intro Heval
    have : sigma a (p*q) = 0 := by simp [sigma, sgn, Heval]
    exact (sigma_a_ne_zero this)
  have eval_a_q_ne_zero : eval a q ≠ 0 := by
    have : eval a p * eval a q ≠ 0 := by rw [eval_mul] at eval_a_ne_zero; exact eval_a_ne_zero
    exact right_ne_zero_of_mul this
  have sigma_b_ne_zero : sigma b (p*q) ≠ 0 := by
    intro H
    have : 0 * sigma a (p*q) = -1 := by rw [H] at hprod; exact hprod
    simp at this
  have eval_b_ne_zero : eval b (p*q) ≠ 0 := by
    intro Heval
    have : sigma b (p*q) = 0 := by simp [sigma, sgn, Heval]
    exact (sigma_b_ne_zero this)
  have eval_b_q_ne_zero : eval b q ≠ 0 := by
    have : eval b p * eval b q ≠ 0 := by rw [eval_mul] at eval_b_ne_zero; exact eval_b_ne_zero
    exact right_ne_zero_of_mul this
  have h1a : sigma a (p*q) = 1 ∨ sigma a (p*q) = -1 := by
    rw[sigma, sgn]
    if hpos : eval a (p*q) > 0 then
      left; split_ifs; rfl
    else right; split_ifs; rfl
  have hseqEval : seqEval a (sturmSeq p q) = eval a p :: seqEval a (sturmSeq q (-p % q)) := by rw[sturmSeq, seqEval.eq_def]; simp at hp; simp[hp]
  have hseqEvalb : seqEval b (sturmSeq p q) = eval b p :: seqEval b (sturmSeq q (-p % q)) := by rw[sturmSeq, seqEval.eq_def]; simp at hp; simp[hp]
  if hsigmaa : sigma a (p*q) = -1 then
    have h2_1 : sigma b (p*q) = 1 := by
      rw [hsigmaa] at hprod
      simp at hprod; exact hprod
    have h2_2a : seqVar (seqEval a (sturmSeq p q)) = 1 + seqVar (seqEval a (sturmSeq q (-p%q))) := by
      rw[hseqEval]
      calc
        seqVar (eval a p :: seqEval a (sturmSeq q (-p % q)))
          = (if eval a p * eval a q < 0 then 1 else 0) + seqVar (seqEval a (sturmSeq q (-p % q))) := by
            have : seqEval a (sturmSeq q (-p % q)) = eval a q :: seqEval a (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]; apply seqVar_sign_change eval_a_q_ne_zero
        _ = 1 + seqVar (seqEval a (sturmSeq q (-p % q))) := by
          simp [hprod]
          have haqsgn : eval a p * eval a q < 0 := by
            rw[sigma_eq_def, sgn] at hsigmaa; simp at hsigmaa
            by_cases hpos : eval a p * eval a q > 0
            · simp [hpos] at hsigmaa
            by_cases heq : eval a p * eval a q = 0
            · simp [heq] at hsigmaa; exfalso
              have contra : eval a p * eval a q ≠ 0 := mul_ne_zero (And.left hsigmaa) (And.right hsigmaa)
              exact contra heq
            have hle : eval a p * eval a q ≤ 0 := le_of_not_gt hpos
            have : 0 ≠ eval a p * eval a q := by intro Haux; exact heq Haux.symm
            exact lt_of_le_of_ne hle (Ne.symm this)
          exact haqsgn
    have h2_2b : seqVar (seqEval b (sturmSeq p q))= seqVar (seqEval b (sturmSeq q (-p%q))) := by
      rw[hseqEvalb]
      calc
        seqVar (eval b p :: seqEval b (sturmSeq q (-p % q)))
          = (if eval b p * eval b q < 0 then 1 else 0) + seqVar (seqEval b (sturmSeq q (-p % q))) := by
            have : seqEval b (sturmSeq q (-p % q)) = eval b q :: seqEval b (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]
            apply seqVar_sign_change eval_b_q_ne_zero
        _ = 0 + seqVar (seqEval b (sturmSeq q (-p % q))) := by
          simp [hprod]
          have hbsgn : eval b p * eval b q > 0 := by
            rw[sigma_eq_def, sgn] at h2_1
            split_ifs at h2_1
            assumption
            linarith
          linarith
      linarith
    rw[h2_2a, h2_2b, h2_1]; simp
    rw [seqVarSturm_ab, seqVar_ab]
    linarith
  else
    have hsa_pos : sigma a (p*q) = 1 := by
      have : sigma a (p*q) = -1 → False := by
        intro H; apply (by simp [H] at hsigmaa)
      rcases h1a with hpos | hneg
      · exact hpos
      · exfalso; exact this hneg
    have h2_1 : sigma b (p*q) = -1 := by rw [hsa_pos] at hprod; simp at hprod; exact hprod
    have h2_2a : seqVar (seqEval a (sturmSeq p q))
      = seqVar (seqEval a (sturmSeq q (-p%q))) := by
      have : seqEval a (sturmSeq p q) = eval a p :: seqEval a (sturmSeq q (-p % q)) := by rw[sturmSeq, seqEval.eq_def]; simp at hp; simp[hp]
      rw[this]
      calc
        seqVar (eval a p :: seqEval a (sturmSeq q (-p % q)))
          = (if eval a p * eval a q < 0 then 1 else 0) + seqVar (seqEval a (sturmSeq q (-p % q))) := by
            have : seqEval a (sturmSeq q (-p % q)) = eval a q :: seqEval a (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]
            apply seqVar_sign_change eval_a_q_ne_zero
        _ = 0 + seqVar (seqEval a (sturmSeq q (-p % q))) := by
          simp [hprod]
          have haqsgn : eval a p * eval a q > 0 := by
            rw[sigma_eq_def, sgn] at hsa_pos
            split_ifs at hsa_pos
            assumption
            linarith
          linarith
      linarith
    have h2_2b : seqVar (seqEval b (sturmSeq p q))
      = 1 + seqVar (seqEval b (sturmSeq q (-p%q))) := by
      have : seqEval b (sturmSeq p q) = eval b p :: seqEval b (sturmSeq q (-p % q)) := by rw[sturmSeq, seqEval.eq_def]; simp at hp; simp[hp]
      rw[this]
      calc
        seqVar (eval b p :: seqEval b (sturmSeq q (-p % q)))
          = (if eval b p * eval b q < 0 then 1 else 0) + seqVar (seqEval b (sturmSeq q (-p % q))) := by
            have : seqEval b (sturmSeq q (-p % q)) = eval b q :: seqEval b (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]
            apply seqVar_sign_change eval_b_q_ne_zero
        _ = 1 + seqVar (seqEval b (sturmSeq q (-p % q))) := by
          simp [hprod]
          have hbsgn : eval b p * eval b q < 0 := by
            rw[sigma_eq_def, sgn] at h2_1
            simp at h2_1
            by_cases hpos : eval b p * eval b q > 0
            · simp [hpos] at h2_1
            by_cases heq : eval b p * eval b q = 0
            · simp [heq] at h2_1
              exfalso
              have contra : eval b p * eval b q ≠ 0 :=
                mul_ne_zero (And.left h2_1) (And.right h2_1)
              exact contra heq
            have hle : eval b p * eval b q ≤ 0 := le_of_not_gt hpos
            have : 0 ≠ eval b p * eval b q := by intro Haux; exact heq Haux.symm
            exact lt_of_le_of_ne hle (Ne.symm this)
          exact hbsgn
    rw[h2_2a, h2_2b, h2_1]; simp
    rw [seqVarSturm_ab, seqVar_ab]
    linarith

theorem L_2_59_2 (a b : ℝ) (p q : Polynomial ℝ) (hprod : sigma b (p*q) * sigma a (p*q) = 1) (hq : q ≠ 0) (hp : p ≠ 0) (hj : ((∀p' ∈ sturmSeq p q, ¬IsRoot p' a) ∧ (∀p' ∈ sturmSeq p q, ¬IsRoot p' b))):
      seqVarSturm_ab p q a b =  seqVarSturm_ab q (-p%q) a b := by
  rw [seqVarSturm_ab, seqVar_ab]; rcases hj with ⟨ha, hb⟩
  have sigma_a_ne_zero : sigma a (p*q) ≠ 0 := by
    intro H
    have : sigma b (p*q) * 0 = 1 := by
      rw [H] at hprod; exact hprod
    simp at this
  have eval_a_ne_zero : eval a (p*q) ≠ 0 := by
    intro Heval
    have : sigma a (p*q) = 0 := by simp [sigma, sgn, Heval]
    exact (sigma_a_ne_zero this)
  have eval_a_q_ne_zero : eval a q ≠ 0 := by
    have : eval a p * eval a q ≠ 0 := by rw [eval_mul] at eval_a_ne_zero; exact eval_a_ne_zero
    exact right_ne_zero_of_mul this
  have sigma_b_ne_zero : sigma b (p*q) ≠ 0 := by
    intro H
    have : 0 * sigma a (p*q) = 1 := by
      rw [H] at hprod; exact hprod
    simp at this
  have eval_b_ne_zero : eval b (p*q) ≠ 0 := by
    intro Heval
    have : sigma b (p*q) = 0 := by simp [sigma, sgn, Heval]
    exact (sigma_b_ne_zero this)
  have eval_b_q_ne_zero : eval b q ≠ 0 := by
    have : eval b p * eval b q ≠ 0 := by rw [eval_mul] at eval_b_ne_zero; exact eval_b_ne_zero
    exact right_ne_zero_of_mul this
  have h1a : sigma a (p*q) = 1 ∨ sigma a (p*q) = -1 := by
    rw[sigma, sgn]
    if hpos : eval a (p*q) > 0 then
      left; split_ifs; rfl
    else right; split_ifs; rfl
  have hseqEval : seqEval a (sturmSeq p q) = eval a p :: seqEval a (sturmSeq q (-p % q)) := by rw[sturmSeq, seqEval.eq_def]; simp at hp; simp[hp]
  have hseqEvalb : seqEval b (sturmSeq p q) = eval b p :: seqEval b (sturmSeq q (-p % q)) := by rw[sturmSeq, seqEval.eq_def]; simp at hp; simp[hp]
  if hsigmaa : sigma a (p*q) = 1 then
    have h2_1 : sigma b (p*q) = 1 := by
      rw [hsigmaa] at hprod
      simp at hprod; exact hprod
    have h2_2a : seqVar (seqEval a (sturmSeq p q)) = 0 + seqVar (seqEval a (sturmSeq q (-p%q))) := by
      rw[hseqEval]
      calc
        seqVar (eval a p :: seqEval a (sturmSeq q (-p % q)))
          = (if eval a p * eval a q < 0 then 1 else 0) + seqVar (seqEval a (sturmSeq q (-p % q))) := by
            have : seqEval a (sturmSeq q (-p % q)) = eval a q :: seqEval a (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]; apply seqVar_sign_change eval_a_q_ne_zero
        _ = 0 + seqVar (seqEval a (sturmSeq q (-p % q))) := by
          simp [hprod]
          have haqsgn : eval a p * eval a q > 0 := by
            rw[sigma_eq_def, sgn] at hsigmaa
            split_ifs at hsigmaa
            assumption
            linarith
          linarith
    simp at hsigmaa
    simp at h2_2a
    have h2_2b : seqVar (seqEval b (sturmSeq p q)) = 0 + seqVar (seqEval b (sturmSeq q (-p%q))) := by
      rw[hseqEvalb]
      calc
        seqVar (eval b p :: seqEval b (sturmSeq q (-p % q)))
          = (if eval b p * eval b q < 0 then 1 else 0) + seqVar (seqEval b (sturmSeq q (-p % q))) := by
            have : seqEval b (sturmSeq q (-p % q)) = eval b q :: seqEval b (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]; apply seqVar_sign_change eval_b_q_ne_zero
        _ = 0 + seqVar (seqEval b (sturmSeq q (-p % q))) := by
          simp [hprod]
          have haqsgn : eval b p * eval b q > 0 := by
            rw[sigma_eq_def, sgn] at h2_1
            split_ifs at h2_1
            assumption
            linarith
          linarith
    simp at h2_1; simp at h2_2b; rw[h2_2a, h2_2b]
    rw [seqVarSturm_ab, seqVar_ab]
  else
    have hsa_neg : sigma a (p*q) = -1 := by
      have : sigma a (p*q) = 1 → False := by
        intro H; apply (by simp [H] at hsigmaa)
      rcases h1a with hpos | hneg
      · exfalso; exact this hpos
      · exact hneg
    have h2_1 : sigma b (p*q) = -1 := by rw [hsa_neg] at hprod; simp at hprod; linarith
    have h2_2a : seqVar (seqEval a (sturmSeq p q)) = 1 + seqVar (seqEval a (sturmSeq q (-p%q))) := by
      rw[hseqEval]
      calc
        seqVar (eval a p :: seqEval a (sturmSeq q (-p % q)))
          = (if eval a p * eval a q < 0 then 1 else 0) + seqVar (seqEval a (sturmSeq q (-p % q))) := by
            have : seqEval a (sturmSeq q (-p % q)) = eval a q :: seqEval a (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]; apply seqVar_sign_change eval_a_q_ne_zero
        _ = 1 + seqVar (seqEval a (sturmSeq q (-p % q))) := by
          simp [hprod]
          have hbsgn : eval a p * eval a q < 0 := by
            rw[sigma_eq_def, sgn] at hsa_neg
            simp at hsa_neg
            by_cases hpos : eval a p * eval a q > 0
            · simp [hpos] at hsa_neg
            by_cases heq : eval a p * eval a q = 0
            · simp [heq] at hsa_neg
              exfalso
              have contra : eval a p * eval a q ≠ 0 :=
                mul_ne_zero (And.left hsa_neg) (And.right hsa_neg)
              exact contra heq
            have hle : eval a p * eval a q ≤ 0 := le_of_not_gt hpos
            have : 0 ≠ eval a p * eval a q := by intro Haux; exact heq Haux.symm
            exact lt_of_le_of_ne hle (Ne.symm this)
          exact hbsgn
    have h2_2b : seqVar (seqEval b (sturmSeq p q)) = 1 + seqVar (seqEval b (sturmSeq q (-p%q))) := by
      rw[hseqEvalb]
      calc
        seqVar (eval b p :: seqEval b (sturmSeq q (-p % q)))
          = (if eval b p * eval b q < 0 then 1 else 0) + seqVar (seqEval b (sturmSeq q (-p % q))) := by
            have : seqEval b (sturmSeq q (-p % q)) = eval b q :: seqEval b (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]; apply seqVar_sign_change eval_b_q_ne_zero
        _ = 1 + seqVar (seqEval b (sturmSeq q (-p % q))) := by
          have haqsgn : eval b p * eval b q < 0 := by
            rw[sigma_eq_def, sgn] at h2_1
            by_cases hpos : eval b p * eval b q > 0
            · simp [hpos] at h2_1
            by_cases heq : eval b p * eval b q = 0
            · simp [heq] at h2_1
            have hle : eval b p * eval b q ≤ 0 := le_of_not_gt hpos
            have : 0 ≠ eval b p * eval b q := by intro Haux; exact heq Haux.symm
            exact lt_of_le_of_ne hle (Ne.symm this)
          simp_all
    simp at h2_1; simp at h2_2a; simp at h2_2b; rw[h2_2a, h2_2b]; simp_all; ring_nf
    rw [seqVarSturm_ab, seqVar_ab]

/-
def seqVar_ab (P: List (Polynomial ℝ)) (a b: ℝ): ℤ :=
  (seqVar (seqEval a P) : Int) - seqVar (seqEval b P)

def seqVarSturm_ab (p q: (Polynomial ℝ)) (a b : ℝ) : ℤ :=
  seqVar_ab (sturmSeq p q) a b
-/
theorem L_2_59 (a b : ℝ) (p q : Polynomial ℝ) (hq : q ≠ 0) (hp : p ≠ 0):
      ((∀p' ∈ sturmSeq p q, ¬IsRoot p' a) ∧ (∀p' ∈ sturmSeq p q, ¬IsRoot p' b))
      → if hprod : sigma b (p*q) * sigma a (p*q) = 1 then (seqVarSturm_ab p q a b)
      =  seqVarSturm_ab q (-p%q) a b else seqVarSturm_ab p q a b
      =  sigma b (p*q) + seqVarSturm_ab q (-p%q) a b := by
  intro h
  if hprod : sigma b (p*q) * sigma a (p*q) = 1 then
    simp_all
    exact L_2_59_2 a b p q hprod hq hp h
  else
    simp_all
    have hneg : sigma b (p*q) * sigma a (p*q) = -1 := by
      have : sigma b (p*q) * sigma a (p*q) ≠ 1 := by intro H; exact hprod H
      have : sigma b (p*q) * sigma a (p*q) ≠ 0 := by
        intro H
        have : sigma b (p*q) ≠ 0 := by
          intro Haux; rw[sigma, sgn] at Haux; simp_all
          have : eval b (p*q) ≠ 0 := by
            intro Heval
            have aux := And.right h
            have : ¬ eval b p = 0 := by
              apply aux p; rw[sturmSeq]; simp; exact hp
            have : ¬ eval b q = 0 := by
              apply aux q; rw[sturmSeq]; simp;
              sorry
            sorry
          sorry
        sorry
      sorry
    exact L_2_59_1 a b p q hneg hq hp h

theorem Tarski (f g : Polynomial ℝ) (hf : f ≠ C 0) (a b : ℝ) (h : a < b) :
      seqVarSturm_ab f (derivative f * g) a b
      = tarskiQuery f g a b
      := by
  rw [B_2_57 _ _ _ _ h]
  rw [<- B_2_58 _ _ _ _ _ h]
  simp [hf]
  simp_all only [map_zero, ne_eq, not_false_eq_true]
