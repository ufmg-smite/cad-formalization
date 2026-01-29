import Mathlib

import Cad.SturmBasu.Utils
import Cad.SturmBasu.SignRPos
import Cad.SturmBasu.CauchyIndex
import Cad.SturmBasu.JumpPoly

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
  (seqVar (seqEval a P) : Int) -   seqVar (seqEval b P)

def seqVarSturm_ab (p q: (Polynomial ℝ)) (a b : ℝ) : ℤ :=
  seqVar_ab (sturmSeq p q) a b

def tarskiQuery (f g : Polynomial ℝ) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval f a b, sgn (g.eval x)

lemma rootsInIntervalZero (a b : ℝ) : rootsInInterval 0 a b = ∅ := by
  simp [rootsInInterval]


lemma smod_nil_eq (p q : Polynomial Real) :
    sturmSeq p q = [] ↔ p = 0 := by
  constructor
  · intro hs
    apply Classical.byContradiction
    intro h_abs
    unfold sturmSeq at hs
    simp [h_abs] at hs
  · intro hp
    simp [hp, sturmSeq]


@[simp]
lemma smods_s_0_1 (p: Polynomial ℝ) : sturmSeq 0 p = [] := by exact (smod_nil_eq 0 p).mpr rfl

@[simp]
lemma smods_s_0_2 (p: Polynomial ℝ) : sturmSeq p 0 = if p = 0 then [] else [p] := by
  split_ifs with H
  · exact (smod_nil_eq p 0).mpr H
  · unfold sturmSeq; simp [H]

@[simp]
lemma seqEval_empty (k: ℝ) : seqEval k [] = [] := by unfold seqEval; rfl
@[simp]
lemma seqVar_ab_singleton (p: Polynomial ℝ) (a b: ℝ): seqVar_ab [p] a b = 0 := by
  unfold seqVar_ab seqVar seqEval
  simp
@[simp]
theorem seqVarSturm_ab_z_1 (p: Polynomial ℝ) (a b: ℝ) : seqVarSturm_ab 0 p a b = 0 := by
  unfold seqVarSturm_ab seqVar_ab seqVar seqEval sturmSeq
  simp

 @[simp]
theorem seqVarSturm_ab_z_2 (p: Polynomial ℝ) (a b: ℝ) : seqVarSturm_ab p 0 a b = 0 := by
  unfold seqVarSturm_ab seqVar_ab seqVar seqEval
  if H: p = 0 then
    simp [H]
  else
    simp [H]

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
    have elim_sgn_r_pos_p : sign_r_pos x (p * (derivative p * q)) = sign_r_pos x q := by
      have : sign_r_pos x (p * (derivative p * q)) = (sign_r_pos x (derivative p * p) ↔ sign_r_pos x q) := by
        have := sign_r_pos_mult (p * derivative p) q x ((mul_ne_zero_iff_right deriv_ne_0).mpr hp) hq
        nth_rw 2 [mul_comm p (derivative p)] at this
        rw [<- mul_assoc]
        exact this
      rw [this]
      have := sign_r_pos_deriv p x hp hev
      aesop
    let simpleL : Int :=
      if derivative p * q ≠ 0 ∧ Odd (1 - rootMultiplicity x q) then
        (if sign_r_pos x q then 1 else -1)
      else 0
    have : jump_val p (derivative p * q) x = simpleL := by
      simp [jump_val, simpleL, hp, deriv_ne_0, hq, elim_p_order, elim_sgn_r_pos_p]
    rw [this]
    cases Classical.em (eval x q = 0)
    next hevQ =>
      have : 0 < rootMultiplicity x q := (rootMultiplicity_pos hq).mpr hevQ
      have : 1 - rootMultiplicity x q = 0 := by omega
      have : ¬ Odd (1 - rootMultiplicity x q) := by rw [this]; exact Nat.not_odd_zero
      have lhs : simpleL = 0 := by
        simp [simpleL, this]
      have rhs : sgn (eval x q) = 0 := by rw [hevQ]; simp [sgn]
      rw [lhs, rhs]
    next hevQ =>
      have : rootMultiplicity x q = 0 := rootMultiplicity_eq_zero hevQ
      have h1 : Odd (1 - rootMultiplicity x q) := by
        rw [this]
        exact Nat.odd_iff.mpr rfl
      have h2 : derivative p * q ≠ 0 := by
        clear * - hq deriv_ne_0
        intro abs
        simp_all only [ne_eq, mul_eq_zero, or_self]
      have h3 : sign_r_pos x q ↔ 0 < eval x q := by
        rw [sign_r_pos_rec]
        simp [hevQ]
        exact hq
      have h4 : simpleL = if 0 < eval x q then 1 else -1 := by
        simp [simpleL, h1, h2, h3]
      rw [h4]
      simp [sgn, hevQ]

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

theorem changes_itv_smods_rec {a b: ℝ} {p q: Polynomial ℝ} (hab: a < b) (hpqa: eval a (p * q)≠ 0) (hpqb: eval b (p * q) ≠ 0) :
        (seqVarSturm_ab p q a b) = cross (p * q) a b + seqVarSturm_ab q (-p%q) a b := by
  if H: p = 0 ∨ q = 0 ∨ p % q = 0 then
    rcases H with h | h | h
    · simp [h]
    · simp [h]
    · unfold seqVarSturm_ab seqVar_ab seqEval cross seqVar sturmSeq
      rw [mod_minus, h]
      have ⟨hap, haq⟩: eval a p ≠ 0 ∧ eval a q ≠ 0 := by aesop
      have ⟨hbp, hbq⟩: eval b p ≠ 0 ∧ eval b q ≠ 0:= by aesop
      have hpz: p ≠ 0 := by aesop
      have hqz: q ≠ 0 := by aesop
      have : ¬sturmSeq p q = [] := by simp [hpz, smod_nil_eq]
      unfold seqEval
      simp [variation_cases, hpz, hqz, haq, hbq]
      split_ifs with h1 h2 h3
      · unfold seqVar;
        rw [(variation_cases (eval a p * eval a q) (eval b p * eval b q)).2.2.2 ⟨h1, h2⟩];
        simp
      · unfold seqVar
        have : eval b p * eval b q > 0 := by
          rw [eval_mul] at hpqb
          rw [not_lt, <-ge_iff_le] at h2
          exact lt_of_le_of_ne h2 (Ne.symm hpqb)
        rw [(variation_cases (eval a p * eval a q) (eval b p * eval b q)).2.2.1 ⟨h1, this⟩];
        simp
      · unfold seqVar
        have : eval a p * eval a q > 0 := by
          rw [eval_mul] at hpqa
          rw [not_lt, <-ge_iff_le] at h1
          exact lt_of_le_of_ne h1 (Ne.symm hpqa)
        rw [(variation_cases (eval a p * eval a q) (eval b p * eval b q)).2.1 ⟨this, h3⟩];
        simp
      · unfold seqVar
        have : eval a p * eval a q > 0 ∧ eval b p * eval b q > 0 := by
          rw [eval_mul] at hpqa hpqb
          rw [not_lt, <-ge_iff_le] at h1 h3
          exact ⟨lt_of_le_of_ne h1 (Ne.symm hpqa), lt_of_le_of_ne h3 (Ne.symm hpqb)⟩
        rw [(variation_cases (eval a p * eval a q) (eval b p * eval b q)).1 this];
        simp
   else
     simp only [not_or] at H
     have ⟨ps, httl, htlmod⟩ : ∃ ps : List (Polynomial ℝ), sturmSeq p q = p :: q :: -p%q:: ps ∧ sturmSeq q (-p%q) = q :: (-p%q) :: ps := by
       unfold sturmSeq sturmSeq
       rw [sturmSeq]
       simp_all
     let changes_diff := fun x => ((seqVar (seqEval x (p::q::(-p%q)::ps)): ℤ) - (seqVar (seqEval x (q::(-p%q)::ps))): ℤ)
     have hz1: ∀ x: ℝ, (eval x p) * (eval x q) < 0 → changes_diff x = 1 := by
       unfold changes_diff -- seqVar seqEval seqEval
       intros x hx
       rw [seqVar.eq_def, seqEval, seqEval]
       have hxq : eval x q ≠ 0 := by aesop
       simp [H.2.2, hxq, hx]
     have hz2: ∀x, (eval x p) * (eval x q) > 0 → changes_diff x = 0 := by
       unfold changes_diff
       intros x hx
       rw [seqVar.eq_def, seqEval, seqEval]
       have hxq : eval x q ≠ 0 := by aesop
       have  : ¬ eval x p * eval x q < 0 := by nlinarith
       simp [hxq, this]
     have hf: changes_diff a - changes_diff b = cross (p * q) a b := by
       unfold cross
       rcases lt_or_gt_of_ne hpqa with ha | ha <;> rcases lt_or_gt_of_ne hpqb with hb | hb
       · rw [(variation_cases (eval a (p * q)) (eval b (p * q))).2.2.2 ⟨ha, hb⟩]
         simp_all
       · rw [(variation_cases (eval a (p * q)) (eval b (p * q))).2.2.1 ⟨ha, hb⟩]
         simp_all
       · rw [(variation_cases (eval a (p * q)) (eval b (p * q))).2.1 ⟨ha, hb⟩]
         simp_all
       · rw [(variation_cases (eval a (p * q)) (eval b (p * q))).1 ⟨ha, hb⟩]
         simp_all
     unfold changes_diff at hf
     unfold seqVarSturm_ab
     rw [httl, htlmod, ← sub_eq_iff_eq_add]
     unfold seqVar_ab
     ring_nf at hf ⊢
     rw [hf]

set_option maxHeartbeats 500000 in
theorem B_2_58_aux (p q: Polynomial ℝ) (a b: ℝ) (hab: a < b): ∃ (a' b': ℝ), a < a' ∧ a' < b' ∧ b' < b ∧ (∀p' ∈ sturmSeq p q, (∀ x: ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) -> eval x p' ≠ 0)) := by
  induction h: (sturmSeq p q) generalizing p q with
    | nil =>
      let a' := 2/3 * a + 1/3 * b
      let b' := 1/3 * a + 2/3 * b
      have ⟨haa', ha'b', hbb'⟩ : a < a' ∧ a' < b' ∧ b' < b := by
        repeat' constructor
        · unfold a'; linarith
        · unfold a' b'; linarith
        · unfold b'; linarith
      have hn_root:(∀p' ∈ [], ∀ x:ℝ, (((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) → (eval x p' ≠ 0))) := by simp
      use a', b'
    | cons hd tl ih =>
      let r := - (p % q)
      have hpz: p ≠ 0 := by aesop
      have htl: sturmSeq q r = tl := by
        unfold sturmSeq at h;
        simp [hpz] at h
        unfold r
        rw [<-mod_minus]; exact h.2
      have h_concat: sturmSeq p q = p :: tl := by
        unfold sturmSeq at h ⊢; simp [hpz] at h; simp [h.2, hpz]
      have h_hd: hd = p := by aesop
      have ⟨a1, b1, haa1, ha1b1, hbb1, ha1b1_nroot⟩: ∃ (a1 b1: ℝ), a < a1 ∧ a1 < b1 ∧ b1 < b ∧
           (∀p' ∈ tl, (∀ x: ℝ, ((a < x ∧ x ≤ a1) ∨ (b1 ≤ x ∧ x < b)) -> eval x p' ≠ 0)) := by
        exact ih q r htl
      have ⟨a2, b2, haa2, ha2_nroot, hbb2, hb2_nroot⟩ : ∃ (a2 b2: ℝ), a < a2 ∧ (∀x: ℝ, (a < x ∧ x ≤ a2) -> eval x p ≠ 0) ∧
                                                         (b2 < b) ∧ (∀x: ℝ, (b2 ≤ x ∧ x < b) -> eval x p ≠ 0) := by
       have ⟨a2, haa2, ha2_nroot⟩ := next_non_root_interval p a hpz
       have ⟨b2, hbb2, hb2_nroot⟩ := last_non_root_interval p b hpz
       use a2, b2
       simp_all
      let a' := if b2 > a then min a1 (min b2 a2) else min a1 a2
      let b' := if a2 < b then max b1 (max a2 b2) else max b1 b2
      have ⟨haa', ha'b', hbb'⟩ : a < a' ∧ a' < b' ∧ b' < b := by
        unfold a' b'
        constructor <;> split_ifs <;> simp_all
      have h_rec: ∀p' ∈ tl, ∀x: ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b))  -> eval x p' ≠ 0 := by
        have ha'a1: a' ≤ a1 := by unfold a'; split_ifs <;> simp
        have hb'b: b1 ≤ b' := by unfold b'; split_ifs <;> simp
        intros p' haux x hx
        rcases hx with hl | hr
        · have : a < x ∧ x ≤ a1 := by constructor <;> linarith
          exact ha1b1_nroot p' haux x (Or.inl this)
        · have : b1 ≤ x ∧ x < b := by constructor <;> linarith
          exact ha1b1_nroot p' haux x (Or.inr this)
      have h_final: ∀ x: ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) -> eval x p ≠ 0 := by
        unfold a' b'; intros x
        split_ifs <;> intros hx <;> simp only [le_inf_iff, sup_le_iff] at hx
        · rcases hx with hl | hr
          · exact ha2_nroot x ⟨hl.1, hl.2.2.2⟩
          · exact hb2_nroot x ⟨hr.1.2.2, hr.2⟩
        · rcases hx with hl | hr
          · exact ha2_nroot x ⟨hl.1, hl.2.2.2⟩
          · exact hb2_nroot x ⟨hr.1.2, hr.2⟩
        · rcases hx with hl | hr
          · exact ha2_nroot x ⟨hl.1, hl.2.2⟩
          · exact hb2_nroot x ⟨hr.1.2.2, hr.2⟩
        · rcases hx with hl | hr
          · exact ha2_nroot x ⟨hl.1, hl.2.2⟩
          · exact hb2_nroot x ⟨hr.1.2, hr.2⟩
      use a', b'
      rw [h_hd]
      simp [haa', ha'b', hbb', <-ne_eq]
      exact ⟨h_final, h_rec⟩

def sigma (b : ℝ) (f : Polynomial ℝ) : ℤ :=
  sgn (eval b f)

-- cindex_poly_rec
-- para o else, precisamos usar ha e hb para mostrar que σ(a) * σ(b) != 0 (e pela definição de sgn, excluir todos outros inteiros).
-- Talvez seja possível expressar isso de alguma forma melhor.
lemma B_2_60 (p q : Polynomial ℝ) (a b: ℝ) (hab : a < b)
    (ha : (p * q).eval a ≠ 0) (hb : (p * q).eval b ≠ 0) :
    cauchyIndex p q a b = cross (p * q) a b + cauchyIndex q (- p % q) a b
    := by
  have : q ≠ 0 := by
    intro abs
    rw [abs] at ha
    simp at ha
  have H := cindex_poly_inverse_add_cross p q a b hab ha hb
  have : - cauchyIndex q p a b = cauchyIndex q (- p % q) a b := by
    have h1 := cauchyIndex_poly_mod q (-p) a b
    have h2 := cauchyIndex_smult_1 q p a b (-1)
    simp [sgn] at h2
    have : (if (1 : Real) < 0 then cauchyIndex q p a b else (-cauchyIndex q p a b)) = -cauchyIndex q p a b := by
      split
      next h => linarith
      next h => rfl
    rw [this] at h2
    clear this
    rw [<- h2, h1]
  simp only [cross, variation] at *
  linarith

lemma changes_smods_congr (p q : Polynomial ℝ) (a a' : ℝ) (haa' : a ≠ a') (hpa : eval a p ≠ 0)
    (no_root : ∀ p' ∈ sturmSeq p q, ∀ x : ℝ, ((a < x ∧ x ≤ a') ∨ (a' ≤ x ∧ x < a)) → eval x p' ≠ 0) :
    seqVar (seqEval a (sturmSeq p q)) = seqVar (seqEval a' (sturmSeq p q)) := by
  have p_neq_0 : p ≠ 0 := eval_non_zero p a hpa
  let r1 := -p%q
  have r1_def : r1 = -p%q := rfl
  have a_a'_rel: ∀ pp ∈ sturmSeq p q, eval a pp * eval a' pp ≥ 0 := by
    by_contra!
    obtain ⟨pp, hpp1, hpp2⟩ := this
    if haa': a < a' then
      obtain ⟨x, hx1, hx2, hx3⟩ : ∃ x : ℝ, a < x ∧ x < a' ∧ eval x pp = 0 := exists_root_ioo_mul (le_of_lt haa') hpp2
      have := no_root pp hpp1 x (Or.inl (And.intro hx1 (le_of_lt hx2)))
      exact this hx3
    else
      simp at haa'
      rw [mul_comm] at hpp2
      obtain ⟨x, hx1, hx2, hx3⟩ : ∃ x : ℝ, a' < x ∧ x < a ∧ eval x pp = 0 := exists_root_ioo_mul haa' hpp2
      have := no_root pp hpp1 x (Or.inr (And.intro (le_of_lt hx1) hx2))
      exact this hx3

  if hq: q = 0 then
    unfold sturmSeq
    simp [hq, seqEval, seqVar, p_neq_0]
  else if hq2: eval a q = 0 then
    let r2 := -(q%r1)
    have : eval a p = - (eval a r1) := by
      have h1 := EuclideanDomain.quotient_mul_add_remainder_eq p q
      have h2 : r1 = EuclideanDomain.remainder (-p) q := by
        unfold r1
        rfl
      have : eval a p = eval a (q * EuclideanDomain.quotient p q + EuclideanDomain.remainder p q) := by
        congr
        exact (Eq.symm h1)
      rw [this]
      simp [hq2]
      rw [h2]
      have : ∀ p q : Polynomial ℝ, EuclideanDomain.remainder p q = p % q := by intros p q; rfl
      rw [this, this (-p) q, mod_minus]
      simp
    have : eval a r1 = -eval a p := by linarith
    have h_eval_r : eval a r1 ≠ 0 := by rw [this]; exact neg_ne_zero.mpr hpa
    have r_neq_0 : r1 ≠ 0 := eval_non_zero r1 a h_eval_r
    have eval_a_eval_r : eval a p * eval a r1 < 0 := by rw [this]; simp; exact hpa
    obtain ⟨ps, hps1, hps2⟩ : ∃ ps, sturmSeq p q = p :: q :: r1 :: ps ∧ sturmSeq r1 r2 = r1 :: ps := by
      unfold sturmSeq
      simp [p_neq_0, hq, r_neq_0]
      rw [<- r1_def]
      nth_rw 1 [sturmSeq]
      simp [hq]
      nth_rw 1 [sturmSeq]
      split_ifs
      next h => exact r_neq_0 h
      next h =>
        congr
        · exact mod_minus q r1
        · exact mod_minus q r1
    have : List.length (sturmSeq r1 r2) < List.length (sturmSeq p q) := by simp [hps1, hps2]
    have no_root_2_aux := no_root
    rw [hps1] at no_root_2_aux
    have no_root_2 : ∀ p' ∈ sturmSeq r1 r2, ∀ (x : ℝ), a < x ∧ x ≤ a' ∨ a' ≤ x ∧ x < a → eval x p' ≠ 0 := by
      rw [hps2]
      clear * - no_root_2_aux
      intros p' hp'
      have : p' ∈ p :: q :: r1 :: ps := by
        simp
        right
        right
        simp at hp'
        exact hp'
      exact no_root_2_aux p' this
    have IH := changes_smods_congr r1 r2 a a' haa' h_eval_r no_root_2
    have rec_a : seqVar (seqEval a (sturmSeq p q)) = 1 + seqVar (seqEval a (sturmSeq r1 r2)) := by
      rw [hps1, hps2, seqEval, seqEval]
      simp [seqVar, hq2]
      rw [seqEval, seqVar]
      simp [hpa, h_eval_r]
      exact eval_a_eval_r
    have rec_a' : seqVar (seqEval a' (sturmSeq p q)) = 1 + seqVar (seqEval a' (sturmSeq r1 r2)) := by
      have hp1 : eval a p * eval a' p ≥ 0 := by
        rw [hps1] at a_a'_rel
        apply a_a'_rel
        exact List.mem_cons_self p (q :: r1 :: ps)
      have hr1 : eval a r1 * eval a' r1 ≥ 0 := by
        rw [hps1] at a_a'_rel
        apply a_a'_rel
        simp only [List.mem_cons, true_or, or_true]
      have ev_neq_0_p : eval a' p ≠ 0 := by
        rw [hps1] at no_root
        apply no_root p (List.mem_cons_self p (q :: r1 :: ps))
        aesop
      have ev_neq_0_r1 : eval a' r1 ≠ 0 := by
        rw [hps1] at no_root
        apply no_root r1
        · simp only [List.mem_cons, true_or, or_true]
        · aesop
      have ev_neq_0_q : eval a' q ≠ 0 := by
        rw [hps1] at no_root
        apply no_root q
        · simp only [List.mem_cons, true_or, or_true]
        · aesop
      rw [hps1, hps2]
      rw [seqEval, seqEval, seqEval]
      rw [seqVar]
      simp [ev_neq_0_q]
      split_ifs
      next H =>
        simp [seqVar, ev_neq_0_r1]
        by_contra!
        have : (eval a' p * eval a' q) * (eval a' q * eval a' r1) > 0 := mul_pos_of_neg_of_neg H this
        have h1 : (eval a' p * eval a' r1) * (eval a' q * eval a' q) > 0 := by linarith
        have h2 : eval a' q * eval a' q > 0 := mul_self_pos.mpr ev_neq_0_q
        have h_pos : eval a' p * eval a' r1 > 0 := (pos_iff_pos_of_mul_pos h1).mpr h2
        have : (eval a p * eval a' p) * (eval a r1 * eval a' r1) ≥ 0 := Left.mul_nonneg hp1 hr1
        have : (eval a p * eval a r1) * (eval a' p * eval a' r1) ≥ 0 := by linarith
        have : eval a p * eval a r1 ≥ 0 := (mul_nonneg_iff_of_pos_right h_pos).mp this
        linarith
      next H =>
        simp [seqVar, ev_neq_0_r1]
        simp at H
        by_contra!
        have : 0 ≤ (eval a' p * eval a' q) * (eval a' q * eval a' r1) := Left.mul_nonneg H this
        have h1 : 0 ≤ (eval a' p * eval a' r1) * (eval a' q * eval a' q) := by linarith
        have h2 : 0 < eval a' q * eval a' q := mul_self_pos.mpr ev_neq_0_q
        have h_pos : 0 ≤ eval a' p * eval a' r1 := (mul_nonneg_iff_of_pos_right h2).mp h1
        have ev_pos : 0 < eval a' p * eval a' r1 := by
          by_contra!
          have : 0 = eval a' p * eval a' r1 := by linarith
          have : eval a' p = 0 ∨ eval a' r1 = 0 := mul_eq_zero.mp (id (Eq.symm this))
          cases this
          next inl => exact ev_neq_0_p inl
          next inr => exact ev_neq_0_r1 inr
        have : (eval a p * eval a' p) * (eval a r1 * eval a' r1) ≥ 0 := Left.mul_nonneg hp1 hr1
        have : (eval a p * eval a r1) * (eval a' p * eval a' r1) ≥ 0 := by linarith
        have : eval a p * eval a r1 ≥ 0 := (mul_nonneg_iff_of_pos_right ev_pos).mp this
        linarith
    rw [rec_a, rec_a', IH]
  else
    obtain ⟨ps, hps1, hps2⟩ : ∃ ps, sturmSeq p q = p :: q :: ps ∧ sturmSeq q r1 = q :: ps := by
      rw [sturmSeq]
      simp [p_neq_0]
      rw [sturmSeq]
      simp [hq, hq2]
    have : List.length (sturmSeq q r1) < List.length (sturmSeq p q) := by
      rw [hps1, hps2]
      simp
    have no_root_2_aux := no_root
    rw [hps1] at no_root_2_aux
    have no_root_2 : ∀ p' ∈ sturmSeq q r1, ∀ (x : ℝ), a < x ∧ x ≤ a' ∨ a' ≤ x ∧ x < a → eval x p' ≠ 0 := by
      rw [hps2]
      clear * - no_root_2_aux
      intros p' hp'
      have : p' ∈ p :: q :: ps := List.mem_cons_of_mem p hp'
      exact no_root_2_aux p' this
    have IH := changes_smods_congr q r1 a a' haa' hq2 no_root_2
    have hpa' : eval a' p ≠ 0 := by
      apply no_root p (by rw [hps1]; exact List.mem_cons_self p (q :: ps))
      aesop
    have hqa' : eval a' q ≠ 0 := by
      apply no_root q (by rw [hps1]; simp)
      aesop
    have ev_pa' : eval a p * eval a' p ≥ 0 := by
      apply a_a'_rel p (by rw [hps1]; exact List.mem_cons_self p (q :: ps))
    have ev_qa' : eval a q * eval a' q ≥ 0 := by
      apply a_a'_rel q (by rw [hps1]; simp)
    rw [hps1]
    simp [seqEval, seqVar, hq2, hqa']
    have eq_a : seqVar (eval a q :: seqEval a ps) = seqVar (seqEval a (q :: ps)) := by simp [seqEval]
    have eq_a' : seqVar (eval a' q :: seqEval a' ps) = seqVar (seqEval a' (q :: ps)) := by simp [seqEval]
    rw [hps2] at IH
    split_ifs
    next h1 h2 => rw [eq_a, eq_a', IH]
    next h1 h2 =>
      push_neg at h2
      clear * - h1 h2 ev_pa' ev_qa' hq2 hpa hpa' hqa'
      cases Classical.em (eval a p > 0)
      next h_evap =>
        have Ha'p : eval a' p > 0 := by
          by_contra!
          have : eval a' p < 0 := lt_of_le_of_ne this hpa'
          have : eval a p * eval a' p < 0 := mul_neg_of_pos_of_neg h_evap this
          linarith
        have Haq : eval a q < 0 := by
          by_contra!
          have : eval a q > 0 := lt_of_le_of_ne this fun a_1 => hq2 (Eq.symm a_1)
          have : eval a p * eval a q > 0 := Left.mul_pos h_evap this
          linarith
        have Ha'q : eval a' q < 0 := by
          by_contra!
          have : eval a' q > 0 := lt_of_le_of_ne this (Ne.symm hqa')
          have : eval a q * eval a' q < 0 := mul_neg_of_neg_of_pos Haq this
          linarith
        have : eval a' q * eval a' p < 0 := mul_neg_of_neg_of_pos Ha'q Ha'p
        linarith
      next h_evap =>
        push_neg at h_evap
        have h_evap : eval a p < 0 := lt_of_le_of_ne h_evap hpa
        have Ha'p : eval a' p < 0 := by
          by_contra!
          have : eval a' p > 0 := lt_of_le_of_ne this (id (Ne.symm hpa'))
          have : eval a p * eval a' p < 0 := mul_neg_of_neg_of_pos h_evap this
          linarith
        have Haq : eval a q > 0 := by
          by_contra!
          have : eval a q < 0 := lt_of_le_of_ne this hq2
          have : eval a p * eval a q > 0 := mul_pos_of_neg_of_neg h_evap this
          linarith
        have Ha'q : eval a' q > 0 := by
          by_contra!
          have : eval a' q < 0 := by exact lt_of_le_of_ne this hqa'
          have : eval a q * eval a' q < 0 := mul_neg_of_pos_of_neg Haq this
          linarith
        have : eval a' p * eval a' q < 0 := mul_neg_of_neg_of_pos Ha'p Ha'q
        linarith
    next h1 h2 =>
      push_neg at h2
      clear * - h1 h2 ev_pa' ev_qa' hq2 hpa hpa' hqa'
      cases Classical.em (eval a p > 0)
      next h_evap =>
        have Ha'p : eval a' p > 0 := by
          by_contra!
          have : eval a' p < 0 := lt_of_le_of_ne this hpa'
          have : eval a p * eval a' p < 0 := mul_neg_of_pos_of_neg h_evap this
          linarith
        have Haq : eval a q > 0 := by
          by_contra!
          have : eval a q < 0 := lt_of_le_of_ne this hq2
          have : eval a p * eval a q < 0 := mul_neg_of_pos_of_neg h_evap this
          linarith
        have Ha'q : eval a' q > 0 := by
          by_contra!
          have : eval a' q < 0 := (pos_iff_neg_of_mul_neg h2).mp Ha'p
          have : eval a q * eval a' q < 0 := mul_neg_of_pos_of_neg Haq this
          linarith
        have : eval a' q * eval a' p > 0 := Left.mul_pos Ha'q Ha'p
        linarith
      next h_evap =>
        push_neg at h_evap
        have h_evap : eval a p < 0 := lt_of_le_of_ne h_evap hpa
        have Ha'p : eval a' p < 0 := by
          by_contra!
          have : eval a' p > 0 := lt_of_le_of_ne this (id (Ne.symm hpa'))
          have : eval a p * eval a' p < 0 := mul_neg_of_neg_of_pos h_evap this
          linarith
        have Haq : eval a q < 0 := by
          by_contra!
          have : eval a q > 0 := lt_of_le_of_ne this fun a_1 => hq2 (id (Eq.symm a_1))
          have : eval a p * eval a q < 0 := mul_neg_of_neg_of_pos h_evap this
          linarith
        have Ha'q : eval a' q < 0 := by
          by_contra!
          have : eval a' q > 0 := (neg_iff_pos_of_mul_neg h2).mp Ha'p
          have : eval a q * eval a' q < 0 := mul_neg_of_neg_of_pos Haq this
          linarith
        have : eval a' p * eval a' q > 0 := mul_pos_of_neg_of_neg Ha'p Ha'q
        linarith
    next h1 h2 => rw [eq_a, eq_a', IH]
termination_by List.length (sturmSeq p q)

lemma changes_itv_smods_congr (p q : Polynomial ℝ) (a a' b b' : ℝ) (hpa : eval a p ≠ 0) (hpb : eval b p ≠ 0)
    (haa' : a < a') (hb'b : b' < b)
    (no_root : ∀ p' ∈ sturmSeq p q, ∀ x : ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) → eval x p' ≠ 0) :
    seqVarSturm_ab p q a b = seqVarSturm_ab p q a' b' := by
  have p_neq_0 : p ≠ 0 := eval_non_zero p a hpa
  have h1 : seqVar (seqEval a (sturmSeq p q)) = seqVar (seqEval a' (sturmSeq p q)) := by
    apply changes_smods_congr p q a a'
    · exact ne_of_lt haa'
    · exact hpa
    · intros p' hp' x hx
      apply no_root p' hp'
      left
      cases hx
      next hx => exact hx
      next hx => linarith
  have h2 : seqVar (seqEval b (sturmSeq p q)) = seqVar (seqEval b' (sturmSeq p q)) := by
    apply changes_smods_congr p q b b'
    · exact Ne.symm (ne_of_lt hb'b)
    · exact hpb
    · intros p' hp' x hx
      apply no_root p' hp'
      right
      cases hx
      next hx => linarith
      next hx => exact hx
  unfold seqVarSturm_ab
  unfold seqVar_ab
  rw [h1, h2]

@[simp]
def rootsInSet (p : Polynomial ℝ) (S : Set ℝ) : Finset ℝ :=
  p.roots.toFinset.filter (fun x => x ∈ S)

lemma rootsInSet_interval (p : Polynomial ℝ) (a b : ℝ) :
    rootsInInterval p a b = rootsInSet p (Set.Ioo a b) := by simp [rootsInInterval]

lemma rootsInSet_cup (p : Polynomial ℝ) (S T : Set ℝ) :
    rootsInSet p S ∪ rootsInSet p T = rootsInSet p (S ∪ T) := by
  simp
  exact Finset.filter_union_right (fun x => x ∈ S) (fun x => x ∈ T) p.roots.toFinset

lemma Ioc_Ioo (a b c : ℝ) (hab : a ≤ b) (hbc : b < c) : Ioc a b ∪ Ioo b c = Ioo a c := by
  exact Ioc_union_Ioo_eq_Ioo hab hbc

lemma non_empty_element {α : Type} (S : Finset α) : ¬ S = ∅ → ∃ x : α, x ∈ S := by
  intro non_empty
  exact Finset.nonempty_iff_ne_empty.mpr non_empty

lemma cindex_poly_congr (p q : Polynomial ℝ) (a a' b b' : ℝ) (haa' : a < a') (hb'b : b' < b) (ha'b' : a' < b')
    (hpx : ∀ x : ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) → eval x p ≠ 0) :
    cauchyIndex p q a b = cauchyIndex p q a' b' := by
  unfold cauchyIndex
  have : rootsInInterval p a b = rootsInInterval p a' b' := by
    rw [rootsInSet_interval]
    rw [rootsInSet_interval]
    have : Ioo a b = Ioc a a' ∪ Ioo a' b' ∪ Ico b' b := by
      rw [Ioc_union_Ioo_eq_Ioo (le_of_lt haa') ha'b']
      rw [Ioo_union_Ico_eq_Ioo (gt_trans ha'b' haa') (le_of_lt hb'b)]
    rw [this, <- rootsInSet_cup, <- rootsInSet_cup]
    have : rootsInSet p (Ioc a a') = ∅ := by
      by_contra!
      simp at this
      obtain ⟨x, hx⟩ : ∃ x : ℝ, x ∈ {x ∈ p.roots.toFinset | a < x ∧ x ≤ a'} := non_empty_element _ this
      simp at hx
      obtain ⟨⟨hx11, hx12⟩, hx2, hx3⟩ := hx
      have := hpx x (Or.inl (And.intro hx2 hx3))
      exact this hx12
    rw [this]
    have : rootsInSet p (Ico b' b) = ∅ := by
      by_contra!
      simp at this
      obtain ⟨x, hx⟩ : ∃ x : ℝ, x ∈ {x ∈ p.roots.toFinset | b' ≤ x ∧ x < b} := non_empty_element _ this
      simp at hx
      obtain ⟨⟨hx11, hx12⟩, hx2, hx3⟩ := hx
      have := hpx x (Or.inr (And.intro hx2 hx3))
      exact this hx12
    rw [this]
    simp
  rw [this]

-- cindex_poly_changes_itv_mods
-- Talvez usar reais extendidos para a e b seja a tradução mais imediata do enunciado.
-- Por enquanto, podemos seguir desconsiderando esse caso.
theorem B_2_58 (p q: Polynomial ℝ) (a b : ℝ) (hpa: p.eval a ≠ 0) (hpb : p.eval b ≠ 0) (hab : a < b) :
    seqVarSturm_ab p q a b = cauchyIndex p q a b := by
  induction h: (sturmSeq p q) generalizing p q a b with
  | nil =>
    unfold seqVarSturm_ab
    rw [h]
    simp [seqVar_ab, seqVar, seqEval]
    have := (smod_nil_eq p q).mp h
    rw [this]
    simp [cauchyIndex, rootsInInterval]
   | cons hd tl ih =>
      have : p ≠ 0 := eval_non_zero p a hpa
      have ⟨a', b', haa', ha'b', hbb', hn_root⟩ := B_2_58_aux p q a b hab
      if H: q = 0 then simp [H]
      else
        let r := (-p % q)
        have ⟨ps, hps, hpsqr, htlps⟩: ∃ps : List (Polynomial ℝ), sturmSeq p q = p :: q :: ps ∧ sturmSeq q r = q :: ps ∧ tl = q :: ps := by
          have ⟨hhd, haux1⟩: p = hd ∧ sturmSeq q (-p % q) = tl := by
            unfold sturmSeq at h
            simp [this] at h
            exact h
          have haux2: q :: sturmSeq (-p % q) (-q % (-p % q)) = tl := by
            unfold sturmSeq at haux1
            simp [H] at haux1
            exact haux1
          let ps := sturmSeq (-p % q) (-q % (-p % q))
          use ps
          unfold ps r;
          simp [haux1, haux2, h]
          exact (Eq.symm hhd)
        have ⟨hpa', hpb', hqa', hqb'⟩ : eval a' p ≠ 0 ∧ eval b' p ≠ 0 ∧  eval a' q ≠ 0 ∧ eval b' q ≠ 0 := by aesop
        have t0 : a' < b' := by linarith
        rw[htlps] at ih
        have h_ind := ih q r a' b' hqa' hqb' t0 hpsqr
        -- r = -p%q

        have : (∀ p' ∈ sturmSeq p q, ∀ (x : ℝ), a < x ∧ x ≤ a' ∨ b' ≤ x ∧ x < b → eval x p' ≠ 0) :=
          fun p' a_1 x a => hn_root p' a_1 x a
        have h_congr_seqvar := changes_itv_smods_congr p q a a' b b' hpa hpb haa' hbb' this
        rw[h_congr_seqvar]

        have : (∀ (x : ℝ), a < x ∧ x ≤ a' ∨ b' ≤ x ∧ x < b → eval x p ≠ 0) := by
          intro x hx
          rcases hn_root p (by rw [hps]; simp) x hx with hneq
          exact hneq
        have h_congr_cindex := cindex_poly_congr p q a a' b b' haa' hbb' t0 this
        rw[h_congr_cindex]

        have t1 : eval a' (p * q) ≠ 0 := by
          simp [Polynomial.eval_mul, hpa', hqa']
        have t2 : eval b' (p * q) ≠ 0 := by
          simp [Polynomial.eval_mul, hpb', hqb']
        have h_cindex := B_2_60 p q a' b' ha'b' t1 t2
        rw[h_cindex]
        have h_changes_itv := changes_itv_smods_rec ha'b' t1 t2
        rw[h_changes_itv]
        rw[h_ind]

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

theorem L_2_59 (a b : ℝ) (p q : Polynomial ℝ) (hq : q ≠ 0) (hp : p ≠ 0):
      ((∀p' ∈ sturmSeq p q, ¬IsRoot p' a) ∧ (∀p' ∈ sturmSeq p q, ¬IsRoot p' b))
      → if sigma b (p*q) * sigma a (p*q) = 1 then (seqVarSturm_ab p q a b)
      =  seqVarSturm_ab q (-p%q) a b else seqVarSturm_ab p q a b
      =  sigma b (p*q) + seqVarSturm_ab q (-p%q) a b := by
  intro h
  if hprod : sigma b (p*q) * sigma a (p*q) = 1 then
    simp_all
    exact L_2_59_2 a b p q hprod hq hp h
  else
    simp_all
    have hneg : sigma b (p*q) * sigma a (p*q) = -1 := by
      have aux1 : sigma b (p*q) * sigma a (p*q) ≠ 1 := by intro H; exact hprod H
      have auxevb : eval b (p*q) ≠ 0 := by
        intro Heval
        have aux := And.right h
        have t1: ¬ eval b p = 0 := by
          apply aux p; rw[sturmSeq]; simp; exact hp
        have t2: ¬ eval b q = 0 := by
          apply aux q; rw[sturmSeq, sturmSeq];
          simp
          if hq0 : q = p then
            rw[hq0]; simp; exact hp
          else
          simp_all
        rw[eval_mul] at Heval
        exact (mul_ne_zero t1 t2) Heval
      have auxeva : eval a (p*q) ≠ 0 := by
            intro Heval
            have aux := And.left h
            have t1: ¬ eval a p = 0 := by
              apply aux p; rw[sturmSeq]; simp; exact hp
            have t2: ¬ eval a q = 0 := by
              apply aux q; rw[sturmSeq, sturmSeq];
              simp
              if hq0 : q = p then
                rw[hq0]; simp; exact hp
              else
                simp_all
            rw[eval_mul] at Heval
            exact (mul_ne_zero t1 t2) Heval
      have aux2 : sigma b (p*q) * sigma a (p*q) ≠ 0 := by
        intro H
        have T1 : sigma b (p*q) ≠ 0 := by
          intro Haux
          have := auxevb
          rw[sigma] at Haux
          simp [sgn] at Haux; simp_all; split_ifs at Haux
          if hnew : 0 < eval b p * eval b q then
            linarith
          else
            linarith
        have T2 : sigma a (p*q) ≠ 0 := by
          intro Haux
          have := auxeva
          rw[sigma] at Haux; simp [sgn] at Haux;
          simp_all; split_ifs at Haux
          if hnew : 0 < eval a p * eval a q then
            linarith
          else
            linarith
        exact (mul_ne_zero T1 T2) H
      simp_all; rw[sigma, sigma]; simp [sigma] at aux1 aux2
      rw[sgn,sgn] at aux1; rw[sgn,sgn] at aux2; rw[sgn,sgn]; simp_all
      if h1a : 0 < eval a p * eval a q then
        have : eval b p * eval b q < 0 := by
          have t0bpq : eval b p * eval b q > 0 → False := by
            intro Haux; simp [h1a, Haux] at aux1;
          have t1bpq : eval b p * eval b q = 0 → False := by
            exact mul_ne_zero (And.left auxevb) (And.right auxevb)
          have h : ¬(eval b p * eval b q > 0) := t0bpq
          have h0 : ¬(eval b p * eval b q = 0) := t1bpq
          classical
          have tri := lt_trichotomy (eval b p * eval b q) 0
          cases tri with
          | inl hlt => exact hlt               -- caso < 0, é o que queremos
          | inr h =>
            cases h with
            | inl heq => exfalso; exact (h0 heq)     -- caso = 0 → contradição
            | inr hgt => exfalso; exact (t0bpq hgt)     -- caso > 0 → contradição
        simp_all
      else
        have a1 : eval b p * eval b q > 0 := by
          have : (-if 0 < eval b p * eval b q then 1 else -1) = 1 ↔ ¬(0 < eval b p * eval b q) := by
            by_cases hpos : 0 < eval b p * eval b q
            · simp [hpos]
            · simp [hpos]
          simp_all
        have a2 : eval a p * eval a q < 0 := by
          simp_all
          have hp := auxeva.left
          have hq := auxeva.right
          have hne : eval a p * eval a q ≠ 0 := by
            intro hzero
            have : eval a p = 0 ∨ eval a q = 0 := by
              apply mul_eq_zero.mp;exact hzero
            cases this with
            | inl hp0 => exact hp hp0
            | inr hq0 => exact hq hq0
          exact lt_of_le_of_ne h1a hne
        simp_all
    exact L_2_59_1 a b p q hneg hq hp h

