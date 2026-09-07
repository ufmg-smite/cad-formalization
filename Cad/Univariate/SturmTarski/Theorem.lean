import Mathlib
import Cad.Univariate.SturmTarski.SturmSeq

open Polynomial SignType

namespace Theorem

theorem sturm_tarski_interval (a b : ℝ) (p q : Polynomial ℝ) (hab : a < b) (hpa : eval a p ≠ 0) (hpb : eval b p ≠ 0) :
    tarskiQuery p q a b = signVariationsSturm_ab p (derivative p * q) a b := by
  rw [cauchyIndex_sturmSeq p (derivative p * q) a b hpa hpb hab]
  rw [cauchyIndex_poly_taq p q a b]

noncomputable def rootsAbove (f : Polynomial ℝ) (a : ℝ) : Finset ℝ :=
  f.roots.toFinset.filter (fun x => x > a)

noncomputable def tarskiQuery_above (p q : Polynomial ℝ) (a : ℝ) : ℤ :=
  ∑ x ∈ rootsAbove p a, sign (q.eval x)

noncomputable def rootsBelow (f : Polynomial ℝ) (b : ℝ) : Finset ℝ :=
  f.roots.toFinset.filter (fun x => x < b)

noncomputable def tarskiQuery_below (p q : Polynomial ℝ) (b : ℝ) : ℤ :=
  ∑ x ∈ rootsBelow p b, sign (q.eval x)

noncomputable def tarskiQuery_R (p q : Polynomial ℝ) : ℤ :=
  ∑ x ∈ p.roots.toFinset, sign (q.eval x)

lemma seq_sign_pos_inf_seqEvalsign (ub : ℝ) (ps : List (Polynomial ℝ)) (key : ∀ x ≥ ub, ∀ pp ∈ ps, sign (eval x pp) = sign_pos_inf pp) :
    seq_sign_pos_inf ps = seqEvalSign ub ps := by
  cases ps
  next => simp only [seq_sign_pos_inf, seqEvalSign, List.map]
  next hd tl =>
    simp only [seq_sign_pos_inf, seqEvalSign, List.cons.injEq, List.map]
    constructor
    · apply Eq.symm
      apply key
      · exact Preorder.le_refl ub
      · exact List.mem_cons_self
    · apply seq_sign_pos_inf_seqEvalsign ub tl
      intros x hx pp hpp
      apply key
      · exact hx
      · exact List.mem_cons_of_mem hd hpp

theorem sturm_tarski_above (a : ℝ) (p q : Polynomial ℝ) (hpa : eval a p ≠ 0) :
    tarskiQuery_above p q a = signVariationsAboveSturm p (derivative p * q) a := by
  let ps := sturmSeq p (derivative p * q)
  have ps_def : ps = sturmSeq p (derivative p * q) := rfl
  have : p ≠ 0 := eval_non_zero p a hpa
  have : p ∈ ps := by
    unfold ps sturmSeq
    simp [this]
  obtain ⟨ub, hub1, hub2, hub3⟩ : ∃ ub,
      (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x < ub)) ∧
      a < ub ∧
      (∀ x, x ≥ ub → (∀ pp ∈ ps, sign (eval x pp) = sign_pos_inf pp)) := by
    apply root_list_ub
    exact no_zero_in_sturmSeq p (derivative p * q)
  have taq_taq : tarskiQuery_above p q a = tarskiQuery p q a ub := by
    simp only [tarskiQuery_above, tarskiQuery]
    congr
    simp only [rootsAbove, rootsInInterval]
    ext z
    simp only [gt_iff_lt, Finset.mem_filter, Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def,
      Set.mem_Ioo, and_congr_right_iff, iff_self_and, and_imp]
    intro a_1 a_2 a_3
    simp_all only [ne_eq, not_false_eq_true, ge_iff_le, ps]
    apply hub1
    on_goal 2 => { exact a_2 }
    · simp_all only
  have changes_changes : signVariationsAboveSturm p (derivative p * q) a = signVariationsSturm_ab p (derivative p * q) a ub := by
    simp [signVariationsSturm_ab, signVariationsAboveSturm, signVariationsAbove_a, signVariations_ab]
    rw [signVariationsSign, <- ps_def, seq_sign_pos_inf_seqEvalsign ub ps hub3]
  rw [taq_taq, changes_changes]
  apply sturm_tarski_interval _ _ _ _ hub2 hpa
  intro abs
  have := hub1 p this ub abs
  simp at this

lemma seq_sign_neg_inf_seqEvalsign (lb : ℝ) (ps : List (Polynomial ℝ)) (key : ∀ x ≤ lb, ∀ pp ∈ ps, sign (eval x pp) = sign_neg_inf pp) :
    seq_sign_neg_inf ps = seqEvalSign lb ps := by
  cases ps
  next => simp only [seq_sign_neg_inf, seqEvalSign, List.map]
  next hd tl =>
    simp only [seq_sign_neg_inf, seqEvalSign, List.cons.injEq, List.map]
    constructor
    · apply Eq.symm
      exact key _ (Preorder.le_refl lb) _ List.mem_cons_self
    · apply seq_sign_neg_inf_seqEvalsign lb tl
      intros x hx pp hpp
      exact key _ hx _ (List.mem_cons_of_mem hd hpp)

theorem sturm_tarski_below (b : ℝ) (p q : Polynomial ℝ) (hpa : eval b p ≠ 0) :
    tarskiQuery_below p q b = signVariationsBelowSturm p (derivative p * q) b := by
  let ps := sturmSeq p (derivative p * q)
  have ps_def : ps = sturmSeq p (derivative p * q) := rfl
  have : p ≠ 0 := eval_non_zero p b hpa
  have : p ∈ ps := by
    unfold ps sturmSeq
    simp [this]
  obtain ⟨lb, hlb1, hlb2, hlb3⟩ : ∃ lb,
      (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x > lb)) ∧
      b > lb ∧
      (∀ x, x ≤ lb → (∀ pp ∈ ps, sign (eval x pp) = sign_neg_inf pp)) := by
    apply root_list_lb
    exact no_zero_in_sturmSeq p (derivative p * q)
  have taq_taq : tarskiQuery_below p q b = tarskiQuery p q lb b := by
    simp [tarskiQuery_below, tarskiQuery]
    congr
    simp [rootsBelow, rootsInInterval]
    ext z
    simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def,
      and_congr_right_iff, iff_and_self, and_imp]
    intro a a_1 a_2
    simp_all only [ne_eq, not_false_eq_true, gt_iff_lt, ps]
    apply hlb1
    on_goal 2 => { exact a_1 }
    simp_all only
  have changes_changes : signVariationsBelowSturm p (derivative p * q) b = signVariationsSturm_ab p (derivative p * q) lb b := by
    simp [signVariationsSturm_ab, signVariationsBelowSturm, signVariationsBelow_b, signVariations_ab]
    rw [signVariationsSign, <- ps_def, seq_sign_neg_inf_seqEvalsign lb ps hlb3]
  rw [taq_taq, changes_changes]
  apply sturm_tarski_interval _ _ _ _ hlb2 _ hpa
  intro abs
  have := hlb1 p this lb abs
  simp at this

theorem sturm_tarski_R (p q : Polynomial ℝ) :
    tarskiQuery_R p q = signVariationsLineSturm p (derivative p * q) := by
  if hp: p = 0 then
    rw [hp]
    simp [tarskiQuery_R, signVariationsLineSturm, signVariationsLine, seq_sign_neg_inf, seq_sign_pos_inf]
  else
    let ps := sturmSeq p (derivative p * q)
    have ps_def : ps = sturmSeq p (derivative p * q) := rfl
    have : p ∈ ps := by
      unfold ps sturmSeq
      simp [hp]
    obtain ⟨lb, hlb1, hlb2, hlb3⟩ : ∃ lb,
        (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x > lb)) ∧
        0 > lb ∧
        (∀ x, x ≤ lb → (∀ pp ∈ ps, sign (eval x pp) = sign_neg_inf pp)) := by
      apply root_list_lb
      exact no_zero_in_sturmSeq p (derivative p * q)
    obtain ⟨ub, hub1, hub2, hub3⟩ : ∃ ub,
        (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x < ub)) ∧
        0 < ub ∧
        (∀ x, x ≥ ub → (∀ pp ∈ ps, sign (eval x pp) = sign_pos_inf pp)) := by
      apply root_list_ub
      exact no_zero_in_sturmSeq p (derivative p * q)
    have taq_taq : tarskiQuery_R p q = tarskiQuery p q lb ub := by
      simp [tarskiQuery_R, tarskiQuery]
      congr
      unfold rootsInInterval
      ext z
      simp only [Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def, Set.mem_Ioo,
        Finset.mem_filter, iff_self_and, and_imp]
      intro a a_1
      simp_all only [not_false_eq_true, gt_iff_lt, ge_iff_le, ps]
      apply And.intro
      · apply hlb1
        on_goal 2 => { exact a_1 }
        · simp_all only
      · apply hub1
        · exact this
        · simp_all only
    have changes_changes : signVariationsLineSturm p (derivative p * q) = signVariationsSturm_ab p (derivative p * q) lb ub := by
      simp [signVariationsLineSturm, signVariationsLine, signVariationsSturm_ab, signVariations_ab]
      rw [ signVariationsSign
         , signVariationsSign
         , <- ps_def
         , seq_sign_neg_inf_seqEvalsign lb ps hlb3
         , seq_sign_pos_inf_seqEvalsign ub ps hub3
         ]
    have lb_neq_0 : eval lb p ≠ 0 := by
      intro abs
      have := hlb1 p this lb abs
      simp at this
    have ub_neq_0 : eval ub p ≠ 0 := by
      intro abs
      have := hub1 p this ub abs
      simp at this
    have lb_ub : lb < ub := by linarith
    rw [taq_taq, changes_changes]
    exact sturm_tarski_interval lb ub p q lb_ub lb_neq_0 ub_neq_0

theorem sturm_interval (a b : ℝ) (p : Polynomial ℝ) (hab : a < b) (hpa : eval a p ≠ 0) (hpb : eval b p ≠ 0) :
    Finset.card (rootsInInterval p a b) = signVariationsSturm_ab p (derivative p) a b := by
  have := sturm_tarski_interval a b p 1 hab hpa hpb
  simp [tarskiQuery, sign] at this
  exact this

theorem sturm_above (a : ℝ) (p : Polynomial ℝ) (hpa : eval a p ≠ 0) :
    Finset.card (rootsAbove p a) = signVariationsAboveSturm p (derivative p) a := by
  have := sturm_tarski_above a p 1 hpa
  simp [tarskiQuery_above, sign] at this
  exact this

theorem sturm_below (b : ℝ) (p : Polynomial ℝ) (hpa : eval b p ≠ 0) :
    Finset.card (rootsBelow p b) = signVariationsBelowSturm p (derivative p) b := by
  have := sturm_tarski_below b p 1 hpa
  simp [tarskiQuery_below, sign] at this
  exact this

theorem sturm_R (p : Polynomial ℝ) :
    Finset.card p.roots.toFinset = signVariationsLineSturm p (derivative p) := by
  have := sturm_tarski_R p 1
  simp [tarskiQuery_R, sign] at this
  exact this

end Theorem
