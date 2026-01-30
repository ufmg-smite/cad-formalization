import Mathlib
import Cad.SturmBasu.Theorem
import Cad.SturmBasu.Utils

noncomputable section

open Polynomial

theorem sturm_tarski_interval (a b : ℝ) (p q : Polynomial ℝ) (hab : a < b) (hpa : eval a p ≠ 0) (hpb : eval b p ≠ 0) :
    tarskiQuery p q a b = seqVarSturm_ab p (derivative p * q) a b := by
  have : p ≠ 0 := eval_non_zero p a hpa
  rw [B_2_58 p (derivative p * q) a b hpa hpb hab]
  rw [B_2_57 p q a b hab]

def rootsAbove (f : Polynomial ℝ) (a : ℝ) : Finset ℝ :=
  f.roots.toFinset.filter (fun x => x > a)

def tarskiQuery_above (p q : Polynomial ℝ) (a : ℝ) : ℤ :=
  ∑ x ∈ rootsAbove p a, sgn (q.eval x)

theorem sturm_tarski_above (a : ℝ) (p q : Polynomial ℝ) (hpa : eval a p ≠ 0) :
    tarskiQuery_above p q a = seqVarAboveSturm p q a := by
  let ps := sturmSeq p (derivative p * q)
  have : p ≠ 0 := eval_non_zero p a hpa
  have : p ∈ ps := by
    unfold ps
    unfold sturmSeq
    simp [this]
  obtain ⟨ub, hub1, hub2, hub3⟩ : ∃ ub,
      (∀ pp ∈ ps, (∀ x, eval x pp = 0 → x < ub)) ∧
      a < ub ∧
      (∀ x, x ≥ ub → (∀ pp ∈ ps, sgn (eval x pp) = sgn_pos_inf pp)) := by
    apply root_list_ub
    exact no_zero_in_sturmSeq p (derivative p * q)
  have taq_taq : tarskiQuery_above p q a = tarskiQuery p q a ub := by
    unfold tarskiQuery_above
    unfold tarskiQuery
    congr
    unfold rootsAbove
    unfold rootsInInterval
    ext z
    simp only [gt_iff_lt, Finset.mem_filter, Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def,
      Set.mem_Ioo, and_congr_right_iff, iff_self_and, and_imp]
    aesop
  have changes_changes : seqVarAboveSturm p q a = seqVarSturm_ab p q a ub := by
    unfold seqVarSturm_ab
    unfold seqVarAboveSturm
    unfold seqVarAbove_a
    unfold seqVar_ab
    simp
    admit

  admit
