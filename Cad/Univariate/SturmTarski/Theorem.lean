import Mathlib
import Cad.Univariate.SturmTarski.SturmSeq

open Polynomial SignType

namespace Theorem

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

/-! ### Pushing an interval endpoint to infinity

Once `ub` is beyond every root of `p`, the roots above `a` are the roots in `(a, ub)`; and once
`ub` is beyond every root of a sequence, the signs of the sequence at `ub` are its signs at `+∞`.
Symmetrically for lower bounds. -/

lemma rootsAbove_eq_rootsInInterval {p : Polynomial ℝ} {a ub : ℝ} (h : ∀ x, eval x p = 0 → x < ub) :
    rootsAbove p a = rootsInInterval p a ub := by
  ext z
  simp only [rootsAbove, rootsInInterval, Finset.mem_filter, Multiset.mem_toFinset, mem_roots',
    IsRoot.def, Set.mem_Ioo, gt_iff_lt]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, h z h1.2⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩

lemma rootsBelow_eq_rootsInInterval {p : Polynomial ℝ} {b lb : ℝ} (h : ∀ x, eval x p = 0 → lb < x) :
    rootsBelow p b = rootsInInterval p lb b := by
  ext z
  simp only [rootsBelow, rootsInInterval, Finset.mem_filter, Multiset.mem_toFinset, mem_roots',
    IsRoot.def, Set.mem_Ioo]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h z h1.2, h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩

lemma roots_toFinset_eq_rootsInInterval {p : Polynomial ℝ} {lb ub : ℝ}
    (hlb : ∀ x, eval x p = 0 → lb < x) (hub : ∀ x, eval x p = 0 → x < ub) :
    p.roots.toFinset = rootsInInterval p lb ub := by
  ext z
  simp only [rootsInInterval, Finset.mem_filter, Multiset.mem_toFinset, mem_roots', IsRoot.def,
    Set.mem_Ioo]
  exact ⟨fun h1 => ⟨h1, hlb z h1.2, hub z h1.2⟩, fun ⟨h1, _, _⟩ => h1⟩

lemma seq_sign_pos_inf_eq_seqEvalSign {ub : ℝ} {ps : List (Polynomial ℝ)}
    (key : ∀ pp ∈ ps, sign (eval ub pp) = sign_pos_inf pp) :
    seq_sign_pos_inf ps = seqEvalSign ub ps :=
  List.map_congr_left fun pp hpp => (key pp hpp).symm

lemma seq_sign_neg_inf_eq_seqEvalSign {lb : ℝ} {ps : List (Polynomial ℝ)}
    (key : ∀ pp ∈ ps, sign (eval lb pp) = sign_neg_inf pp) :
    seq_sign_neg_inf ps = seqEvalSign lb ps :=
  List.map_congr_left fun pp hpp => (key pp hpp).symm

lemma mem_sturmSeq_self {p q : Polynomial ℝ} (hp : p ≠ 0) : p ∈ sturmSeq p q := by
  rw [sturmSeq_cons hp]; exact List.mem_cons_self

theorem sturm_tarski_interval (a b : ℝ) (p q : Polynomial ℝ) (hab : a < b) (hpa : eval a p ≠ 0) (hpb : eval b p ≠ 0) :
    tarskiQuery p q a b = signVariationsSturm_ab p (derivative p * q) a b := by
  rw [cauchyIndex_sturmSeq p (derivative p * q) a b hpa hpb hab]
  rw [cauchyIndex_poly_taq p q a b]

theorem sturm_tarski_above (a : ℝ) (p q : Polynomial ℝ) (hpa : eval a p ≠ 0) :
    tarskiQuery_above p q a = signVariationsAboveSturm p (derivative p * q) a := by
  obtain ⟨ub, hroots, hab, hsign⟩ :=
    root_list_ub (sturmSeq p (derivative p * q)) a (no_zero_in_sturmSeq _ _)
  have hp_mem := mem_sturmSeq_self (q := derivative p * q) (eval_non_zero p a hpa)
  have hpub : eval ub p ≠ 0 := fun h => lt_irrefl ub (hroots p hp_mem ub h)
  have taq : tarskiQuery_above p q a = tarskiQuery p q a ub := by
    unfold tarskiQuery_above tarskiQuery
    rw [rootsAbove_eq_rootsInInterval (hroots p hp_mem)]
  rw [taq, sturm_tarski_interval a ub p q hab hpa hpub, signVariationsAboveSturm,
    signVariationsAbove_a, signVariationsSturm_ab, signVariations_ab,
    seq_sign_pos_inf_eq_seqEvalSign (hsign ub le_rfl), signVariationsSign _ ub]

theorem sturm_tarski_below (b : ℝ) (p q : Polynomial ℝ) (hpb : eval b p ≠ 0) :
    tarskiQuery_below p q b = signVariationsBelowSturm p (derivative p * q) b := by
  obtain ⟨lb, hroots, hlb, hsign⟩ :=
    root_list_lb (sturmSeq p (derivative p * q)) b (no_zero_in_sturmSeq _ _)
  have hp_mem := mem_sturmSeq_self (q := derivative p * q) (eval_non_zero p b hpb)
  have hplb : eval lb p ≠ 0 := fun h => lt_irrefl lb (hroots p hp_mem lb h)
  have taq : tarskiQuery_below p q b = tarskiQuery p q lb b := by
    unfold tarskiQuery_below tarskiQuery
    rw [rootsBelow_eq_rootsInInterval (hroots p hp_mem)]
  rw [taq, sturm_tarski_interval lb b p q hlb hplb hpb, signVariationsBelowSturm,
    signVariationsBelow_b, signVariationsSturm_ab, signVariations_ab,
    seq_sign_neg_inf_eq_seqEvalSign (hsign lb le_rfl), signVariationsSign _ lb]

theorem sturm_tarski_R (p q : Polynomial ℝ) :
    tarskiQuery_R p q = signVariationsLineSturm p (derivative p * q) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [tarskiQuery_R, signVariationsLineSturm, signVariationsLine, seq_sign_neg_inf,
      seq_sign_pos_inf, sturmSeq_zero]
  obtain ⟨lb, hroots_lb, hlb, hsign_lb⟩ :=
    root_list_lb (sturmSeq p (derivative p * q)) 0 (no_zero_in_sturmSeq _ _)
  obtain ⟨ub, hroots_ub, hub, hsign_ub⟩ :=
    root_list_ub (sturmSeq p (derivative p * q)) 0 (no_zero_in_sturmSeq _ _)
  have hp_mem := mem_sturmSeq_self (q := derivative p * q) hp
  have hplb : eval lb p ≠ 0 := fun h => lt_irrefl lb (hroots_lb p hp_mem lb h)
  have hpub : eval ub p ≠ 0 := fun h => lt_irrefl ub (hroots_ub p hp_mem ub h)
  have taq : tarskiQuery_R p q = tarskiQuery p q lb ub := by
    unfold tarskiQuery_R tarskiQuery
    rw [roots_toFinset_eq_rootsInInterval (hroots_lb p hp_mem) (hroots_ub p hp_mem)]
  rw [taq, sturm_tarski_interval lb ub p q (by linarith) hplb hpub, signVariationsLineSturm,
    signVariationsLine, signVariationsSturm_ab, signVariations_ab,
    seq_sign_neg_inf_eq_seqEvalSign (hsign_lb lb le_rfl),
    seq_sign_pos_inf_eq_seqEvalSign (hsign_ub ub le_rfl), signVariationsSign _ lb,
    signVariationsSign _ ub]

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
