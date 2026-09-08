import Mathlib

import Cad.Univariate.SturmTarski.CauchyIndex

open Polynomial Set Filter Classical SignType

noncomputable section

lemma no_zero_in_sturmSeq (p q : Polynomial ℝ) : 0 ∉ sturmSeq p q := by
  induction p, q using sturmSeq.induct
  next p => simp [sturmSeq]
  next p q h_zero IH =>
    have h_zero' : ¬ 0 = p := Ne.intro fun a => h_zero (Eq.symm a)
    rw [sturmSeq_cons h_zero]
    simp [h_zero', IH]

@[simp] lemma SignType.sign_cast {β : Type*} [Ring β] [LinearOrder β] [IsStrictOrderedRing β]
    (s : SignType) : sign (s : β) = s := by
  cases s <;> simp [sign_neg]

lemma sign_intCast_sign {α : Type*} [Zero α] [LinearOrder α] (a : α) :
    sign ((sign a : SignType) : ℤ) = sign a :=
  SignType.sign_cast _

lemma signVariationsSign : ∀ ps : List (Polynomial ℝ), ∀ (k : ℝ), List.signVariations (seqEval k ps) = List.signVariations (seqEvalSign k ps) := by
  intro ps k
  have : seqEvalSign k ps = (seqEval k ps).map (fun x => ((sign x : SignType) : ℤ)) := by
    simp only [seqEvalSign, seqEval, List.map_map, Function.comp_def]
  rw [this, List.signVariations_map sign_intCast_sign]

lemma smod_nil_eq (p q : Polynomial Real) :
    sturmSeq p q = [] ↔ p = 0 := by
  constructor
  · intro hs
    by_contra!
    rw [sturmSeq_cons this] at hs
    trivial
  · intro hp
    rw [hp]
    exact sturmSeq_zero (q := q)

@[simp]
lemma smods_s_0_1 (p: Polynomial ℝ) : sturmSeq 0 p = [] := (smod_nil_eq 0 p).mpr rfl

@[simp]
lemma smods_s_0_2 (p: Polynomial ℝ) : sturmSeq p 0 = if p = 0 then [] else [p] := by
  split_ifs with H
  · exact (smod_nil_eq p 0).mpr H
  · rw [sturmSeq_cons H, sturmSeq_zero]

@[simp]
theorem seqVarSturm_ab_z_1 (p: Polynomial ℝ) (a b: ℝ) : signVariationsSturm_ab 0 p a b = 0 := by
  simp [signVariationsSturm_ab, signVariations_ab]

@[simp]
theorem seqVarSturm_ab_z_2 (p: Polynomial ℝ) (a b: ℝ) : signVariationsSturm_ab p 0 a b = 0 := by
  if H: p = 0 then simp [H]
  else
    simp [signVariationsSturm_ab, signVariations_ab, seqEval, H]
    rw [List.signVariations_singleton, List.signVariations_singleton]
    norm_num

lemma cauchyIndex_poly_taq (p q : Polynomial ℝ) (a b : ℝ) :
    tarskiQuery p q a b = cauchyIndex p (derivative p * q) a b := by
  if hp : p = 0 then
    simp_rw [hp, tarskiQuery, cauchyIndex, rootsInIntervalZero]
    norm_num
  else
    unfold tarskiQuery cauchyIndex
    apply Finset.sum_congr rfl
    intros x hx
    have : p.eval x = 0 := by
      simp [rootsInInterval] at hx
      exact hx.1.2
    rw [jump_poly_sign p q x hp this]

/-- For nonzero reals, "same sign" versus "product negative", as `signVariations` uses the former
and the Sturm proofs reason with the latter. -/
lemma ite_sign_eq {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (if sign x = sign y then (0 : ℕ) else 1) = if x * y < 0 then 1 else 0 := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy
  · simp [sign_neg hx, sign_neg hy, le_of_lt (mul_pos_of_neg_of_neg hx hy)]
  · simp [sign_neg hx, sign_pos hy, mul_neg_of_neg_of_pos hx hy]
  · simp [sign_pos hx, sign_neg hy, mul_neg_of_pos_of_neg hx hy]
  · simp [sign_pos hx, sign_pos hy, le_of_lt (mul_pos hx hy)]

theorem changes_itv_smods_rec {a b: ℝ} {p q: Polynomial ℝ} (hpqa: eval a (p * q)≠ 0) (hpqb: eval b (p * q) ≠ 0) :
    (signVariationsSturm_ab p q a b) = cross (p * q) a b + signVariationsSturm_ab q (-p%q) a b := by
  if H: p = 0 ∨ q = 0 ∨ p % q = 0 then
    rcases H with h | h | h
    · simp [cross, variation, h]
    · simp [cross, variation, h]
    · unfold signVariationsSturm_ab signVariations_ab seqEval cross sturmSeq
      rw [mod_minus, h]
      have ⟨hap, haq⟩: eval a p ≠ 0 ∧ eval a q ≠ 0 := by simp_all only [eval_mul, ne_eq, mul_eq_zero, not_or,
        EuclideanDomain.mod_eq_zero, not_false_eq_true, and_self]
      have ⟨hbp, hbq⟩: eval b p ≠ 0 ∧ eval b q ≠ 0:= by simp_all only [eval_mul, ne_eq, mul_eq_zero, or_self,
        not_false_eq_true, not_or, EuclideanDomain.mod_eq_zero, and_self]
      have hpz: p ≠ 0 := by
        simp_all only [eval_mul, ne_eq, mul_eq_zero, or_self, not_false_eq_true, EuclideanDomain.mod_eq_zero]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [dvd_zero, eval_zero, not_true_eq_false]
      have hqz: q ≠ 0 := by
        simp_all only [eval_mul, ne_eq, mul_eq_zero, or_self, not_false_eq_true, EuclideanDomain.mod_eq_zero]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [zero_dvd_iff]
      simp [hpz, hqz]
      rw [List.signVariations_cons_cons_of_ne_zero _ _ _ hap haq,
        List.signVariations_cons_cons_of_ne_zero _ _ _ hbp hbq,
        ite_sign_eq hap haq, ite_sign_eq hbp hbq]
      simp only [List.signVariations_singleton]
      split_ifs with h1 h2 h3
      · rw [(variation_cases (eval a p * eval a q) (eval b p * eval b q)).2.2.2 ⟨h1, h2⟩]
        simp
      · have : eval b p * eval b q > 0 := by
          rw [eval_mul] at hpqb
          rw [not_lt, <-ge_iff_le] at h2
          exact lt_of_le_of_ne h2 (Ne.symm hpqb)
        rw [(variation_cases (eval a p * eval a q) (eval b p * eval b q)).2.2.1 ⟨h1, this⟩]
        simp
      · have : eval a p * eval a q > 0 := by
          rw [eval_mul] at hpqa
          rw [not_lt, <-ge_iff_le] at h1
          exact lt_of_le_of_ne h1 (Ne.symm hpqa)
        rw [(variation_cases (eval a p * eval a q) (eval b p * eval b q)).2.1 ⟨this, h3⟩]
        simp
      · have : eval a p * eval a q > 0 ∧ eval b p * eval b q > 0 := by
          rw [eval_mul] at hpqa hpqb
          rw [not_lt, <-ge_iff_le] at h1 h3
          exact ⟨lt_of_le_of_ne h1 (Ne.symm hpqa), lt_of_le_of_ne h3 (Ne.symm hpqb)⟩
        rw [(variation_cases (eval a p * eval a q) (eval b p * eval b q)).1 this]
        simp
   else
     simp only [not_or] at H
     have ⟨ps, httl, htlmod⟩ : ∃ ps : List (Polynomial ℝ), sturmSeq p q = p :: q :: -p%q:: ps ∧ sturmSeq q (-p%q) = q :: (-p%q) :: ps := by
       rw [sturmSeq_cons H.1, sturmSeq_cons H.2.1, sturmSeq]
       simp_all
     let changes_diff := fun x => ((List.signVariations (seqEval x (p::q::(-p%q)::ps)): ℤ) - (List.signVariations (seqEval x (q::(-p%q)::ps))): ℤ)
     have hz1: ∀ x: ℝ, (eval x p) * (eval x q) < 0 → changes_diff x = 1 := by
       unfold changes_diff
       intros x hx
       obtain ⟨hxp, hxq⟩ := mul_ne_zero_iff.mp hx.ne
       simp only [seqEval, List.map_cons]
       rw [List.signVariations_cons_cons_of_ne_zero _ _ _ hxp hxq, ite_sign_eq hxp hxq, if_pos hx]
       push_cast
       ring
     have hz2: ∀x, (eval x p) * (eval x q) > 0 → changes_diff x = 0 := by
       unfold changes_diff
       intros x hx
       obtain ⟨hxp, hxq⟩ := mul_ne_zero_iff.mp hx.ne'
       simp only [seqEval, List.map_cons]
       rw [List.signVariations_cons_cons_of_ne_zero _ _ _ hxp hxq, ite_sign_eq hxp hxq, if_neg (not_lt.mpr (le_of_lt hx))]
       push_cast
       ring
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
     unfold signVariationsSturm_ab
     rw [httl, htlmod, ← sub_eq_iff_eq_add]
     unfold signVariations_ab
     ring_nf at hf ⊢
     rw [hf]

theorem cauchyIndex_sturmSeq_aux (p q: Polynomial ℝ) (a b: ℝ) (hab: a < b): ∃ (a' b': ℝ), a < a' ∧ a' < b' ∧ b' < b ∧ (∀p' ∈ sturmSeq p q, (∀ x: ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) -> eval x p' ≠ 0)) := by
  induction p, q using sturmSeq.induct
  next H =>
      let a' := 2/3 * a + 1/3 * b
      let b' := 1/3 * a + 2/3 * b
      have ⟨haa', ha'b', hbb'⟩ : a < a' ∧ a' < b' ∧ b' < b := by constructor <;> grind
      use a', b'
      simp_all only [List.not_mem_nil, ne_eq, not_isEmpty_of_nonempty, IsEmpty.forall_iff,
        implies_true, smods_s_0_1, and_self]
  next p q h_zero IH =>
      let r := - (p % q)
      have ⟨a1, b1, haa1, ha1b1, hbb1, ha1b1_nroot⟩: ∃ (a1 b1: ℝ), a < a1 ∧ a1 < b1 ∧ b1 < b ∧
           (∀p' ∈ sturmSeq q (-p%q), (∀ x: ℝ, ((a < x ∧ x ≤ a1) ∨ (b1 ≤ x ∧ x < b)) -> eval x p' ≠ 0)) := by gcongr
      have ⟨a2, b2, haa2, ha2_nroot, hbb2, hb2_nroot⟩ :
          ∃ (a2 b2: ℝ), a < a2 ∧ (∀x: ℝ, (a < x ∧ x ≤ a2) -> eval x p ≠ 0) ∧
            (b2 < b) ∧ (∀x: ℝ, (b2 ≤ x ∧ x < b) -> eval x p ≠ 0) := by
        have ⟨a2, haa2, ha2_nroot⟩ := next_non_root_interval p a h_zero
        have ⟨b2, hbb2, hb2_nroot⟩ := last_non_root_interval p b h_zero
        use a2, b2
        simp_all
      let a' := if b2 > a then min a1 (min b2 a2) else min a1 a2
      let b' := if a2 < b then max b1 (max a2 b2) else max b1 b2
      have ⟨haa', ha'b', hbb'⟩ : a < a' ∧ a' < b' ∧ b' < b := by grind
      have h_rec: ∀p' ∈ sturmSeq q (-p%q), ∀x: ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b))  -> eval x p' ≠ 0 := by
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
      simp [haa', ha'b', hbb']
      rw [sturmSeq_cons h_zero]
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨h_final, h_rec⟩

lemma cauchyIndex_poly_rec (p q : Polynomial ℝ) (a b: ℝ) (hab : a < b)
    (ha : (p * q).eval a ≠ 0) (hb : (p * q).eval b ≠ 0) :
    cauchyIndex p q a b = cross (p * q) a b + cauchyIndex q (- p % q) a b
    := by
  have H := cindex_poly_inverse_add_cross p q a b hab ha hb
  have : - cauchyIndex q p a b = cauchyIndex q (- p % q) a b := by
    have h1 := cauchyIndex_poly_mod q (-p) a b
    have h2 := cauchyIndex_smult_1 q p a b (-1)
    simp at h2
    rw [<- h2, h1]
  simp only [cross, variation] at *
  linarith

lemma eval_neg_mod {p q : Polynomial ℝ} {x : ℝ} (hq : eval x q = 0) :
    eval x (-p % q) = -eval x p := by
  rw [mod_minus, eval_neg, eval_mod p q x hq]

lemma sign_eq_sign_of_mul_nonneg {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h : 0 ≤ x * y) :
    sign x = sign y := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy
  · rw [sign_neg hx, sign_neg hy]
  · exact absurd h (not_le.mpr (mul_neg_of_neg_of_pos hx hy))
  · exact absurd h (not_le.mpr (mul_neg_of_pos_of_neg hx hy))
  · rw [sign_pos hx, sign_pos hy]

/-- Sign variations across a nonzero entry `t` sitting between `s` and `-s`: exactly one. -/
lemma signType_ite_add_ite (s t : SignType) (hs : s ≠ 0) (ht : t ≠ 0) :
    (if s = t then (0 : ℕ) else 1) + (if t = -s then 0 else 1) = 1 := by
  cases s <;> cases t <;> simp_all

lemma changes_smods_congr (p q : Polynomial ℝ) (a a' : ℝ) (haa' : a ≠ a') (hpa : eval a p ≠ 0)
    (no_root : ∀ p' ∈ sturmSeq p q, ∀ x : ℝ, ((a < x ∧ x ≤ a') ∨ (a' ≤ x ∧ x < a)) → eval x p' ≠ 0) :
    List.signVariations (seqEval a (sturmSeq p q)) = List.signVariations (seqEval a' (sturmSeq p q)) := by
  induction hn : (sturmSeq p q).length using Nat.strong_induction_on generalizing p q with
  | _ n ih =>
  have p_ne : p ≠ 0 := eval_non_zero p a hpa
  -- `a'` lies in the root-free interval, so nothing in the sequence vanishes at `a'`
  have ha' : ∀ pp ∈ sturmSeq p q, eval a' pp ≠ 0 := by
    intro pp hpp
    apply no_root pp hpp
    rcases lt_or_gt_of_ne haa' with h | h
    · exact Or.inl ⟨h, le_rfl⟩
    · exact Or.inr ⟨le_rfl, h⟩
  -- no sign change between `a` and `a'` (intermediate value theorem)
  have hsame : ∀ pp ∈ sturmSeq p q, 0 ≤ eval a pp * eval a' pp := by
    intro pp hpp
    by_contra! hneg
    rcases lt_or_gt_of_ne haa' with h | h
    · obtain ⟨x, hx1, hx2, hx3⟩ := exists_root_ioo_mul (le_of_lt h) hneg
      exact no_root pp hpp x (Or.inl ⟨hx1, le_of_lt hx2⟩) hx3
    · rw [mul_comm] at hneg
      obtain ⟨x, hx1, hx2, hx3⟩ := exists_root_ioo_mul (le_of_lt h) hneg
      exact no_root pp hpp x (Or.inr ⟨le_of_lt hx1, hx2⟩) hx3
  have hsign : ∀ pp ∈ sturmSeq p q, eval a pp ≠ 0 → sign (eval a pp) = sign (eval a' pp) :=
    fun pp hpp h => sign_eq_sign_of_mul_nonneg h (ha' pp hpp) (hsame pp hpp)
  have hS : sturmSeq p q = p :: sturmSeq q (-p % q) := sturmSeq_cons p_ne
  have hp_mem : p ∈ sturmSeq p q := by rw [hS]; exact List.mem_cons_self
  by_cases hq : q = 0
  · -- the sequence is `[p]`
    subst hq
    rw [hS, smods_s_0_1]
    simp [seqEval, List.signVariations_singleton]
  have hS2 : sturmSeq q (-p % q) = q :: sturmSeq (-p % q) (-q % (-p % q)) := sturmSeq_cons hq
  have hq_mem : q ∈ sturmSeq p q := by rw [hS, hS2]; simp
  by_cases hqa : eval a q = 0
  · -- the middle term vanishes at `a`, so its neighbours have opposite signs there
    have hra : eval a (-p % q) = -eval a p := eval_neg_mod hqa
    have hra0 : eval a (-p % q) ≠ 0 := by rw [hra]; exact neg_ne_zero.mpr hpa
    have hS3 : sturmSeq (-p % q) (-q % (-p % q)) =
        (-p % q) :: sturmSeq (-q % (-p % q)) (-(-p % q) % (-q % (-p % q))) :=
      sturmSeq_cons (eval_non_zero _ a hra0)
    have hr_mem : -p % q ∈ sturmSeq p q := by rw [hS, hS2, hS3]; simp
    have hlen : (sturmSeq (-p % q) (-q % (-p % q))).length < n := by
      rw [← hn, hS, hS2]; simp
    have IH := ih _ hlen (-p % q) (-q % (-p % q)) hra0
      (fun pp hpp => no_root pp (by rw [hS, hS2]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hpp))) rfl
    rw [hS3] at IH
    rw [hS, hS2, hS3]
    simp only [seqEval, List.map_cons] at IH ⊢
    rw [hqa, List.signVariations_cons_zero_cons, List.signVariations_cons_cons_of_ne_zero _ _ _ hpa hra0,
      List.signVariations_cons_cons_of_ne_zero _ _ _ (ha' p hp_mem) (ha' q hq_mem),
      List.signVariations_cons_cons_of_ne_zero _ _ _ (ha' q hq_mem) (ha' _ hr_mem),
      ← hsign p hp_mem hpa, ← hsign _ hr_mem hra0, IH, hra, Left.sign_neg, ← add_assoc,
      signType_ite_add_ite _ _ (sign_ne_zero.mpr hpa) (sign_ne_zero.mpr (ha' q hq_mem))]
    simp [hpa]
  · -- the middle term is nonzero at `a`: one step of the sequence
    have hlen : (sturmSeq q (-p % q)).length < n := by rw [← hn, hS]; simp
    have IH := ih _ hlen q (-p % q) hqa
      (fun pp hpp => no_root pp (by rw [hS]; exact List.mem_cons_of_mem _ hpp)) rfl
    rw [hS2] at IH
    rw [hS, hS2]
    simp only [seqEval, List.map_cons] at IH ⊢
    rw [List.signVariations_cons_cons_of_ne_zero _ _ _ hpa hqa,
      List.signVariations_cons_cons_of_ne_zero _ _ _ (ha' p hp_mem) (ha' q hq_mem),
      ← hsign p hp_mem hpa, ← hsign q hq_mem hqa, IH]

lemma changes_itv_smods_congr (p q : Polynomial ℝ) (a a' b b' : ℝ) (hpa : eval a p ≠ 0) (hpb : eval b p ≠ 0)
    (haa' : a < a') (hb'b : b' < b)
    (no_root : ∀ p' ∈ sturmSeq p q, ∀ x : ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) → eval x p' ≠ 0) :
    signVariationsSturm_ab p q a b = signVariationsSturm_ab p q a' b' := by
  have h1 : List.signVariations (seqEval a (sturmSeq p q)) = List.signVariations (seqEval a' (sturmSeq p q)) := by
    apply changes_smods_congr p q a a'
    · exact ne_of_lt haa'
    · exact hpa
    · intros p' hp' x hx
      apply no_root p' hp'
      left
      cases hx
      next hx => exact hx
      next hx => linarith
  have h2 : List.signVariations (seqEval b (sturmSeq p q)) = List.signVariations (seqEval b' (sturmSeq p q)) := by
    apply changes_smods_congr p q b b'
    · exact Ne.symm (ne_of_lt hb'b)
    · exact hpb
    · intros p' hp' x hx
      apply no_root p' hp'
      right
      cases hx
      next hx => linarith
      next hx => exact hx
  unfold signVariationsSturm_ab signVariations_ab
  rw [h1, h2]

theorem cauchyIndex_sturmSeq (p q: Polynomial ℝ) (a b : ℝ) (hpa: p.eval a ≠ 0) (hpb : p.eval b ≠ 0) (hab : a < b) :
    signVariationsSturm_ab p q a b = cauchyIndex p q a b := by
  induction p, q using sturmSeq.induct generalizing a b
  next p =>
    rw [signVariationsSturm_ab, sturmSeq_zero]
    simp [signVariations_ab, cauchyIndex, rootsInInterval]
  next p q h_zero IH =>
    if H: q = 0 then simp [H]
    else
      have ⟨a_, b_, haa_, ha_b_, hbb_, hn_root⟩ := cauchyIndex_sturmSeq_aux p q a b hab
      let r := (-p % q)
      have ⟨ps, hps, hpsqr, htlps⟩: ∃ps : List (Polynomial ℝ), sturmSeq p q = p :: q :: ps ∧ sturmSeq q r = q :: ps ∧ sturmSeq q (-p%q) = q :: ps := by
        use sturmSeq (-p % q) (-q % (-p % q))
        rw [sturmSeq_cons h_zero, sturmSeq_cons H]
        simp
      have ⟨hpa_, hpb_, hqa_, hqb_⟩ : eval a_ p ≠ 0 ∧ eval b_ p ≠ 0 ∧  eval a_ q ≠ 0 ∧ eval b_ q ≠ 0 := by aesop
      have t0 : a_ < b_ := by linarith
      have : (∀ p' ∈ sturmSeq p q, ∀ (x : ℝ), a < x ∧ x ≤ a_ ∨ b_ ≤ x ∧ x < b → eval x p' ≠ 0) :=
        fun p' a_1 x a => hn_root p' a_1 x a
      rw [changes_itv_smods_congr p q a a_ b b_ hpa hpb haa_ hbb_ this]
      have : (∀ (x : ℝ), a < x ∧ x ≤ a_ ∨ b_ ≤ x ∧ x < b → eval x p ≠ 0) := by
        intro x hx
        rcases hn_root p (by rw [hps]; simp) x hx with hneq
        exact hneq
      have h_congr_cindex := cindex_poly_congr p q a a_ b b_ haa_ hbb_ t0 this
      have t1 : eval a_ (p * q) ≠ 0 := by simp [Polynomial.eval_mul, hpa_, hqa_]
      have t2 : eval b_ (p * q) ≠ 0 := by simp [Polynomial.eval_mul, hpb_, hqb_]
      have h_cindex := cauchyIndex_poly_rec p q a_ b_ ha_b_ t1 t2
      have h_changes_itv := changes_itv_smods_rec t1 t2
      rw [h_congr_cindex, h_cindex, h_changes_itv]
      rw [IH a_ b_ hqa_ hqb_ t0]
