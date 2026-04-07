import Mathlib
import CompPoly
import Cad.AlgebraicNumbers.AlgNum

open CompPoly

lemma neg_ex_unique {α : Type*} {P : α → Prop} (a b : α) : a ≠ b → P a → P b → ¬ (∃! x, P x) := by
  intro hab hpa hpb ⟨x, _, huniq⟩
  exact hab ((huniq a hpa).trans (huniq b hpb).symm)

lemma eval_eval₂ (p : Polynomial ℚ) (q : ℚ) :
    (Polynomial.eval q p) = Polynomial.eval₂ (Rat.castHom ℝ) q p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, Polynomial.eval₂_add, Rat.cast_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.eval_monomial, Polynomial.eval₂_monomial]
    push_cast
    norm_num

lemma c_eval_eval₂ (p : CPolynomial ℚ) (q : ℚ) :
    (CPolynomial.eval q p) = CPolynomial.eval₂ (Rat.castHom Real) q p := by
  rw [CPolynomial.eval_toPoly, CPolynomial.eval₂_toPoly]
  exact eval_eval₂ p.toPoly q

lemma sturm_l_r_cpoly (p : CPolynomial ℚ) (l r : ℚ) (hl : p.eval l ≠ 0) (hr : p.eval r ≠ 0) (hlr : l < r) :
    seqVarSturmC_ab p p.derivative l r = (rootsInInterval (p.toPoly.map (Rat.castHom Real)) l r).card := by
  have : p.derivative = p.derivative * 1 := by norm_num
  rw [this, seqVarABEquivSturm p 1]
  have hl0 : Polynomial.eval (↑l) (Polynomial.map (Rat.castHom ℝ) p.toPoly) ≠ 0 := by
    rw [<- cpolynomial_map_cast l p]
    finiteness
  have hr0 : Polynomial.eval (↑r) (Polynomial.map (Rat.castHom ℝ) p.toPoly) ≠ 0 := by
    rw [<- cpolynomial_map_cast r p]
    finiteness
  have sturm_l_r := Theorem.sturm_interval l r (p.toPoly.map (Rat.castHom Real)) (Real.ratCast_lt.mpr hlr) hl0 hr0
  have : (Polynomial.derivative (Polynomial.map (Rat.castHom ℝ) p.toPoly) * Polynomial.map (Rat.castHom ℝ) (CPolynomial.toPoly 1))
       = (Polynomial.derivative (Polynomial.map (Rat.castHom ℝ) p.toPoly)) := by
    rw [CPolynomial.toPoly_one, Polynomial.map_one (Rat.castHom ℝ)]
    norm_num
  rw [this, sturm_l_r]

theorem Polynomial.isolated_root_right (p : Polynomial Real) (hp : p ≠ 0) (x : ℝ) :
    ∃ eps : ℝ, (0 < eps ∧ ∀ y ∈ Set.Ioc x (x + eps), ¬p.IsRoot y) := by
  have ha : AnalyticAt ℝ (p.eval ·) x :=
    AnalyticOnNhd.eval_polynomial p x (Set.mem_univ x)
  rcases ha.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso; apply hp
    rw [Metric.eventually_nhds_iff] at hzero
    obtain ⟨ε, hε, hball⟩ := hzero
    exact Polynomial.eq_zero_of_infinite_isRoot p <|
      (Real.ball_eq_Ioo x ε ▸ Set.Ioo_infinite (by linarith : x - ε < x + ε)).mono
        fun y hy => hball hy
  · have hright : ∀ᶠ z in (nhdsWithin x (Set.Ioi x)), p.eval z ≠ 0 :=
      hne.filter_mono (nhdsWithin_mono x fun _ hz => hz.ne')
    rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioc_subset] at hright
    obtain ⟨u, hu, hsub⟩ := hright
    exact ⟨u - x, sub_pos.mpr hu, fun y hy hroot =>
      hsub (show y ∈ Set.Ioc x u from ⟨hy.1, by linarith [hy.2]⟩) hroot⟩

theorem Polynomial.isolated_root_right_rat (p : Polynomial Real) (hp : p ≠ 0) (x : Real) :
    ∃ eps : ℚ, 0 < eps ∧ ∀ y ∈ Set.Ioc x (x + (eps : ℝ)), ¬p.IsRoot y := by
  obtain ⟨e, he, hroot⟩ := isolated_root_right p hp x
  obtain ⟨q, hq0, hqe⟩ := exists_rat_btwn he
  exact ⟨q, Rat.cast_pos.mp hq0, fun y hy =>
    hroot y ⟨hy.1, hy.2.trans (by linarith)⟩⟩

-- (Tom) Oh wow I actually don't think this is possible in general, but we can assume that a.l and a.r are
-- not roots in the case of the algebraic numbers coming from cvc5
/- instance (a : Raw) : Decidable a.wellDefined := -/
/-   if hlr : a.r ≤ a.l then by -/
/-     if hlr: a.l = a.r then -/
/-       if hl: a.p.eval a.l = 0 then -/
/-         apply Decidable.isTrue -/
/-         simp [Raw.wellDefined, ExistsUnique] -/
/-         use a.l -/
/-         constructor -/
/-         · refine And.intro ?_ (And.intro ?_ ?_) -/
/-           · rw [<- c_eval_eval₂ a.p a.l] -/
/-             exact Rat.cast_eq_zero.mpr hl -/
/-           · exact le_refl (a.l : Real) -/
/-           · rw [hlr] -/
/-         · intros y hy1 hy2 hy3 -/
/-           rw [hlr] at hy2 -/
/-           grind -/
/-       else -/
/-         apply Decidable.isFalse -/
/-         simp [Raw.wellDefined] -/
/-         rw [hlr] -/
/-         rintro ⟨x, ⟨⟨h11, h12, h13⟩, h2⟩⟩ -/
/-         have : x = a.l := by grind -/
/-         rw [this,  <- c_eval_eval₂ a.p] at h11 -/
/-         apply hl -/
/-         norm_num at h11 -/
/-         exact h11 -/
/-     else -/
/-       apply Decidable.isFalse -/
/-       have not_le : ¬ (a.l ≤ a.r) := by grind -/
/-       intro abs -/
/-       exact False.elim (not_le (lr_wellDefined a abs)) -/
/-   else if hp0: a.p = 0 then by -/
/-     apply Decidable.isFalse -/
/-     push_neg at hlr -/
/-     simp [Raw.wellDefined, hp0] -/
/-     have : a.l ≠ a.r := ne_of_lt hlr -/
/-     apply neg_ex_unique (a.l : Real) (a.r : Real) -/
/-     · simp_all only [ne_eq, Rat.cast_inj, not_false_eq_true] -/
/-     · refine And.intro ?_ (And.intro ?_ ?_) -/
/-       · exact Complex.ofReal_eq_zero.mp rfl -/
/-       · exact le_refl (a.l : Real) -/
/-       · gcongr -/
/-     · refine And.intro ?_ (And.intro ?_ ?_) -/
/-       · exact Complex.ofReal_eq_zero.mp rfl -/
/-       · gcongr -/
/-       · exact le_refl (a.r : Real) -/
/-   else by -/
/-     push_neg at hlr -/
/-     let p' := a.p.toPoly.map (Rat.castHom Real) -/
/-     if hpl: a.p.eval a.l = 0 then -/
/-       if hpr : a.p.eval a.r = 0 then -/
/-         apply Decidable.isFalse -/
/-         simp [Raw.wellDefined] -/
/-         rintro ⟨x, ⟨h1, h2, h3⟩, h4⟩ -/
/-         rw [<- Rat.cast_eq_zero (α := Real), c_eval_eval₂ a.p] at hpl hpr -/
/-         have hlx := h4 a.l (by grind) -/
/-         have hrx := h4 a.r (by grind) -/
/-         subst hlx -/
/-         simp_all only [Rat.cast_inj, lt_self_iff_false] -/
/-       else -/
/-         have : a.p.toPoly ≠ 0 := gneg_imp_gtopoly_neg a.p hp0 -/
/-         have : a.p.toPoly.map (Rat.castHom Real) ≠ 0 := by -/
/-           simp_all only [ne_eq, Polynomial.map_eq_zero, not_false_eq_true] -/
/-         have no_roots_int := Polynomial.isolated_root_right_rat (a.p.toPoly.map (Rat.castHom Real)) this a.l -/
/-         have ⟨heps1, heps2⟩ := Classical.choose_spec no_roots_int -/
/-         set eps := Classical.choose no_roots_int -/
/-         have := heps2 (a.l + eps) (by simp_all only [ne_eq, Polynomial.map_eq_zero, -/
/-           not_false_eq_true, Set.mem_Ioc, Polynomial.IsRoot.def, and_imp, lt_add_iff_pos_right, -/
/-           Rat.cast_pos, le_refl, and_self]) -/
/-         have : a.p.toPoly.eval (a.l + eps) ≠ 0 := by admit -/
/-         if hseq : seqVarSturmC_ab a.p a.p.derivative (a.l + eps) a.r = 1 then -/
/-           sorry -/
/-         else sorry -/
/-     else if hpr : a.p.eval a.r = 0 then -/
/-       sorry -/
/-     else -/
/-       if hseq: seqVarSturmC_ab a.p a.p.derivative a.l a.r = 1 then -/
/-         have h_sturm := sturm_l_r_cpoly a.p a.l a.r hpl hpr hlr -/
/-         have : a.p.toPoly ≠ 0 := gneg_imp_gtopoly_neg a.p hp0 -/
/-         have : a.p.toPoly.map (Rat.castHom Real) ≠ 0 := by -/
/-           simp_all only [ne_eq, Nat.cast_eq_one, Polynomial.map_eq_zero, not_false_eq_true] -/
/-         apply Decidable.isTrue -/
/-         apply (wellDefined_iff_rootsInInterval a this hpl hpr hlr).mpr -/
/-         zify -/
/-         rw [<- h_sturm] -/
/-         exact hseq -/
/-       else -/
/-         have h_sturm := sturm_l_r_cpoly a.p a.l a.r hpl hpr hlr -/
/-         have : a.p.toPoly ≠ 0 := gneg_imp_gtopoly_neg a.p hp0 -/
/-         have : a.p.toPoly.map (Rat.castHom Real) ≠ 0 := by -/
/-           simp_all only [ne_eq, Nat.cast_eq_one, Polynomial.map_eq_zero, not_false_eq_true] -/
/-         apply Decidable.isFalse -/
/-         intro abs -/
/-         have : a.p.toPoly ≠ 0 := gneg_imp_gtopoly_neg a.p hp0 -/
/-         have : a.p.toPoly.map (Rat.castHom Real) ≠ 0 := by -/
/-           simp_all only [ne_eq, Polynomial.map_eq_zero, not_false_eq_true] -/
/-         have := (wellDefined_iff_rootsInInterval a this hpl hpr hlr).mp abs -/
/-         zify at this -/
/-         rw [<- h_sturm] at this -/
/-         exact hseq this -/
