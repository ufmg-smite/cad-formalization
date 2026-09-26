import Cad.Univariate.SturmTarski.SeqDefs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial

open Polynomial Set Filter SignType Topology

noncomputable section

def rootsInInterval (f : Polynomial ℝ) (a b : ℝ) : Finset ℝ :=
  f.roots.toFinset.filter (fun x => x ∈ Ioo a b)

def tarskiQuery (f g : Polynomial ℝ) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval f a b, sign (g.eval x)

lemma rootsInIntervalZero (a b : ℝ) : rootsInInterval 0 a b = ∅ := by simp [rootsInInterval]

lemma mem_rootsInInterval {p : Polynomial ℝ} {a b x : ℝ} :
    x ∈ rootsInInterval p a b ↔ (p ≠ 0 ∧ eval x p = 0) ∧ a < x ∧ x < b := by
  simp [rootsInInterval, mem_roots']

open scoped Classical in
@[simp]
def rootsInSet (p : Polynomial ℝ) (S : Set ℝ) : Finset ℝ :=
  p.roots.toFinset.filter (fun x => x ∈ S)

lemma rootsInSet_interval (p : Polynomial ℝ) (a b : ℝ) :
    rootsInInterval p a b = rootsInSet p (Set.Ioo a b) := by simp [rootsInInterval]

open scoped Classical in
lemma rootsInSet_cup (p : Polynomial ℝ) (S T : Set ℝ) :
    rootsInSet p S ∪ rootsInSet p T = rootsInSet p (S ∪ T) := by
  simp only [rootsInSet, mem_union]
  exact Finset.filter_union_right (fun x => x ∈ S) (fun x => x ∈ T) p.roots.toFinset

lemma rootsInInterval_mul {p q : Polynomial ℝ} (a b : ℝ) (hpq : p * q ≠ 0) :
    rootsInInterval (p * q) a b = rootsInInterval p a b ∪ rootsInInterval q a b := by
  unfold rootsInInterval
  rw [roots_mul hpq, Multiset.toFinset_add]
  exact Finset.filter_union (fun x => x ∈ Ioo a b) p.roots.toFinset q.roots.toFinset

/-! ### Algebraic facts -/

/-- A nonzero polynomial with a root has nonzero derivative. -/
theorem derivative_ne_zero_of_isRoot {R : Type*} [CommRing R] [IsAddTorsionFree R] {p : R[X]}
    {x : R} (hp : p ≠ 0)
    (h : p.IsRoot x) : derivative p ≠ 0 :=
  derivative_ne_zero.mpr (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_root hp h)).ne'

lemma eval_mod (p q: Polynomial ℝ) (x: ℝ) (h: eval x q = 0) : eval x (p % q) = eval x p := by
 have : eval x (p % q) = eval x (p / q * q) + eval x (p % q) := by simp; exact Or.inr h
 rw [← eval_add, EuclideanDomain.div_add_mod'] at this; exact this

lemma mul_C_eq_root_multiplicity (p: Polynomial ℝ) (c r: ℝ) (hc: ¬ c = 0):
    (rootMultiplicity r p = rootMultiplicity r (C c * p)) := by
  simp only [←count_roots]
  rw [roots_C_mul]
  exact hc

lemma eval_neg_mod {p q : Polynomial ℝ} {x : ℝ} (hq : eval x q = 0) :
    eval x (-p % q) = -eval x p := by
  rw [mod_minus, eval_neg, eval_mod p q x hq]

lemma comp_neg_X_leadingCoeff (p : Polynomial ℝ) :
    (p.comp (-X)).leadingCoeff = (-1) ^ p.natDegree * p.leadingCoeff := by
  rw [leadingCoeff_comp (by simp), leadingCoeff_neg, leadingCoeff_X, mul_comm]

lemma comp_neg_X_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) : p.comp (-X) ≠ 0 := by
  intro h
  have := congrArg leadingCoeff h
  rw [comp_neg_X_leadingCoeff, leadingCoeff_zero, mul_eq_zero] at this
  rcases this with h1 | h1
  · exact pow_ne_zero _ (by norm_num) h1
  · exact hp (leadingCoeff_eq_zero.mp h1)

lemma sign_inf_comp (p : Polynomial ℝ) :
    signNegInf p = signPosInf (p.comp (-Polynomial.X)) := by
  rw [signPosInf, comp_neg_X_leadingCoeff, sign_mul, signNegInf]
  rcases Nat.even_or_odd p.natDegree with h | h
  · simp [h, h.neg_one_pow]
  · simp [h.neg_one_pow, Nat.not_even_iff_odd.mpr h, sign_neg neg_one_lt_zero]

/-! ### Root-free neighbourhoods and the intermediate value theorem -/

lemma next_non_root_interval (p : Polynomial ℝ) (lb : ℝ) (hp : p ≠ 0) :
    ∃ ub : ℝ, lb < ub ∧ (∀ z ∈ Ioc lb ub, eval z p ≠ 0) := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    ((eventually_eval_ne_zero_codiscrete hp).filter_mono ((nhdsGT_le_nhdsNE lb).trans (nhdsNE_le_codiscrete lb)))
  have hu : lb < u := hu
  exact ⟨(lb + u) / 2, by linarith, fun z hz => hsub ⟨hz.1, by linarith [hz.2]⟩⟩

lemma last_non_root_interval (p : Polynomial ℝ) (ub : ℝ) (hp : p ≠ 0) :
    ∃ lb : ℝ, lb < ub ∧ (∀ z ∈ Ico lb ub, eval z p ≠ 0) := by
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    ((eventually_eval_ne_zero_codiscrete hp).filter_mono ((nhdsLT_le_nhdsNE ub).trans (nhdsNE_le_codiscrete ub)))
  have hl : l < ub := hl
  exact ⟨(l + ub) / 2, by linarith, fun z hz => hsub ⟨by linarith [hz.1], hz.2⟩⟩

/-- If a polynomial takes values of opposite signs at `a ≤ b`, it has a root strictly between
them (intermediate value theorem). -/
theorem exists_root_ioo_mul {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (hap : eval a p * eval b p < 0) :
    ∃ r : ℝ, a < r ∧ r < b ∧ eval r p = 0 := by
  rcases lt_or_gt_of_ne (left_ne_zero_of_mul hap.ne) with ha | ha
  · have hb : 0 < eval b p := pos_of_mul_neg_right hap ha.le
    obtain ⟨r, ⟨har, hrb⟩, hr⟩ := intermediate_value_Ioo hab p.continuousOn ⟨ha, hb⟩
    exact ⟨r, har, hrb, hr⟩
  · have hb : eval b p < 0 := neg_of_mul_neg_right hap ha.le
    obtain ⟨r, ⟨har, hrb⟩, hr⟩ := intermediate_value_Ioo' hab p.continuousOn ⟨hb, ha⟩
    exact ⟨r, har, hrb, hr⟩

/-- On an open interval containing no root of `p`, the sign of `p` is constant. -/
lemma eval_neg_or_eval_pos_of_forall_ne_zero {p : Polynomial ℝ} {a b : ℝ}
    (h : ∀ z ∈ Ioo a b, eval z p ≠ 0) :
    (∀ z ∈ Ioo a b, eval z p < 0) ∨ (∀ z ∈ Ioo a b, 0 < eval z p) := by
  by_contra! hcon
  obtain ⟨⟨z₁, hz₁, h₁⟩, ⟨z₂, hz₂, h₂⟩⟩ := hcon
  have h₁' : 0 < eval z₁ p := lt_of_le_of_ne h₁ (h z₁ hz₁).symm
  have h₂' : eval z₂ p < 0 := lt_of_le_of_ne h₂ (h z₂ hz₂)
  rcases le_total z₁ z₂ with hle | hle
  · obtain ⟨r, hr₁, hr₂, hr₃⟩ := exists_root_ioo_mul hle (mul_neg_of_pos_of_neg h₁' h₂')
    exact h r ⟨lt_trans hz₁.1 hr₁, lt_trans hr₂ hz₂.2⟩ hr₃
  · obtain ⟨r, hr₁, hr₂, hr₃⟩ := exists_root_ioo_mul hle (mul_neg_of_neg_of_pos h₂' h₁')
    exact h r ⟨lt_trans hz₂.1 hr₁, lt_trans hr₂ hz₁.2⟩ hr₃

/-! ### Behaviour at infinity -/

/-- Far to the right, the sign of a polynomial is the sign of its leading coefficient. -/
lemma eventually_sign_eq_atTop {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∀ᶠ x in atTop, sign (eval x p) = signPosInf p := by
  rcases eq_or_ne p.natDegree 0 with hdeg | hdeg
  · obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp hdeg
    simp [signPosInf]
  · have hdeg' : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
    rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp) with hlc | hlc
    · filter_upwards [(tendsto_atBot_of_leadingCoeff_nonpos p hdeg'
        (le_of_lt hlc)).eventually_lt_atBot 0]
        with x hx
      rw [signPosInf, sign_neg hx, sign_neg hlc]
    · filter_upwards [(tendsto_atTop_of_leadingCoeff_nonneg p hdeg'
        (le_of_lt hlc)).eventually_gt_atTop 0]
        with x hx
      rw [signPosInf, sign_pos hx, sign_pos hlc]

lemma eventually_sign_eq_atBot {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∀ᶠ x in atBot, sign (eval x p) = signNegInf p := by
  rw [sign_inf_comp]
  filter_upwards [tendsto_neg_atBot_atTop.eventually
    (eventually_sign_eq_atTop (comp_neg_X_ne_zero hp))] with x hx
  simpa using hx

lemma eventually_roots_lt_atTop {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∀ᶠ x in atTop, ∀ y, eval y p = 0 → y < x := by
  obtain ⟨M, hM⟩ := (finite_setOfPred_isRoot hp).bddAbove
  filter_upwards [eventually_gt_atTop M] with x hx y hy
  exact lt_of_le_of_lt (hM hy) hx

lemma eventually_lt_roots_atBot {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∀ᶠ x in atBot, ∀ y, eval y p = 0 → x < y := by
  obtain ⟨M, hM⟩ := (finite_setOfPred_isRoot hp).bddBelow
  filter_upwards [eventually_lt_atBot M] with x hx y hy
  exact lt_of_lt_of_le hx (hM hy)

lemma root_list_ub (ps : List (Polynomial ℝ)) (a : ℝ) (h0 : 0 ∉ ps) :
    ∃ ub : ℝ,
      ((∀ p ∈ ps, ∀ x : ℝ, eval x p = 0 → x < ub) ∧
       (a < ub) ∧
       (∀ x : ℝ, ub ≤ x → ∀ p ∈ ps, sign (eval x p) = signPosInf p)) := by
  have h : ∀ᶠ x in atTop, ∀ p ∈ ps,
      (∀ y, eval y p = 0 → y < x) ∧ sign (eval x p) = signPosInf p := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have hp : p ≠ 0 := fun h => h0 (by rw [← h]; exact List.mem_cons_self)
      simp only [List.mem_cons, forall_eq_or_imp]
      exact eventually_and.mpr ⟨(eventually_roots_lt_atTop hp).and (eventually_sign_eq_atTop hp),
        ih (fun h => h0 (List.mem_cons_of_mem p h))⟩
  obtain ⟨ub, hub⟩ := eventually_atTop.mp (h.and (eventually_gt_atTop a))
  exact ⟨ub, fun p hp x hx => ((hub ub le_rfl).1 p hp).1 x hx, (hub ub le_rfl).2,
    fun x hx p hp => ((hub x hx).1 p hp).2⟩

lemma root_list_lb (ps : List (Polynomial ℝ)) (b : ℝ) (h0 : 0 ∉ ps) :
    ∃ lb : ℝ,
      ((∀ p ∈ ps, ∀ x : ℝ, eval x p = 0 → lb < x) ∧
       (lb < b) ∧
       (∀ x : ℝ, x ≤ lb → ∀ p ∈ ps, sign (eval x p) = signNegInf p)) := by
  have h : ∀ᶠ x in atBot, ∀ p ∈ ps,
      (∀ y, eval y p = 0 → x < y) ∧ sign (eval x p) = signNegInf p := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have hp : p ≠ 0 := fun h => h0 (by rw [← h]; exact List.mem_cons_self)
      simp only [List.mem_cons, forall_eq_or_imp]
      exact eventually_and.mpr ⟨(eventually_lt_roots_atBot hp).and (eventually_sign_eq_atBot hp),
        ih (fun h => h0 (List.mem_cons_of_mem p h))⟩
  obtain ⟨lb, hlb⟩ := eventually_atBot.mp (h.and (eventually_lt_atBot b))
  exact ⟨lb, fun p hp x hx => ((hlb lb le_rfl).1 p hp).1 x hx, (hlb lb le_rfl).2,
    fun x hx p hp => ((hlb x hx).1 p hp).2⟩
