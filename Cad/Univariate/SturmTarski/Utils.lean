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

lemma rootsInInterval_mul {p q: Polynomial ℝ} (a b: ℝ) (hpq: p * q ≠ 0): rootsInInterval (p * q) a b = rootsInInterval p a b ∪ rootsInInterval q a b := by
  unfold rootsInInterval
  rw [roots_mul hpq, Multiset.toFinset_add]
  exact Finset.filter_union (fun x => x ∈ Ioo a b) p.roots.toFinset q.roots.toFinset

/-! ### Algebraic facts -/

lemma eval_non_zero (p: Polynomial ℝ) (x: ℝ) (h: eval x p ≠ 0) : p ≠ 0 := by
  rintro rfl
  simp at h

lemma derivative_ne_0 (p : Polynomial Real) (x : Real) (hev : eval x p = 0) (hp : p ≠ 0) : derivative p ≠ 0 := by
  intro abs
  obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp (natDegree_eq_zero_of_derivative_eq_zero abs)
  simp at hev
  simp [hev] at hp

lemma eval_mod (p q: Polynomial ℝ) (x: ℝ) (h: eval x q = 0) : eval x (p % q) = eval x p := by
 have : eval x (p % q) = eval x (p / q * q) + eval x (p % q) := by simp; exact Or.inr h
 rw [<- eval_add, EuclideanDomain.div_add_mod'] at this; exact this

lemma mul_C_eq_root_multiplicity (p: Polynomial ℝ) (c r: ℝ) (hc: ¬ c = 0):
    (rootMultiplicity r p = rootMultiplicity r (C c * p)) := by
  simp only [<-count_roots]
  rw [roots_C_mul]
  exact hc

theorem mod_mul (p q r : Polynomial ℝ) (hr : r ≠ 0) : (r * p) % (r * q) = r * (p % q) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · have h1 : (r * p) % (r * q) = (r * (p % q)) % (r * q) :=
      mod_eq_of_dvd_sub ⟨p / q, by rw [← mul_sub, EuclideanDomain.mod_eq_sub_mul_div]; ring⟩
    rw [h1, mod_eq_self_iff (mul_ne_zero hr hq), degree_mul, degree_mul]
    exact WithBot.add_lt_add_left (degree_ne_bot.mpr hr) (degree_mod_lt p hq)

lemma mod_minus (p q: Polynomial ℝ) : -p%q = -(p%q) := by rw [mod_def, mod_def, neg_modByMonic]

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
    sign_neg_inf p = sign_pos_inf (p.comp (-Polynomial.X)) := by
  rw [sign_pos_inf, comp_neg_X_leadingCoeff, sign_mul, sign_neg_inf]
  rcases Nat.even_or_odd p.natDegree with h | h
  · simp [h, h.neg_one_pow]
  · simp [h.neg_one_pow, Nat.not_even_iff_odd.mpr h, sign_neg neg_one_lt_zero]

/-! ### Root-free neighbourhoods and the intermediate value theorem -/

/-- A nonzero polynomial has no roots in a punctured neighbourhood of any point. -/
lemma eventually_eval_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) (x : ℝ) :
    ∀ᶠ z in 𝓝[≠] x, eval z p ≠ 0 := by
  have hfin : ({z | IsRoot p z} \ {x}).Finite := (finite_setOf_isRoot hp).diff
  have hmem : ({z | IsRoot p z} \ {x})ᶜ ∈ 𝓝 x :=
    hfin.isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with z hz hzx h0
  exact hz ⟨h0, hzx⟩

lemma next_non_root_interval (p : Polynomial Real) (lb : Real) (hp : p ≠ 0) :
    ∃ ub : Real, lb < ub ∧ (∀ z ∈ Ioc lb ub, eval z p ≠ 0) := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    ((eventually_eval_ne_zero hp lb).filter_mono (nhdsGT_le_nhdsNE lb))
  have hu : lb < u := hu
  exact ⟨(lb + u) / 2, by linarith, fun z hz => hsub ⟨hz.1, by linarith [hz.2]⟩⟩

lemma last_non_root_interval (p : Polynomial Real) (ub : Real) (hp : p ≠ 0) :
    ∃ lb : Real, lb < ub ∧ (∀ z ∈ Ico lb ub, eval z p ≠ 0) := by
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    ((eventually_eval_ne_zero hp ub).filter_mono (nhdsLT_le_nhdsNE ub))
  have hl : l < ub := hl
  exact ⟨(l + ub) / 2, by linarith, fun z hz => hsub ⟨by linarith [hz.1], hz.2⟩⟩

theorem exists_root_ioo {p: Polynomial ℝ} {a b : ℝ} (hab: a <= b) (hap: eval a p < 0) (hbp: eval b p > 0): ∃ r: ℝ, r > a ∧ r < b ∧ eval r p = 0 := by
  obtain ⟨x, ⟨hxa, hxb⟩, hx⟩ := intermediate_value_Ioo hab p.continuousOn ⟨hap, hbp⟩
  exact ⟨x, hxa, hxb, hx⟩

theorem exists_root_ioo' {p: Polynomial ℝ} {a b : ℝ} (hab: a <= b) (hap: eval a p > 0) (hbp: eval b p < 0): ∃ r: ℝ, r > a ∧ r < b ∧ eval r p = 0 := by
  obtain ⟨x, ⟨hxa, hxb⟩, hx⟩ := intermediate_value_Ioo' hab p.continuousOn ⟨hbp, hap⟩
  exact ⟨x, hxa, hxb, hx⟩

theorem exists_root_ioo_mul {p: Polynomial ℝ} {a b: ℝ} (hab: a ≤ b) (hap: (eval a p) * (eval b p) < 0) : ∃ r: ℝ, r > a ∧ r < b ∧ eval r p = 0 := by
  if H: eval a p > 0 then
    have haux: eval b p < 0 := by nlinarith
    exact exists_root_ioo' hab H haux
  else
    have haux1: eval b p > 0 := by nlinarith
    have haux: eval a p < 0 := by nlinarith
    exact exists_root_ioo hab haux haux1

lemma not_eq_pos_or_neg_iff_1 (p : Polynomial Real) (lb ub : Real) :
    (∀ z ∈ Ioc lb ub, eval z p ≠ 0) ↔ ((∀ z ∈ Ioc lb ub, eval z p < 0) ∨ (∀ z ∈ Ioc lb ub, 0 < eval z p)) := by
  refine ⟨fun h => ?_, fun h z hz => h.elim (fun h => (h z hz).ne) (fun h => (h z hz).ne')⟩
  by_contra! hcon
  obtain ⟨⟨z₁, hz₁, h₁⟩, ⟨z₂, hz₂, h₂⟩⟩ := hcon
  have h₁' : 0 < eval z₁ p := lt_of_le_of_ne h₁ (h z₁ hz₁).symm
  have h₂' : eval z₂ p < 0 := lt_of_le_of_ne h₂ (h z₂ hz₂)
  rcases le_total z₁ z₂ with hle | hle
  · obtain ⟨r, hr₁, hr₂, hr₃⟩ := exists_root_ioo' hle h₁' h₂'
    exact h r ⟨lt_of_lt_of_le hz₁.1 (le_of_lt hr₁), le_trans (le_of_lt hr₂) hz₂.2⟩ hr₃
  · obtain ⟨r, hr₁, hr₂, hr₃⟩ := exists_root_ioo hle h₂' h₁'
    exact h r ⟨lt_of_lt_of_le hz₂.1 (le_of_lt hr₁), le_trans (le_of_lt hr₂) hz₁.2⟩ hr₃

lemma exists_deriv_eq_slope_poly (a b : Real) (hab : a < b) (p : Polynomial Real) :
    ∃ c : Real, c > a ∧ c < b ∧ eval b p - eval a p = (b - a) * eval c (derivative p) := by
  obtain ⟨c, hc1, hc2⟩ :=
    exists_deriv_eq_slope (a := a) (b := b) (fun x => eval x p) hab
      (Polynomial.continuousOn_aeval p) (Polynomial.differentiableOn_aeval p)
  simp at hc1
  obtain ⟨hc_low, hc_high⟩ := hc1
  use c
  refine ⟨hc_low, hc_high, ?_⟩
  rw [Polynomial.deriv] at hc2
  rw [hc2]
  have : (b - a) ≠ 0 := by linarith
  field_simp

/-! ### Behaviour at infinity -/

/-- Far to the right, the sign of a polynomial is the sign of its leading coefficient. -/
lemma eventually_sign_eq_atTop {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∀ᶠ x in atTop, sign (eval x p) = sign_pos_inf p := by
  rcases eq_or_ne p.natDegree 0 with hdeg | hdeg
  · obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp hdeg
    simp [sign_pos_inf]
  · have hdeg' : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
    rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp) with hlc | hlc
    · filter_upwards [(tendsto_atBot_of_leadingCoeff_nonpos p hdeg' (le_of_lt hlc)).eventually_lt_atBot 0]
        with x hx
      rw [sign_pos_inf, sign_neg hx, sign_neg hlc]
    · filter_upwards [(tendsto_atTop_of_leadingCoeff_nonneg p hdeg' (le_of_lt hlc)).eventually_gt_atTop 0]
        with x hx
      rw [sign_pos_inf, sign_pos hx, sign_pos hlc]

lemma eventually_sign_eq_atBot {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∀ᶠ x in atBot, sign (eval x p) = sign_neg_inf p := by
  rw [sign_inf_comp]
  filter_upwards [tendsto_neg_atBot_atTop.eventually
    (eventually_sign_eq_atTop (comp_neg_X_ne_zero hp))] with x hx
  simpa using hx

lemma eventually_roots_lt_atTop {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∀ᶠ x in atTop, ∀ y, eval y p = 0 → y < x := by
  obtain ⟨M, hM⟩ := (finite_setOf_isRoot hp).bddAbove
  filter_upwards [eventually_gt_atTop M] with x hx y hy
  exact lt_of_le_of_lt (hM hy) hx

lemma eventually_lt_roots_atBot {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∀ᶠ x in atBot, ∀ y, eval y p = 0 → x < y := by
  obtain ⟨M, hM⟩ := (finite_setOf_isRoot hp).bddBelow
  filter_upwards [eventually_lt_atBot M] with x hx y hy
  exact lt_of_lt_of_le hx (hM hy)

lemma root_list_ub (ps : List (Polynomial ℝ)) (a : ℝ) (h0 : 0 ∉ ps) :
    ∃ ub : ℝ,
      ((∀ p ∈ ps, ∀ x : ℝ, eval x p = 0 → x < ub) ∧
       (a < ub) ∧
       (∀ x : ℝ, x ≥ ub → ∀ p ∈ ps, sign (eval x p) = sign_pos_inf p)) := by
  have h : ∀ᶠ x in atTop, ∀ p ∈ ps,
      (∀ y, eval y p = 0 → y < x) ∧ sign (eval x p) = sign_pos_inf p := by
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
       (∀ x : ℝ, x ≤ lb → ∀ p ∈ ps, sign (eval x p) = sign_neg_inf p)) := by
  have h : ∀ᶠ x in atBot, ∀ p ∈ ps,
      (∀ y, eval y p = 0 → x < y) ∧ sign (eval x p) = sign_neg_inf p := by
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
