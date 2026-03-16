import CompPoly
import Cad.SturmBasu.Theorem

open CompPoly

lemma lt_of_le_of_neq (a b : Rat) : a ≠ 0 → b ≠ 0 → a * b ≤ 0 → a * b < 0 := by
  intros h1 h2 h3
  by_contra! abs
  have : a * b = 0 := by linarith
  simp_all only [ne_eq, le_refl, mul_eq_zero, or_self]

lemma sgns_3 {a b c : Rat} : 0 < a * b → a * c ≤ 0 → b * c ≤ 0 := by
  intros h1 h2
  if ha: 0 < a then
    have hb : 0 < b := (Rat.mul_pos_iff_of_pos_left ha).mp h1
    have hc : c ≤ 0 := nonpos_of_mul_nonpos_right h2 ha
    nlinarith
  else
    if ha: a = 0 then
      rw [ha] at h1
      simp at h1
    else
      have ha : a < 0 := by grind
      have hb : b < 0 := (neg_iff_neg_of_mul_pos h1).mp ha
      have hc : 0 ≤ c := nonneg_of_mul_nonpos_right h2 ha
      nlinarith

lemma eval_comm_map (p : Polynomial Rat) (l : Rat) : (p.eval l) = (p.map (Rat.castHom ℝ)).eval (l : Real) := by
  simp [Polynomial.eval_eq_sum_range]

lemma cpoly_eval2_poly_eval (p : CPolynomial Rat) (x : Rat) : p.eval₂ (Rat.castHom ℝ) x = p.toPoly.eval x := by
  rw [CPolynomial.eval₂_toPoly, <- Polynomial.eval_map, <- eval_comm_map]

namespace AlgebraicNumber

-- The root of `p` in the interval `[l, r]`
structure Raw where
  p: CPolynomial Rat
  l: Rat
  r: Rat
  -- This is also guaranteed by libpoly; this is necessary for `refine_wellDefined`.
  sgn_diff : p.eval l * p.eval r ≤ 0

def Raw.wellDefined (a: Raw) : Prop :=
  let ⟨p, l, r, _⟩ := a
  ∃! x : Real, p.eval₂ (Rat.castHom ℝ) x = 0 ∧ l ≤ x ∧ x ≤ r

instance (a : Raw) : Decidable a.wellDefined := sorry

lemma lr_wellDefined : ∀ a: Raw, a.wellDefined → a.l ≤ a.r := by
  rintro ⟨p, l, r⟩ ⟨x, ⟨hx, hxl, hxr⟩, hx_unique⟩
  have : (l : Real) ≤ r := Std.le_trans hxl hxr
  simp_all only [and_imp, Rat.cast_le]

def Raw.refine (a: Raw) : Raw :=
  let ⟨p, l, r, hsgn_diff⟩ := a
  let m := (l + r) / 2
  if hev: p.eval l * p.eval m ≤ 0 then
    ⟨p, l, m, hev⟩
  else
    ⟨p, m, r, by push_neg at hev; exact sgns_3 hev hsgn_diff⟩

lemma refine_bounds_l : ∀ (a : Raw), a.wellDefined → a.l ≤ a.refine.l := by
  intros a h
  have := lr_wellDefined a h
  simp [Raw.refine]
  split_ifs
  · linarith
  · linarith

lemma refine_bounds_r : ∀ (a : Raw), a.wellDefined → a.refine.r ≤ a.r := by
  intros a h
  have := lr_wellDefined a h
  simp [Raw.refine]
  split_ifs
  · linarith
  · linarith

lemma refine_wellDefined : ∀ a: Raw, a.wellDefined → a.refine.wellDefined := by
  intros a ha
  have hlr := lr_wellDefined a ha
  obtain ⟨p, l, r, hsgn_diff⟩ := a
  have hlr' : (l : Real) ≤ r := Rat.cast_le.mpr hlr
  obtain ⟨x, ⟨hx, hlx, hxr⟩, hx_unique⟩ := ha
  simp only [Raw.refine]
  split_ifs
  next hi =>
    rw [CPolynomial.eval_toPoly, CPolynomial.eval_toPoly] at hi
    if hpl: p.toPoly.eval l = 0 then
      have hxl : l = x := by
        apply hx_unique
        constructor
        · rw [cpoly_eval2_poly_eval]
          exact Rat.cast_eq_zero.mpr hpl
        · grind
      use l
      simp only [le_refl, Rat.cast_le, true_and, and_imp]
      constructor
      · constructor
        · rw [cpoly_eval2_poly_eval]
          exact Rat.cast_eq_zero.mpr hpl
        · linarith
      · intros y hy1 hy2 hy3
        rw [hxl]
        apply hx_unique
        constructor
        · exact hy1
        · exact And.intro hy2 (by norm_num at hy3; linarith)
    else
      let m := (l + r) / 2
      if hpm: p.toPoly.eval m = 0 then
        use m
        simp only [Rat.cast_le, and_imp]
        constructor
        · constructor
          · rw [cpoly_eval2_poly_eval]
            exact Rat.cast_eq_zero.mpr hpm
          · grind
        · intros y hy1 hy2 hy3
          have : m = x := by
            apply hx_unique
            constructor
            · rw [cpoly_eval2_poly_eval]
              exact Rat.cast_eq_zero.mpr hpm
            · norm_cast
              grind
          rw [this]
          apply hx_unique
          constructor
          · exact hy1
          · exact And.intro hy2 (by norm_num at hy3; linarith)
      else
        have : p.toPoly.eval l * p.toPoly.eval m < 0 := lt_of_le_of_neq _ _ hpl hpm hi
        replace this : ((p.toPoly.eval l * p.toPoly.eval m) : Real) < (0 : Real) := by norm_cast
        rw [eval_comm_map, eval_comm_map] at this
        have hlm : (l : Real) ≤ m := by unfold m; norm_cast; linarith
        obtain ⟨R, hR1, hR2, hR3⟩  := exists_root_ioo_mul (p := p.toPoly.map (Rat.castHom ℝ)) hlm this
        have hRx : R = x := by
          refine hx_unique R ⟨?_, ⟨le_of_lt hR1, ?_⟩⟩
          · rw [CPolynomial.eval₂_toPoly, <- Polynomial.eval_map]
            exact hR3
          · unfold m at hR2
            norm_num at hR2
            grind
        use R
        constructor
        · constructor
          · rw [CPolynomial.eval₂_toPoly, <- Polynomial.eval_map]
            exact hR3
          · grind
        · intros y hy
          rw [hRx]
          refine hx_unique y ⟨hy.1, ⟨hy.2.1, ?_⟩⟩
          · norm_num at hy
            grind
  next hi =>
    push_neg at hi
    if hpr: p.toPoly.eval r = 0 then
      have hxr : r = x := by
        apply hx_unique
        constructor
        · rw [cpoly_eval2_poly_eval]
          exact Rat.cast_eq_zero.mpr hpr
        · grind
      use r
      simp only [le_refl, Rat.cast_le, and_imp]
      constructor
      · constructor
        · rw [cpoly_eval2_poly_eval]
          exact Rat.cast_eq_zero.mpr hpr
        · grind
      · intros y hy1 hy2 hy3
        rw [hxr]
        apply hx_unique
        constructor
        · exact hy1
        · exact And.intro (by norm_num at hy2; linarith) (by linarith)
    else
      have hm_neq0 : p.eval ((l + r) / 2) ≠ 0 := by
        intro abs
        rw [abs] at hi
        simp at hi
      have hsgn_diff' := sgns_3 hi hsgn_diff
      rw [CPolynomial.eval_toPoly, CPolynomial.eval_toPoly] at hsgn_diff'
      have : p.toPoly.eval ((l + r) / 2) * p.toPoly.eval r ≠ 0 := by
        intro abs
        have : p.toPoly.eval ((l + r) / 2) = 0 ∨ p.toPoly.eval r = 0 := Rat.mul_eq_zero.mp abs
        cases this
        next H =>
          rw [CPolynomial.eval_toPoly] at hm_neq0
          exact hm_neq0 H
        next H => exact hpr H
      have mul_lt := Rat.lt_of_le_of_ne hsgn_diff' this
      have mul_lt_r : (p.toPoly.map (Rat.castHom ℝ)).eval (((l : Real) + r) / 2) * (p.toPoly.map (Rat.castHom ℝ)).eval (r : Real) < 0 := by
        norm_cast
        rw [<- eval_comm_map, <- eval_comm_map]
        norm_cast
      obtain ⟨R, hR1, hR2, hR3⟩  := exists_root_ioo_mul (p := p.toPoly.map (Rat.castHom ℝ)) (by linarith) mul_lt_r
      have hRx : R = x := by
        refine hx_unique R ⟨?_, ⟨?_, ?_⟩⟩
        · rw [CPolynomial.eval₂_toPoly, <- Polynomial.eval_map]
          exact hR3
        · grind
        · grind
      use R
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [CPolynomial.eval₂_toPoly, <- Polynomial.eval_map]
        exact hR3
      · norm_num
        grind
      · intros y hy
        norm_num at hy
        rw [hRx]
        refine hx_unique y ⟨hy.1, ⟨?_, ?_⟩⟩
        · grind
        · grind

@[simp]
def toSeq (a: Raw) : ℕ → ℚ := fun n =>
  match n with
  | 0 => (a.l + a.r) / 2
  | n + 1 =>
    let a' := a.refine
    toSeq a' n

lemma toSeq_bound : ∀ a : Raw, ∀ i : Nat, a.wellDefined → a.l ≤ toSeq a i ∧ toSeq a i ≤ a.r := by
  intros a i h
  have := lr_wellDefined a h
  cases i
  next =>
    simp only [toSeq]
    constructor <;> linarith
  next i =>
    simp only [toSeq]
    have := toSeq_bound a.refine i (refine_wellDefined a h)
    have hl := refine_bounds_l a h
    have hr := refine_bounds_r a h
    grind

lemma toSeq_iterate (a : Raw) : ∀ n k : ℕ, toSeq a (n + k) = toSeq (Raw.refine^[n] a) k := by
  intro n
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    intro k
    rw [Nat.succ_add]
    simp only [toSeq]
    rw [ih a.refine k, Function.iterate_succ, Function.comp]

lemma refineN_wellDefined (a : Raw) (n : ℕ) (h : a.wellDefined) : (Raw.refine^[n] a).wellDefined := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp]
    exact refine_wellDefined _ ih

lemma refine_width (a : Raw) : a.refine.r - a.refine.l = (a.r - a.l) / 2 := by
  obtain ⟨p, l, r, hsgn⟩ := a
  simp [Raw.refine]
  split_ifs <;> ring

lemma refineN_width (a : Raw) : ∀ n : ℕ,
    (Raw.refine^[n] a).r - (Raw.refine^[n] a).l = (a.r - a.l) / 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp, refine_width, ih]
    rw [pow_succ]
    field_simp

lemma toSeq_in_refineN (a : Raw) (n i : ℕ) (h : a.wellDefined) (hni : n ≤ i) :
    (Raw.refine^[n] a).l ≤ toSeq a i ∧ toSeq a i ≤ (Raw.refine^[n] a).r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hni
  rw [toSeq_iterate]
  exact toSeq_bound _ k (refineN_wellDefined a n h)

theorem toSeq_cauchy : ∀ a: Raw, a.wellDefined → IsCauSeq abs (toSeq a) := by
  intros a ha
  intro ε hε
  have hlr := lr_wellDefined a ha
  have hwidth_nn : 0 ≤ a.r - a.l := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (a.r - a.l) / 2 ^ N < ε := by
    rcases eq_or_lt_of_le hwidth_nn with heq | hlt
    · exact ⟨0, by simp [← heq, hε]⟩
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hlt) (show (1:ℚ)/2 < 1 by norm_num)
      refine ⟨N, ?_⟩
      have h2pos : (0 : ℚ) < 2 ^ N := pow_pos (by norm_num) N
      have := mul_lt_mul_of_pos_right hN hlt
      rwa [div_mul_cancel₀ _ (ne_of_gt hlt), one_div, inv_pow, mul_comm,
        ← div_eq_mul_inv] at this
  use N
  intro j hj
  have hbN := toSeq_in_refineN a N N ha le_rfl
  have hbj := toSeq_in_refineN a N j ha hj
  have hwidthN : (Raw.refine^[N] a).r - (Raw.refine^[N] a).l = (a.r - a.l) / 2 ^ N := refineN_width a N
  rw [abs_lt]
  constructor <;> nlinarith [hbN.1, hbN.2, hbj.1, hbj.2]

@[simp]
def Raw.toReal (a: Raw): ℝ :=
  if h: a.wellDefined then Real.ofCauchy (CauSeq.Completion.mk ⟨toSeq a, toSeq_cauchy a h⟩) else 0

lemma toReal_bounds : ∀ a : Raw, a.wellDefined → a.l ≤ a.toReal ∧ a.toReal ≤ a.r := by
  rintro a hwda
  simp [hwda]
  admit

theorem refine_toReal : ∀ a : Raw, a.wellDefined → a.toReal = a.refine.toReal := by
  intro a hwd
  have hwd' := refine_wellDefined a hwd
  simp only [Raw.toReal, hwd, hwd', dite_true]
  apply Real.ext_cauchy
  exact CauSeq.Completion.mk_eq.mpr (by
    show CauSeq.LimZero _
    intro ε hε
    -- Both toSeq a n and toSeq a.refine n are in the interval [refine^n a .l, refine^n a .r]
    -- which has width (a.r - a.l) / 2^n → 0
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (a.r - a.l) / 2 ^ N < ε := by
      have hlr := lr_wellDefined a hwd
      have hwidth_nn : 0 ≤ a.r - a.l := by linarith
      rcases eq_or_lt_of_le hwidth_nn with heq | hlt
      · exact ⟨0, by simp [← heq, hε]⟩
      · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hlt) (show (1:ℚ)/2 < 1 by norm_num)
        refine ⟨N, ?_⟩
        have h2pos : (0 : ℚ) < 2 ^ N := pow_pos (by norm_num) N
        have := mul_lt_mul_of_pos_right hN hlt
        rwa [div_mul_cancel₀ _ (ne_of_gt hlt), one_div, inv_pow, mul_comm,
          ← div_eq_mul_inv] at this
    use N
    intro j hj
    have hbA := toSeq_in_refineN a N j hwd hj
    -- toSeq a.refine j is in refine^j (a.refine) = refine^(j+1) a ⊆ refine^N a
    have hbR_own := toSeq_in_refineN a.refine N j hwd' hj
    -- refine^N (a.refine) = refine^(N+1) a
    -- refine^(N+1) a is contained in refine^N a
    have hcontain_l := refine_bounds_l (Raw.refine^[N] a) (refineN_wellDefined a N hwd)
    have hcontain_r := refine_bounds_r (Raw.refine^[N] a) (refineN_wellDefined a N hwd)
    have hbR : (Raw.refine^[N] a).l ≤ toSeq a.refine j ∧ toSeq a.refine j ≤ (Raw.refine^[N] a).r := by
      have : (Raw.refine^[N] a.refine) = (Raw.refine^[N] a).refine := by
        rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      rw [this] at hbR_own
      constructor
      · exact le_trans hcontain_l hbR_own.1
      · exact le_trans hbR_own.2 hcontain_r
    have hwidthN : (Raw.refine^[N] a).r - (Raw.refine^[N] a).l = (a.r - a.l) / 2 ^ N := refineN_width a N
    simp only [CauSeq.sub_apply]
    rw [abs_lt]
    constructor <;> nlinarith [hbA.1, hbA.2, hbR.1, hbR.2]
  )

instance : LT Raw where
  lt a b := a.r < b.l

theorem lt_toReal : ∀ (a b : Raw), a.wellDefined → b.wellDefined → a < b → a.toReal < b.toReal := sorry

lemma refine_lt_toReal : ∀ a b : Raw, a.wellDefined → b.wellDefined → a.refine.toReal < b.refine.toReal → a.toReal < b.toReal := by
  intros a b ha hb h
  rw [refine_toReal a ha, refine_toReal b hb]
  exact h

end AlgebraicNumber
