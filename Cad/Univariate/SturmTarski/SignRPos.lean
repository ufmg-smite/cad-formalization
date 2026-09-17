import Cad.Univariate.SturmTarski.Utils

open Polynomial Set Filter SignType Topology

noncomputable section

/-- `signRPos x p` says that `p` is positive immediately to the right of `x`. -/
def signRPos (x : ℝ) (p : Polynomial ℝ) : Prop := ∀ᶠ y in 𝓝[>] x, 0 < eval y p

theorem signRPos_iff {x : ℝ} {p : Polynomial ℝ} :
    signRPos x p ↔ ∃ b, x < b ∧ ∀ y : ℝ, x < y ∧ y < b → 0 < eval y p :=
  mem_nhdsGT_iff_exists_Ioo_subset

/-- Immediately to the right of `x`, a nonzero polynomial has a constant nonzero sign. -/
theorem exists_eventually_sign_eq (x : ℝ) {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∃ s : SignType, s ≠ 0 ∧ ∀ᶠ y in 𝓝[>] x, sign (eval y p) = s := by
  obtain ⟨b, hb, hb2⟩ := next_non_root_interval p x hp
  rcases (not_eq_pos_or_neg_iff_1 p x b).mp hb2 with h | h
  · exact ⟨-1, by decide, mem_nhdsGT_iff_exists_Ioo_subset.mpr
      ⟨b, hb, fun y hy => sign_neg (h y ⟨hy.1, le_of_lt hy.2⟩)⟩⟩
  · exact ⟨1, by decide, mem_nhdsGT_iff_exists_Ioo_subset.mpr
      ⟨b, hb, fun y hy => sign_pos (h y ⟨hy.1, le_of_lt hy.2⟩)⟩⟩

/-- If the sign of `p` right of `x` is eventually `s`, then `p` is positive right of `x`
iff `s = 1`. -/
theorem signRPos_iff_of_eventually {x : ℝ} {p : Polynomial ℝ} {s : SignType}
    (h : ∀ᶠ y in 𝓝[>] x, sign (eval y p) = s) : signRPos x p ↔ s = 1 := by
  constructor
  · intro hpos
    obtain ⟨y, hy1, hy2⟩ := (hpos.and h).exists
    rw [← hy2, sign_pos hy1]
  · rintro rfl
    exact h.mono fun y hy => sign_eq_one_iff.mp hy

lemma signRPos_of_eval_pos {x : ℝ} {p : Polynomial ℝ} (h : 0 < eval x p) : signRPos x p :=
  ((p.continuous.tendsto x).eventually (lt_mem_nhds h)).filter_mono nhdsWithin_le_nhds

/-- The mean value theorem, in the form needed for `signRPos_rec`. -/
lemma eventually_lt_of_deriv_pos {x : ℝ} {p : Polynomial ℝ} (h : signRPos x (derivative p)) :
    ∀ᶠ y in 𝓝[>] x, eval x p < eval y p := by
  obtain ⟨b, hb, hb2⟩ := signRPos_iff.mp h
  refine mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨b, hb, fun y hy => ?_⟩
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_deriv_eq_slope_poly x y hy.1 p
  have : 0 < (y - x) * eval c (derivative p) :=
    mul_pos (sub_pos.mpr hy.1) (hb2 c ⟨hc1, lt_trans hc2 hy.2⟩)
  show eval x p < eval y p
  linarith

lemma signRPos_minus (x : ℝ) (p : Polynomial ℝ) :
    p ≠ 0 → (signRPos x p ↔ (¬ signRPos x (-p))) := by
  intro hp
  obtain ⟨s, hs, hps⟩ := exists_eventually_sign_eq x hp
  have hneg : ∀ᶠ y in 𝓝[>] x, sign (eval y (-p)) = -s :=
    hps.mono fun y hy => by rw [eval_neg, Left.sign_neg, hy]
  rw [signRPos_iff_of_eventually hps, signRPos_iff_of_eventually hneg]
  clear hps hneg
  revert hs; revert s; decide

lemma signRPos_rec (p : Polynomial ℝ) (x : ℝ) (hp : p ≠ 0) :
    signRPos x p = if eval x p = 0 then signRPos x (derivative p) else 0 < eval x p := by
  rw [eq_iff_iff]
  split_ifs with hev
  · have hd : derivative p ≠ 0 := derivative_ne_0 p x hev hp
    constructor
    · intro h
      by_contra hneg
      rw [signRPos_minus x _ hd, not_not, ← derivative_neg] at hneg
      obtain ⟨y, hy1, hy2⟩ := (h.and (eventually_lt_of_deriv_pos hneg)).exists
      rw [eval_neg, eval_neg, hev] at hy2
      linarith
    · intro h
      exact (eventually_lt_of_deriv_pos h).mono fun y hy => by rwa [hev] at hy
  · constructor
    · intro h
      by_contra hle
      have hneg : 0 < eval x (-p) := by
        rw [eval_neg]; exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hle) hev)
      obtain ⟨y, hy1, hy2⟩ := (h.and (signRPos_of_eval_pos hneg)).exists
      rw [eval_neg] at hy2
      linarith
    · exact signRPos_of_eval_pos

lemma signRPos_mult (p q : Polynomial ℝ) (x : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) :
    signRPos x (p * q) = (signRPos x p ↔ signRPos x q) := by
  obtain ⟨s, hs, hps⟩ := exists_eventually_sign_eq x hp
  obtain ⟨t, ht, hqt⟩ := exists_eventually_sign_eq x hq
  have hpq : ∀ᶠ y in 𝓝[>] x, sign (eval y (p * q)) = s * t :=
    (hps.and hqt).mono fun y ⟨h1, h2⟩ => by rw [eval_mul, sign_mul, h1, h2]
  rw [eq_iff_iff, signRPos_iff_of_eventually hpq, signRPos_iff_of_eventually hps,
    signRPos_iff_of_eventually hqt]
  clear hps hqt hpq
  revert hs ht; revert s t; decide

lemma signRPos_mul_self (x : ℝ) {p : Polynomial ℝ} (hp : p ≠ 0) : signRPos x (p * p) := by
  obtain ⟨s, hs, hps⟩ := exists_eventually_sign_eq x hp
  exact hps.mono fun y hy => by
    rw [eval_mul]
    exact mul_self_pos.mpr (sign_ne_zero.mp (by rw [hy]; exact hs))

lemma signRPos_deriv (p : Polynomial ℝ) (x : ℝ) (hp : p ≠ 0) (hev : eval x p = 0) :
    signRPos x (derivative p * p) := by
  have deriv_ne_0 : derivative p ≠ 0 := derivative_ne_0 p x hev hp
  suffices signRPos x (derivative p) = signRPos x p by
    rw [signRPos_mult (derivative p) p x deriv_ne_0 hp]
    exact Eq.to_iff this
  rw [signRPos_rec p]
  · simp [hev]
  · exact hp

lemma signRPos_add {x : ℝ} (p q: Polynomial ℝ) (hp_eval: eval x p = 0) (hq_eval: eval x q ≠ 0) :
    (signRPos x (p + q) = signRPos x q) := by
  have hf : eval x (p + q) ≠ 0 := by rw [eval_add, hp_eval, zero_add]; exact hq_eval
  rw [signRPos_rec (p + q) x (eval_non_zero _ x hf), ite_eq_right hf,
    signRPos_rec q x (eval_non_zero q x hq_eval), ite_eq_right hq_eval, eval_add, hp_eval, zero_add]

lemma signRPos_mod {x : ℝ} (p q: Polynomial ℝ) (hp_eval: eval x p = 0) (hq_eval: eval x q ≠ 0) :
    signRPos x (q % p) = signRPos x q := by
  have h' : eval x (q % p) ≠ 0 := by rw [eval_mod q p x hp_eval]; exact hq_eval
  nth_rw 2 [←EuclideanDomain.div_add_mod q p]
  rw [signRPos_add]
  · simp only [eval_mul, mul_eq_zero]; exact Or.inl hp_eval
  · exact h'

lemma signRPos_smult (p: Polynomial ℝ) (x c: ℝ) : (c ≠ 0) → (p ≠ 0) ->
  signRPos x (Polynomial.C c * p) = if 0 < c then signRPos x p else ¬ signRPos x p := by
  intros hc hp
  have hC : signRPos x (C c) ↔ 0 < c := by
    rw [signRPos_iff_of_eventually (s := sign c) (Eventually.of_forall fun y => by rw [eval_C]),
      sign_eq_one_iff]
  rw [signRPos_mult _ _ _ (C_ne_zero.mpr hc) hp, eq_iff_iff]
  split_ifs with h
  · simp [hC, h]
  · simp [hC, h]

lemma signRPos_power (a: ℝ) (n: ℕ): signRPos a ((X - C a)^n) :=
  eventually_mem_nhdsWithin.mono fun y hy => by
    rw [eval_pow, eval_sub, eval_X, eval_C]
    exact pow_pos (sub_pos.mpr hy) n
