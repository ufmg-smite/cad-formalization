import Cad.Univariate.SturmTarski.SignRight

open Polynomial Set Filter SignType

noncomputable section

/-- The jump of the rational function `q / p` at `x`: `1` if it goes from `-∞` to `+∞`, `-1` if it
goes from `+∞` to `-∞`, and `0` otherwise (in particular when `q / p` has no pole at `x`). -/
def jumpVal (p q : ℝ[X]) (x : ℝ) : ℤ :=
  if Odd (rootMultiplicity x p - rootMultiplicity x q) then signRight x (p * q) else 0

@[simp]
lemma jump_poly_z1 (p : ℝ[X]) (x : ℝ) : jumpVal p 0 x = 0 := by simp [jumpVal]

@[simp]
lemma jump_poly_z2 (q : ℝ[X]) (x : ℝ) : jumpVal 0 q x = 0 := by simp [jumpVal]

@[simp]
lemma jump_poly_not_root {p q : ℝ[X]} {x : ℝ} (hp : eval x p ≠ 0) : jumpVal p q x = 0 := by
  simp [jumpVal, rootMultiplicity_eq_zero hp]

lemma jump_poly_mult {p q p': Polynomial ℝ} {x: ℝ} (hp': p' ≠ 0) :
                    jumpVal (p' * p) (p'* q) x = jumpVal p q x := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have h_sign : signRight x (p' * p * (p' * q)) = signRight x (p * q) := by
    rw [show p' * p * (p' * q) = (p' * p') * (p * q) by ring, signRight_mul,
      signRight_mul_self hp', one_mul]
  have h_odd : Odd (rootMultiplicity x (p' * p) - rootMultiplicity x (p' * q)) =
               Odd (rootMultiplicity x p - rootMultiplicity x q) := by
    have hp'p : p' * p ≠ 0 := mul_ne_zero hp' hp
    have hp'q : p' * q ≠ 0 := mul_ne_zero hp' hq
    simp only [rootMultiplicity_mul hp'p, rootMultiplicity_mul hp'q, eq_iff_iff]
    rw [Nat.add_sub_add_left]
  simp only [jumpVal, h_sign, h_odd]

lemma jump_poly_mod (p q: Polynomial ℝ) (x: ℝ) : jumpVal p q x = jumpVal p (q % p) x := by
  by_cases (p = 0 ∨ q = 0)
  next H => rcases H with rfl | rfl <;> simp
  next hf =>
    simp only [not_or, ← ne_eq] at hf
    let n := min (rootMultiplicity x q) (rootMultiplicity x p)
    have ⟨q', hq'⟩ : ∃q', q = (X - C x)^n * q' := by
      have  : (X - C x)^n ∣ q := by
        rw [← le_rootMultiplicity_iff hf.2]
        exact Nat.min_le_left (rootMultiplicity x q) (rootMultiplicity x p)
      exact this
    have ⟨p', hp'⟩ : ∃p', p = (X - C x)^n * p' := by
      have : (X - C x)^n ∣ p := by
        rw [← (le_rootMultiplicity_iff hf.1)]
        exact Nat.min_le_right (rootMultiplicity x q) (rootMultiplicity x p)
      exact this
    have hz' : q' ≠ 0 ∧ p' ≠ 0:= by
      rw [hq', hp'] at hf
      exact ⟨right_ne_zero_of_mul hf.2, right_ne_zero_of_mul hf.1⟩
    have hrm: rootMultiplicity x q' = 0 ∨ rootMultiplicity x p' = 0 := by
      if H: n = rootMultiplicity x q then
        have : ¬(X - C x)^1 ∣ q' := by
         simp only [pow_one]
         have hbound := rootMultiplicity_le_iff hf.2 x n
         simp only [H, Std.le_refl, true_iff] at hbound
         by_contra!
         have ⟨f, hf⟩ := exists_eq_mul_left_of_dvd this
         rw [hf, mul_comm, mul_assoc, mul_comm, ← pow_succ'] at hq'
         have hcontra : (X - C x)^(n + 1) ∣ q := by
           simp [hq']
         rw [H] at hcontra
         exact hbound hcontra
        rw [← rootMultiplicity_le_iff hz'.1 x 0] at this
        omega
      else
        have H : n = rootMultiplicity x p := by omega
        have : ¬(X - C x)^1 ∣ p' := by
          simp only [pow_one]
          have hbound := rootMultiplicity_le_iff hf.1 x n
          simp only [H, Std.le_refl, true_iff] at hbound
          by_contra!
          have ⟨f, hf⟩ := exists_eq_mul_left_of_dvd this
          rw [hf, mul_comm, mul_assoc, mul_comm, ← pow_succ'] at hp'
          have hcontra : (X - C x)^(n + 1) ∣ p := by
            simp [hp']
          rw [H] at hcontra
          exact hbound hcontra
        rw [← rootMultiplicity_le_iff hz'.2 x 0] at this
        omega
    have hcond: q' ≠ 0 ∧ Odd (rootMultiplicity x p' - rootMultiplicity x q') =
               ((q' % p' ≠ 0) ∧ Odd (rootMultiplicity x p' - rootMultiplicity x (q' % p'))) := by
        by_cases (rootMultiplicity x p' = 0)
        next htt => simp [htt, hz']
        next hff =>
          rw [←ne_eq] at hff
          rcases hrm with hok | hcontra
          · have hq_ndvd: ¬ ((X - C x)^1 ∣ q') := by
              apply (rootMultiplicity_le_iff hz'.1 x 0).mp
              linarith
            have hp_dvd : (X - C x) ∣ p' := by
              have : rootMultiplicity x p' >= 1:= by omega
              apply (le_rootMultiplicity_iff hz'.2).mp at this
              simp only [pow_one] at this; exact this
            have hq_mod_ndvd : ¬ ((X - C x)^1 ∣ q' % p') := by
              simp only [pow_one] at hq_ndvd ⊢
              simp only [EuclideanDomain.dvd_mod_iff hp_dvd]
              exact hq_ndvd
            have : rootMultiplicity x (q' % p') = 0 ∧ q' % p' ≠ 0 := by
              simp only [pow_one] at hq_mod_ndvd hq_ndvd
              have : q' % p' ≠ 0 := by
                simp only [ne_eq, EuclideanDomain.mod_eq_zero]
                by_contra!
                exact hq_ndvd (dvd_trans hp_dvd this)
              constructor
              · apply Nat.le_zero.mp; apply (rootMultiplicity_le_iff this x 0).mpr
                simp only [zero_add, pow_one]
                exact hq_mod_ndvd
              · exact this
            simp [hz', this, hok]
          · exfalso; exact hff hcontra
    have h_ult : jumpVal p' q' x = jumpVal p' (q' % p') x := by
      by_cases hodd : Odd (rootMultiplicity x p' - rootMultiplicity x q')
      · -- `p'` vanishes at `x` (otherwise the multiplicity difference is `0`), and `q'` does not
        have hB : q' % p' ≠ 0 ∧ Odd (rootMultiplicity x p' - rootMultiplicity x (q' % p')) :=
          (eq_iff_iff.mp hcond.2).mp hodd
        have hpx : eval x p' = 0 := by
          by_contra h
          rw [rootMultiplicity_eq_zero h, Nat.zero_sub, Nat.odd_iff] at hodd
          omega
        have hqx : eval x q' ≠ 0 := by
          have hq0 : rootMultiplicity x q' = 0 :=
            hrm.resolve_right (Nat.pos_iff_ne_zero.mp ((rootMultiplicity_pos hz'.2).mpr hpx))
          exact fun h => hz'.1 (rootMultiplicity_eq_zero_iff.mp hq0 h)
        simp only [jumpVal, hodd, hB.2, ite_true, signRight_mul, signRight_mod hpx hqx]
      · have hB : ¬ Odd (rootMultiplicity x p' - rootMultiplicity x (q' % p')) := by
          intro h
          rcases eq_or_ne (q' % p') 0 with h0 | h0
          · -- `p' ∣ q'`, so `x` cannot be a root of `p'` unless it is one of `q'`
            have hp0 : rootMultiplicity x p' = 0 := by
              rcases hrm with hq0 | hp0
              · by_contra hp0
                have hpx : eval x p' = 0 :=
                  (rootMultiplicity_pos hz'.2).mp (Nat.pos_of_ne_zero hp0)
                obtain ⟨k, hk⟩ := EuclideanDomain.mod_eq_zero.mp h0
                have hqx : eval x q' = 0 := by rw [hk, eval_mul, hpx, zero_mul]
                exact hz'.1 (rootMultiplicity_eq_zero_iff.mp hq0 hqx)
              · exact hp0
            simp [hp0] at h
          · exact hodd ((eq_iff_iff.mp hcond.2).mpr ⟨h0, h⟩)
        simp only [jumpVal, hodd, hB, ite_false]
    clear *- h_ult hq' hp' hf hz'
    have h_mon_z :  (X - C x) ^ n ≠ 0:= by
      exact pow_ne_zero n (X_sub_C_ne_zero x)
    rw [hp', hq']
    have h_mod : ((X - C x)^n * q') % ((X - C x)^n * p') = (X - C x)^n * (q' % p') :=
      mul_mod_mul_left q' p' ((X - C x) ^ n) h_mon_z
    simp only [jump_poly_mult h_mon_z, h_mod]
    exact h_ult

lemma jump_poly_smult_1 (p q : ℝ[X]) (c x : ℝ) :
    jumpVal p (C c * q) x = sign c * jumpVal p q x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  simp only [jumpVal, ← mul_C_eq_root_multiplicity q c x hc, mul_left_comm p (C c) q,
    signRight_C_mul]
  split_ifs <;> simp

lemma jump_poly_coprime {p q : Polynomial ℝ} {x : ℝ} (hp : eval x p = 0)
    (hpq_coprime : IsCoprime p q) :
    jumpVal p q x = jumpVal (q*p) 1 x := by
  if hpqz: (p = 0 ∨ q = 0) then
    rcases hpqz with h | h <;> simp [h]
  else
    push Not at hpqz
    have ⟨hpz, hqz⟩ := hpqz
    have hroot : eval x p ≠ 0 ∨ eval x q ≠ 0 := aeval_ne_zero_of_isCoprime hpq_coprime x
    have hq_root : eval x q ≠ 0 := hroot.resolve_left (not_not.mpr hp)
    have hq_multiplicity : rootMultiplicity x q = 0 := rootMultiplicity_eq_zero hq_root
    have h: rootMultiplicity x p - rootMultiplicity x q = rootMultiplicity x (p * q) := by
      have : p * q ≠ 0 := mul_ne_zero_iff.mpr hpqz
      have := rootMultiplicity_mul (x := x) this
      rw [hq_multiplicity] at this ⊢
      simp [this]
    have h_one : rootMultiplicity x 1 = 0 := rootMultiplicity_C 1 x
    simp only [jumpVal, h, h_one, tsub_zero, mul_one, mul_comm p q]

/-- The jump of `p * q` at a point where `p` does not vanish is the jump of `q`, signed by `p`. -/
lemma jump_poly_1_mult_left {p q : Polynomial ℝ} {x : ℝ} (hp : eval x p ≠ 0) :
    jumpVal (p * q) 1 x = sign (eval x p) * jumpVal q 1 x := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hp0 : p ≠ 0 := eval_non_zero p x hp
  have hmul : rootMultiplicity x (p * q) = rootMultiplicity x q := by
    rw [rootMultiplicity_mul (mul_ne_zero hp0 hq), rootMultiplicity_eq_zero hp, zero_add]
  have h1 : rootMultiplicity x (1 : ℝ[X]) = 0 := rootMultiplicity_eq_zero (by simp)
  simp only [jumpVal, mul_one, hmul, h1, Nat.sub_zero, signRight_mul, signRight_of_eval_ne_zero hp]
  split_ifs <;> simp

lemma jump_poly_1_mult {p q: Polynomial ℝ} {x: ℝ} (hnroot: eval x p ≠ 0 ∨ eval x q ≠ 0) :
      jumpVal (p * q) 1 x =
        sign (eval x q) * jumpVal p 1 x + sign (eval x p) * jumpVal q 1 x := by
  rcases hnroot with h | h
  · rw [jump_poly_1_mult_left h, jump_poly_not_root h, mul_zero, zero_add]
  · rw [mul_comm p q, jump_poly_1_mult_left h, jump_poly_not_root h, mul_zero, add_zero]

lemma jump_poly_sign (p q : ℝ[X]) (x : ℝ) :
    p ≠ 0 → p.eval x = 0 → jumpVal p (derivative p * q) x = sign (q.eval x) := by
  intro hp hev
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have deriv_ne_0 : derivative p ≠ 0 := derivative_ne_zero_of_isRoot hp hev
  have elim_p_order :
      rootMultiplicity x p - rootMultiplicity x (derivative p * q) = 1 - rootMultiplicity x q := by
    rw [rootMultiplicity_mul (mul_ne_zero deriv_ne_0 hq), derivative_rootMultiplicity_of_root hev]
    have : 1 ≤ rootMultiplicity x p := (rootMultiplicity_pos hp).mpr hev
    omega
  have hsign : signRight x (p * (derivative p * q)) = signRight x q := by
    rw [← mul_assoc, mul_comm p, signRight_mul, signRight_derivative_mul hp hev, one_mul]
  simp only [jumpVal, elim_p_order, hsign]
  rcases eq_or_ne (eval x q) 0 with hq0 | hq0
  · have : 1 - rootMultiplicity x q = 0 := by
      have := (rootMultiplicity_pos hq).mpr hq0; omega
    simp [this, hq0]
  · simp [rootMultiplicity_eq_zero hq0, signRight_of_eval_ne_zero hq0]
