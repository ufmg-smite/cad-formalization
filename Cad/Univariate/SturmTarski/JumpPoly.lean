import Cad.Univariate.SturmTarski.SignRPos

open Polynomial Set Filter Classical SignType

noncomputable section

-- 1 if p / q goes from -inf to +inf at x, -1 if goes from +inf to -inf
-- 0 otherwise
def jump_val (p q : Polynomial ℝ) (x : ℝ) : ℤ :=
  let orderP : Nat := rootMultiplicity x p
  let orderQ : Nat := rootMultiplicity x q
  let oddOrder := Odd (orderP - orderQ)
  if p ≠ 0 ∧ q ≠ 0 ∧ oddOrder then
    -- note that p * q > 0 is the same as p / q > 0
    if sign_r_pos x (p * q) then 1 else -1
  else 0

@[simp]
lemma jump_poly_z1 (p: Polynomial ℝ) (x: ℝ) : jump_val p 0 x = 0 := by simp [jump_val]

@[simp]
lemma jump_poly_z2 (q: Polynomial ℝ) (x: ℝ) : jump_val 0 q x = 0 := by simp [jump_val]

@[simp]
lemma jump_poly_not_root {p q: Polynomial ℝ} {x: ℝ} (hp: eval x p ≠ 0) : jump_val p q x = 0 := by
  simp [jump_val, rootMultiplicity_eq_zero hp]

lemma jump_poly_mult {p q p': Polynomial ℝ} {x: ℝ} (hp': p' ≠ 0) :
                    jump_val (p' * p) (p'* q) x = jump_val p q x := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have h_sign : sign_r_pos x (p' * p * (p' * q)) = sign_r_pos x (p * q) := by
    have : p' * p * (p' * q) = (p' * p') * (p * q) := by ring
    rw [this, sign_r_pos_mult _ _ _ (mul_ne_zero hp' hp') (mul_ne_zero hp hq), eq_iff_iff]
    simp [sign_r_pos_mul_self x hp']
  have h_odd : Odd (rootMultiplicity x (p' * p) - rootMultiplicity x (p' * q)) =
               Odd (rootMultiplicity x p - rootMultiplicity x q) := by
    have hp'p : p' * p ≠ 0 := mul_ne_zero hp' hp
    have hp'q : p' * q ≠ 0 := mul_ne_zero hp' hq
    simp [rootMultiplicity_mul hp'q, rootMultiplicity_mul hp'p]
    rw [Nat.add_sub_add_left]
  simp [jump_val, h_sign, h_odd, hp', hp, hq]

lemma jump_poly_mod (p q: Polynomial ℝ) (x: ℝ) : jump_val p q x = jump_val p (q % p) x := by
  by_cases (p = 0 ∨ q = 0)
  next H => rcases H with rfl | rfl <;> simp
  next hf =>
    simp [<- ne_eq] at hf
    let n := min (rootMultiplicity x q) (rootMultiplicity x p)
    have ⟨q', hq'⟩ : ∃q', q = (X - C x)^n * q' := by
      have  : (X - C x)^n ∣ q := by
        rw [<- le_rootMultiplicity_iff hf.2]
        exact Nat.min_le_left (rootMultiplicity x q) (rootMultiplicity x p)
      exact this
    have ⟨p', hp'⟩ : ∃p', p = (X - C x)^n * p' := by
      have : (X - C x)^n ∣ p := by
        rw [<- (le_rootMultiplicity_iff hf.1)]
        exact Nat.min_le_right (rootMultiplicity x q) (rootMultiplicity x p)
      exact this
    have hz' : q' ≠ 0 ∧ p' ≠ 0:= by
      rw [hq', hp'] at hf
      exact ⟨right_ne_zero_of_mul hf.2, right_ne_zero_of_mul hf.1⟩
    have hrm: rootMultiplicity x q' = 0 ∨ rootMultiplicity x p' = 0 := by
      if H: n = rootMultiplicity x q then
        have : ¬(X - C x)^1 ∣ q' := by
         simp
         have hbound := rootMultiplicity_le_iff hf.2 x n
         simp [H] at hbound
         by_contra!
         have ⟨f, hf⟩ := exists_eq_mul_left_of_dvd this
         rw [hf, mul_comm, mul_assoc, mul_comm, <- pow_succ'] at hq'
         have hcontra : (X - C x)^(n + 1) ∣ q := by
           simp [hq']
         rw [H] at hcontra
         exact hbound hcontra
        rw [<- rootMultiplicity_le_iff hz'.1 x 0] at this
        omega
      else
        have H : n = rootMultiplicity x p := by omega
        have : ¬(X - C x)^1 ∣ p' := by
          simp
          have hbound := rootMultiplicity_le_iff hf.1 x n
          simp [H] at hbound
          by_contra!
          have ⟨f, hf⟩ := exists_eq_mul_left_of_dvd this
          rw [hf, mul_comm, mul_assoc, mul_comm, <- pow_succ'] at hp'
          have hcontra : (X - C x)^(n + 1) ∣ p := by
            simp [hp']
          rw [H] at hcontra
          exact hbound hcontra
        rw [<- rootMultiplicity_le_iff hz'.2 x 0] at this
        omega
    have hcond: q' ≠ 0 ∧ Odd (rootMultiplicity x p' - rootMultiplicity x q') =
               ((q' % p' ≠ 0) ∧ Odd (rootMultiplicity x p' - rootMultiplicity x (q' % p'))) := by
        by_cases (rootMultiplicity x p' = 0)
        next htt => simp [htt, hz']
        next hff =>
          rw [<-ne_eq] at hff
          rcases hrm with hok | hcontra
          · have hq_ndvd: ¬ ((X - C x)^1 ∣ q') := by
              apply (rootMultiplicity_le_iff hz'.1 x 0).mp
              linarith
            have hp_dvd : (X - C x) ∣ p' := by
              have : rootMultiplicity x p' >= 1:= by omega
              apply (le_rootMultiplicity_iff hz'.2).mp at this
              simp at this; exact this
            have hq_mod_ndvd : ¬ ((X - C x)^1 ∣ q' % p') := by
              simp at hq_ndvd ⊢
              simp [EuclideanDomain.dvd_mod_iff hp_dvd]; exact hq_ndvd
            have : rootMultiplicity x (q' % p') = 0 ∧ q' % p' ≠ 0 := by
              simp at hq_mod_ndvd hq_ndvd
              have : q' % p' ≠ 0 := by
                simp only [ne_eq, EuclideanDomain.mod_eq_zero]
                by_contra!
                exact hq_ndvd (dvd_trans hp_dvd this)
              constructor
              · apply Nat.le_zero.mp; apply (rootMultiplicity_le_iff this x 0).mpr
                simp
                exact hq_mod_ndvd
              · exact this
            simp [hz', this, hok]
          · exfalso; exact hff hcontra
    have h_ult : jump_val p' q' x = jump_val p' (q' % p') x := by
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
        simp only [jump_val, hz'.2, hz'.1, hodd, hB, ne_eq, not_false_eq_true, and_self, if_true]
        rw [sign_r_pos_mult _ _ _ hz'.2 hz'.1, sign_r_pos_mult _ _ _ hz'.2 hB.1,
          sign_r_pos_mod p' q' hpx hqx]
      · have hB : ¬ (q' % p' ≠ 0 ∧ Odd (rootMultiplicity x p' - rootMultiplicity x (q' % p'))) := by
          rw [← hcond.2]; exact hodd
        simp only [jump_val]
        rw [if_neg (fun h => hodd h.2.2), if_neg (fun h => hB ⟨h.2.1, h.2.2⟩)]
    clear *- h_ult hq' hp' hf hz'
    have h_mon_z :  (X - C x) ^ n ≠ 0:= by
      exact pow_ne_zero n (X_sub_C_ne_zero x)
    rw [hp', hq']
    have h_mod : ((X - C x)^n * q') % ((X - C x)^n * p') = (X - C x)^n * (q' % p') :=
      mod_mul q' p' ((X - C x) ^ n) h_mon_z
    simp [h_mod, jump_poly_mult h_mon_z]
    exact h_ult

lemma jump_poly_smult_1 (p q: Polynomial ℝ) (c x: ℝ) :
    jump_val p (Polynomial.C c * q) x = (sign c) * jump_val p q x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have hCq : C c * q ≠ 0 := mul_ne_zero (C_ne_zero.mpr hc) hq
  simp only [jump_val, ← mul_C_eq_root_multiplicity q c x hc, mul_left_comm p (C c) q,
    sign_r_pos_smult (p * q) x c hc (mul_ne_zero hp hq), hp, hq, hCq, ne_eq, not_false_eq_true,
    true_and]
  rcases lt_or_gt_of_ne hc with hc | hc
  · simp only [sign_neg hc, not_lt.mpr (le_of_lt hc), if_false, SignType.coe_neg_one]
    split_ifs <;> simp
  · simp [sign_pos hc, hc]

lemma jump_poly_coprime {p q: Polynomial ℝ} {x: ℝ} (hp: eval x p = 0) (hpq_coprime : IsCoprime p q) : jump_val p q x = jump_val (q*p) 1 x := by
  if hpqz: (p = 0 ∨ q  = 0) then
    rcases hpqz with h | h <;> simp[h]
  else
    push_neg at hpqz
    have ⟨hpz, hqz⟩ := hpqz
    have hroot : eval x p ≠ 0 ∨ eval x q ≠ 0 := aeval_ne_zero_of_isCoprime hpq_coprime x
    have hq_root : eval x q ≠ 0 := hroot.resolve_left (not_not.mpr hp)
    have hq_multiplicity : rootMultiplicity x q = 0 := rootMultiplicity_eq_zero hq_root
    have h: rootMultiplicity x p - rootMultiplicity x q = rootMultiplicity x (p * q) := by
      have : p * q ≠ 0 := mul_ne_zero_iff.mpr hpqz
      have := rootMultiplicity_mul (x := x) this
      rw [hq_multiplicity] at this ⊢
      simp [this]
    unfold jump_val
    have h_one: rootMultiplicity x 1 = 0 := rootMultiplicity_C 1 x
    simp [hqz, h_one, h]
    rw [mul_comm]

/-- The jump of `p * q` at a point where `p` does not vanish is the jump of `q`, signed by `p`. -/
lemma jump_poly_1_mult_left {p q : Polynomial ℝ} {x : ℝ} (hp : eval x p ≠ 0) :
    jump_val (p * q) 1 x = sign (eval x p) * jump_val q 1 x := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hp0 : p ≠ 0 := eval_non_zero p x hp
  have hpq : p * q ≠ 0 := mul_ne_zero hp0 hq
  have hmul : rootMultiplicity x (p * q) = rootMultiplicity x q := by
    rw [rootMultiplicity_mul hpq, rootMultiplicity_eq_zero hp, zero_add]
  have h1 : rootMultiplicity x (1 : Polynomial ℝ) = 0 := rootMultiplicity_eq_zero (by simp)
  have hsr : sign_r_pos x p ↔ 0 < eval x p := by
    rw [sign_r_pos_rec p x hp0, if_neg hp]
  simp only [jump_val, mul_one, hmul, h1, Nat.sub_zero, hpq, hq, one_ne_zero, ne_eq,
    not_false_eq_true, true_and, sign_r_pos_mult _ _ _ hp0 hq, hsr]
  rcases lt_or_gt_of_ne hp with h | h
  · simp only [sign_neg h, not_lt.mpr (le_of_lt h), false_iff, SignType.coe_neg_one]
    split_ifs <;> simp
  · simp [sign_pos h, h]

lemma jump_poly_1_mult {p q: Polynomial ℝ} {x: ℝ} (hnroot: eval x p ≠ 0 ∨ eval x q ≠ 0) :
      jump_val (p * q) 1 x  = sign (eval x q) * jump_val p 1 x + sign (eval x p) * jump_val q 1 x := by
  rcases hnroot with h | h
  · rw [jump_poly_1_mult_left h, jump_poly_not_root h, mul_zero, zero_add]
  · rw [mul_comm p q, jump_poly_1_mult_left h, jump_poly_not_root h, mul_zero, add_zero]

lemma jump_poly_sign (p q : Polynomial ℝ) (x : ℝ) :
    p ≠ 0 → p.eval x = 0 → jump_val p (derivative p * q) x = sign (q.eval x) := by
  intros hp hev
  if hq : q = 0 then
    rw [hq]
    simp
  else
    have deriv_ne_0 : derivative p ≠ 0 := derivative_ne_0 p x hev hp
    have elim_p_order : rootMultiplicity x p - rootMultiplicity x (derivative p * q) = 1 - rootMultiplicity x q := by
      rw [Polynomial.rootMultiplicity_mul]
      · rw [derivative_rootMultiplicity_of_root hev]
        have : 1 ≤ rootMultiplicity x p := by
          apply (Polynomial.le_rootMultiplicity_iff hp).mpr
          simp
          exact dvd_iff_isRoot.mpr hev
        omega
      · exact (mul_ne_zero_iff_right hq).mpr deriv_ne_0
    have elim_sign_r_pos_p : sign_r_pos x (p * (derivative p * q)) = sign_r_pos x q := by
      have : sign_r_pos x (p * (derivative p * q)) = (sign_r_pos x (derivative p * p) ↔ sign_r_pos x q) := by
        have := sign_r_pos_mult (p * derivative p) q x ((mul_ne_zero_iff_right deriv_ne_0).mpr hp) hq
        nth_rw 2 [mul_comm p (derivative p)] at this
        rw [<- mul_assoc]
        exact this
      rw [this]
      exact propext (iff_true_left (sign_r_pos_deriv p x hp hev))
    let simpleL : Int :=
      if derivative p * q ≠ 0 ∧ Odd (1 - rootMultiplicity x q) then
        (if sign_r_pos x q then 1 else -1)
      else 0
    have : jump_val p (derivative p * q) x = simpleL := by
      simp [jump_val, simpleL, hp, deriv_ne_0, hq, elim_p_order, elim_sign_r_pos_p]
    rw [this]
    by_cases eval x q = 0
    next hevQ =>
      have : 0 < rootMultiplicity x q := (rootMultiplicity_pos hq).mpr hevQ
      have : 1 - rootMultiplicity x q = 0 := by omega
      have : ¬ Odd (1 - rootMultiplicity x q) := by rw [this]; exact Nat.not_odd_zero
      have lhs : simpleL = 0 := by
        simp [simpleL, this]
      have rhs : sign (eval x q) = 0 := by rw [hevQ, sign_zero]
      rw [lhs, rhs]
      norm_cast
    next hevQ =>
      have : rootMultiplicity x q = 0 := rootMultiplicity_eq_zero hevQ
      have h1 : Odd (1 - rootMultiplicity x q) := by
        rw [this]
        exact Nat.odd_iff.mpr rfl
      have h2 : derivative p * q ≠ 0 := mul_ne_zero deriv_ne_0 hq
      have h3 : sign_r_pos x q ↔ 0 < eval x q := by
        rw [sign_r_pos_rec]
        simp [hevQ]
        exact hq
      have h4 : simpleL = if 0 < eval x q then 1 else -1 := by
        simp [simpleL, h1, h2, h3]
      rw [h4]
      rcases lt_or_gt_of_ne hevQ with h | h
      · simp [sign_neg h, not_lt.mpr (le_of_lt h)]
      · simp [sign_pos h, h]
