import Mathlib

open Polynomial Set Filter Classical

noncomputable section

def rootsInInterval (f : Polynomial ℝ) (a b : ℝ) : Finset ℝ :=
  f.roots.toFinset.filter (fun x => x ∈ Ioo a b)

def sgn (k : ℝ) : ℤ  :=
  if k > 0 then 1
  else if k = 0 then 0
  else -1

lemma next_non_root_interval (p : Polynomial Real) (lb : Real) (hp : p ≠ 0) :
    ∃ ub : Real, lb < ub ∧ (∀ z ∈ Ioc lb ub, eval z p ≠ 0) := by
  cases Classical.em (∃ r : Real, eval r p = 0 ∧ r > lb)
  next hr =>
    obtain ⟨r, hr1, hr2⟩ := hr
    let S := p.roots.toFinset.filter (fun w => w > lb)
    if hS: Finset.Nonempty S then
      obtain ⟨lr, hlr⟩ := Finset.min_of_nonempty hS
      have : lr ∈ S := Finset.mem_of_min hlr
      simp [S] at this
      have H1 : lb < lr := by linarith
      have H2 : ∀ z ∈ Ioo lb lr, eval z p ≠ 0 := by
        intros z hz
        simp at hz
        obtain ⟨hz1, hz2⟩ := hz
        intro abs
        have : z ∉ S := Finset.not_mem_of_lt_min hz2 hlr
        simp [S] at this
        have := this hp abs
        linarith
      use (lb + lr) / 2
      simp
      constructor
      · linarith
      · intros z hz1 hz2 abs
        have : z ∈ Ioo lb lr := by
          simp
          constructor
          · exact hz1
          · linarith
        have := H2 z this
        exact this abs
    else
      use lb + 1
      simp
      intros z hz1 hz2 abs
      have : z ∈ S := by simp [S, hp, abs, hz1]
      have : Finset.Nonempty S := by simp_all only [ne_eq, gt_iff_lt, Finset.not_nonempty_iff_eq_empty, Finset.not_mem_empty, S]
      exact hS this
  next hr =>
    push_neg at hr
    use lb + 1
    simp
    intros z hz1 hz2 abs
    have := hr z abs
    linarith

lemma last_non_root_interval (p : Polynomial Real) (ub : Real) (hp : p ≠ 0) :
    ∃ lb : Real, lb < ub ∧ (∀ z ∈ Ico lb ub, eval z p ≠ 0) := by
  cases Classical.em (∃ r : Real, eval r p = 0 ∧ r < ub)
  next hr =>
    obtain ⟨r, hr1, hr2⟩ := hr
    let S := p.roots.toFinset.filter (fun w => w < ub)
    if hS: Finset.Nonempty S then
      obtain ⟨mr, hmr⟩ := Finset.max_of_nonempty hS
      have : mr ∈ S := Finset.mem_of_max hmr
      simp [S] at this
      have H1 : mr < ub := by linarith
      have H2 : ∀ z ∈ Ioo mr ub, eval z p ≠ 0 := by
        intros z hz
        simp at hz
        obtain ⟨hz1, hz2⟩ := hz
        intro abs
        have : z ∉ S := Finset.not_mem_of_max_lt hz1 hmr
        simp [S] at this
        have := this hp abs
        linarith
      use (mr + ub) / 2
      simp
      constructor
      · linarith
      · intros z hz1 hz2 abs
        have : z ∈ Ioo mr ub := by
          simp
          constructor
          · linarith
          · exact hz2
        have := H2 z this
        exact this abs
    else
      use ub - 1
      simp
      intros z hz1 hz2 abs
      have : z ∈ S := by simp [S, abs, hz2, hp]
      have : Finset.Nonempty S := by simp_all only [ne_eq, Finset.not_nonempty_iff_eq_empty, Finset.not_mem_empty, S]
      exact hS this
  next hr =>
    push_neg at hr
    use ub - 1
    simp
    intros z hz1 hz2 abs
    have := hr z abs
    linarith

theorem exists_root_interval : ∀ p: Polynomial Real, ∀ (a b : ℝ), a <= b → eval a p <= 0 → 0 <= eval b p -> ∃ r: ℝ, r >= a ∧ r <= b ∧ eval r p = 0 := by
  intros p a b hab ha hb
  have p_continuous : ContinuousOn p.eval (Set.Icc a b) := p.continuousOn
  have poly_mathlib_root : ∃ r: ℝ, r >= a ∧ r <= b ∧ p.IsRoot r := by
    have intermediate_value_app := intermediate_value_Icc hab p_continuous
    have zero_in_image : 0 ∈ p.eval '' Set.Icc a b := by
      have zab : 0 ∈ Set.Icc (p.eval a) (p.eval b) := by
        simp
        aesop
      exact Set.mem_of_mem_of_subset zab intermediate_value_app
    obtain ⟨x, ⟨hxa, hxb⟩, hx_root⟩ := zero_in_image
    exact Exists.intro x ⟨hxa, hxb, hx_root⟩
  obtain ⟨r, hra, hrb, hr_root⟩ := poly_mathlib_root
  use r
  exact ⟨hra, hrb, hr_root⟩

lemma not_eq_pos_or_neg_iff_1 (p : Polynomial Real) (lb ub : Real) :
    (∀ z ∈ Ioc lb ub, eval z p ≠ 0) ↔ ((∀ z ∈ Ioc lb ub, eval z p < 0) ∨ (∀ z ∈ Ioc lb ub, 0 < eval z p)) := by
  by_contra!
  cases this
  next H =>
    obtain ⟨H₁, ⟨z₁, hz₁, hz₁'⟩, ⟨z₂, hz₂, hz₂'⟩⟩ := H
    have z1Neq0 : eval z₁ p ≠ 0 := by aesop
    have z2Neq0 : eval z₂ p ≠ 0 := by aesop
    have z1Pos : 0 < eval z₁ p := lt_of_le_of_ne hz₁' (id (Ne.symm z1Neq0))
    have z2Neg : eval z₂ p < 0 := lt_of_le_of_ne hz₂' (H₁ z₂ hz₂)
    have : z₁ ≠ z₂ := by
      intro abs
      rw [abs] at  hz₁'
      have : eval z₂ p = 0 := by linarith
      exact H₁ z₂ hz₂ this
    cases Classical.em (z₁ < z₂)
    next hle =>
      obtain ⟨r, hr₁, hr₂, hr₃⟩ := exists_root_interval (-p) z₁ z₂ (le_of_lt hle) (by simp; exact hz₁') (by simp; exact hz₂')
      simp at hr₃
      have : r ∈ Set.Ioc lb ub := by
        simp at hz₁ hz₂ ⊢
        constructor
        · linarith
        · linarith
      exact H₁ r this hr₃
    next hge =>
      push_neg at hge
      obtain ⟨r, hr₁, hr₂, hr₃⟩ := exists_root_interval p z₂ z₁ hge (le_of_lt z2Neg) (le_of_lt z1Pos)
      have : r ∈ Set.Ioc lb ub := by
        simp at hz₁ hz₂ ⊢
        constructor
        · linarith
        · linarith
      exact H₁ r this hr₃
  next H =>
    obtain ⟨⟨z, hz1, hz2⟩, H₂⟩ := H
    cases H₂
    next H₂ =>
      have := H₂ z hz1
      linarith
    next H₂ =>
      have := H₂ z hz1
      linarith

lemma derivative_ne_0 (p : Polynomial Real) (x : Real) (hev : eval x p = 0) (hp : p ≠ 0) : derivative p ≠ 0 := by
  intro abs
  have := natDegree_eq_zero_of_derivative_eq_zero abs
  obtain ⟨c, hc⟩  := (natDegree_eq_zero.mp this)
  have : c ≠ 0 := by
    intro abs2
    rw [abs2] at hc
    rw [<- hc] at hp
    simp at hp
  rw [<- hc] at hev
  simp at hev
  exact this hev

lemma exists_deriv_eq_slope_poly (a b : Real) (hab : a < b) (p : Polynomial Real) :
    ∃ c : Real, c > a ∧ c < b ∧
                eval b p - eval a p = (b - a) * eval c (derivative p) := by
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

lemma eval_mod (p q: Polynomial ℝ) (x: ℝ) (h: eval x q = 0) : eval x (p % q) = eval x p := by
 have : eval x (p % q) = eval x (p / q * q) + eval x (p % q) := by simp; exact Or.inr h
 rw [<- eval_add, EuclideanDomain.div_add_mod'] at this; exact this

lemma eval_non_zero(p: Polynomial ℝ) (x: ℝ) (h: eval x p ≠ 0) : p ≠ 0 := by aesop

lemma mul_C_eq_root_multiplicity (p: Polynomial ℝ) (c r: ℝ) (hc: ¬ c = 0):
                                        (rootMultiplicity r p = rootMultiplicity r (C c * p)) := by
  simp only [<-count_roots]
  rw [roots_C_mul]
  exact hc

theorem div_rem_zero {b c r: Polynomial ℝ} (h_rem: r.degree < b.degree) : (c * b + r)/ b = c := by
  rw [mul_comm]
  have h_b : b ≠ 0 := by exact ne_zero_of_degree_gt h_rem
  if H: r = 0 then
   simp[H, h_b];
  else
    have h_pr : ¬(b ∣ r) := by exact not_dvd_of_degree_lt H h_rem
    have h_stronger : (b * c + r)/b = c ∧ (b * c + r) % b = r := by
      by_contra!
      have h_div_mod: ((b * c + r)/b - c) * b = r - ((b * c + r)% b) := by
       ring_nf
       rw [eq_sub_iff_add_eq, add_rotate, ← eq_sub_iff_add_eq, sub_neg_eq_add]
       simp [EuclideanDomain.div_add_mod]; ring
      have : (b * c + r) / b ≠ c ∧ (b * c + r) % b ≠ r := by
        rw [<- if_false_left]
        split_ifs with H'
        · simp [H', eq_sub_iff_add_eq'] at h_div_mod
          exact this H' h_div_mod
        · intro h_contra
          simp [h_contra, h_b, sub_eq_iff_eq_add] at h_div_mod
          exact H' h_div_mod
      have h_b_dvd : ¬ (b ∣ (b * c + r)) := by
        have h_trivial : b ∣ b * c := by exact dvd_mul_right b c
        rw [dvd_add_right h_trivial]
        exact h_pr
      have h_mod_deg : degree ((b * c  + r) % b) < degree b := by
        refine degree_lt_degree ?_
        refine natDegree_mod_lt (b * c + r) ?_
        exact Nat.ne_zero_of_lt ((natDegree_lt_natDegree_iff H).mpr h_rem)
      have h_r : degree (r - (b * c + r)% b) < degree b := by
        have h_max := degree_sub_le r ((b * c + r) % b)
        exact lt_of_le_of_lt h_max (max_lt h_rem h_mod_deg)
      have h_lt_deg : degree b ≤ degree ((b * c + r) / b - c) + degree b := by
        refine le_add_of_nonneg_of_le ?_ ?_
        · exact zero_le_degree_iff.mpr (sub_ne_zero_of_ne this.1)
        · rfl
      have h_div_deg : degree ((b * c + r)/b - c) + degree b = degree (((b * c + r) / b - c) * b) := by
        exact Eq.symm degree_mul
      have h_deg_plus: degree ((b * c + r)/b - c) + degree b = degree (r - (b * c + r)%b) := by
        simp_all
      have h_final : b.degree ≤ degree (r - (b * c + r) % b) := by
        exact le_of_le_of_eq h_lt_deg h_deg_plus
      have h_contra: degree (r - (b * c + r) % b) < degree (r - (b * c + r) % b) := by
        exact gt_of_ge_of_gt h_final h_r
      exact (lt_self_iff_false (r - (b * c + r) % b).degree).mp h_contra
    exact h_stronger.1

theorem mul_cancel' {p q r: Polynomial ℝ} (hr: r ≠ 0) : (r * p) / (r * q) = p / q := by
  simp [mul_comm]
  if H: q.natDegree = 0 then
    have ⟨x, h_x⟩ := natDegree_eq_zero.mp H
    rw [<-h_x]
    rw [div_C_mul, mul_div_cancel_right₀ (hb := hr)]
    have : p/ C x = p / (C x * 1) := by rw [mul_one]
    rw [this, div_C_mul]; simp_all 
  else
    have hq : q ≠ 0 := by exact Ne.symm (ne_of_apply_ne natDegree fun a => H (id (Eq.symm a)))
    have : p = (p/q) * q + p % q := by exact Eq.symm (EuclideanDomain.div_add_mod' p q)
    rw[this]; ring_nf
    if H': p % q = 0 then
      have h_ne_z : q * r ≠ 0 := by exact (mul_ne_zero_iff_right hr).mpr hq
      simp [H']
      rw [mul_assoc, mul_div_cancel_right₀ (hb := h_ne_z), mul_div_cancel_right₀ (hb := hq)]
    else
      have h_mod_deg : natDegree (p % q) < natDegree q := by
        exact natDegree_mod_lt p H
      have h_mod_r_deg : natDegree ((p % q) * r) < natDegree (q * r) := by
        simp [natDegree_mul, H', hr, hq]
        exact h_mod_deg
      rw [div_rem_zero (degree_lt_degree h_mod_deg), mul_assoc, div_rem_zero (degree_lt_degree h_mod_r_deg)]

lemma mod_eq_sub_div {a b: Polynomial ℝ} : a % b = a - (a/b) * b := by
  have := EuclideanDomain.div_add_mod' a b
  exact eq_sub_of_add_eq' this

theorem mod_mul (p q r: Polynomial ℝ) (hr: r ≠ 0) : (r * p) % (r * q) = r * (p % q) := by
  have : (r * p) % (r * q) = r * p - ((r * p)/(r * q)) * (r * q) := by
    exact mod_eq_sub_div 
  ring_nf at this; 
  rw [mul_cancel' hr, mul_assoc, <-mul_sub, mul_comm q (p/q), <- mod_eq_sub_div (a := p) (b := q) ] at this
  exact this

lemma X_sub_C_ne_one (r : ℝ) : X - C r ≠ 1 := by
  rw [sub_eq_neg_add, add_comm, <-C_neg]
  exact X_add_C_ne_one (-r) 

