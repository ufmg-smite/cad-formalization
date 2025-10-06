import Mathlib

open Polynomial Set Filter Classical

noncomputable section

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

